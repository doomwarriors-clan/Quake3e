/*
===========================================================================
botctl.c -- external per-frame bot control channel for the RL bot project.

Additive, optional control layer for the dedicated server. When enabled
(botctl_enable 1) it opens a Unix-domain socket that an external sidecar
process (the "brain") can use to:

  * add / remove bot client slots (driven as *human* clients, i.e. no
    SVF_BOT flag, so the game module assigns teams, runs warmup, scoring,
    scoreboard and kick exactly as it would for a person),
  * stage usercmds per client that the server thread replays each frame
    (with substep resolution: the sidecar sends N inputs per frame and the
    engine spreads them across the frame's serverTime, running P_Think once
    per substep -- exactly like a fast human client),
  * send game text commands as a client ("ready", "say hi", "team red", ...)
    through the same entry point a network text message uses,
  * read a per-frame state dump (player states + items/missiles) built on
    the server thread so it is always consistent.

Design notes (why this is safe and does not modify the game module):

  * The bot client is a normal NA_BOT netchan client. The engine already
    fully supports NA_BOT clients (this is how the stock botlib bots work):
    SV_SendClientSnapshot() builds their snapshot but returns before sending
    (no netchan to send over), and NET_SendPacket()/NET_QueuePacket() no-op
    for NA_BOT. So no network message is ever sent to a bot slot.
  * Input replay happens on the server thread, right before GAME_RUN_FRAME,
    by calling SV_ClientThink() for each staged usercmd. That is the same
    dispatch the network path uses; the game module's ClientThink() then
    runs P_Think with msec = cmd.serverTime - ps.commandTime, so feeding
    several cmds with increasing serverTime yields substep movement.
  * View angles are delta-encoded here (cmd.angles = ANGLE2SHORT(absolute)
    - ps.delta_angles), exactly as the client would. ps.delta_angles is read
    from the engine-side copy of the playerState (SV_GameClientNum), which
    is the same memory the game writes, so the encoding is exact.
  * No Python is linked in and no GPL code is pulled into the engine: the
    sidecar is a separate plain process talking a tiny binary protocol over
    a Unix socket.

Blueprint: the mechanics mirror minqlx/botctl.c (GPL-3.0, BobbyBones
project) which hooks SV_ClientThink to drive a bot's inputs from Python.
This file is a clean re-implementation for the Quake3e (1.32 layout) engine
with a socket transport instead of embedded CPython.
===========================================================================
*/

#include "server.h"

#include <pthread.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <fcntl.h>
#include <errno.h>
#include <sys/types.h>
#include <sys/socket.h>
#include <sys/un.h>
#include <poll.h>

//=============================================================================

// protocol opcodes (1 byte)
#define BOTCTL_OP_PING		0x01
#define BOTCTL_OP_ADD		0x02
#define BOTCTL_OP_REMOVE	0x03
#define BOTCTL_OP_CMD		0x04
#define BOTCTL_OP_SNAP		0x05
#define BOTCTL_OP_LIST		0x06
#define BOTCTL_OP_TEXT		0x07	// game text command as the client ("ready", "say hi", ...)

// a staged input (absolute view angles in degrees; the engine delta-encodes)
typedef struct {
	int		fwd, right, up;		// -127..127
	int		buttons;			// BUTTON_* bitmask
	int		weapon;			// 0 = none, else 1-based weapon num
	float	pitch, yaw;		// degrees
} botctl_input_t;

#define BOTCTL_MAX_QUEUE	128	// inputs the sidecar may stage per client

// per managed client
typedef struct {
	qboolean			active;
	botctl_input_t		queue[BOTCTL_MAX_QUEUE];
	int					qhead;	// next write index
	int					qcount;	// number of staged inputs
	char				name[MAX_NAME_LENGTH];
	char				team[16];
	float				last_pitch, last_yaw;	// for idle frames
	int					last_weapon;
} botctl_client_t;

// a pending request the UDS thread asked the server thread to perform
// (ADD / REMOVE / TEXT). ADD uses name+team, REMOVE uses clientNum,
// TEXT uses clientNum+text.
typedef struct {
	int		type;		// BOTCTL_OP_ADD / REMOVE / TEXT
	char		name[MAX_NAME_LENGTH];
	char		team[16];
	char		text[256];	// for TEXT
	int		clientNum;	// for REMOVE / TEXT
	// result, filled in by the server thread:
	int		result;		// ADD: client num or -1 ; REMOVE/TEXT: 1 ok / 0 fail
	qboolean	done;
} botctl_request_t;

// globals
static cvar_t		*botctl_enable;
static cvar_t		*botctl_sockpath;

static botctl_client_t	s_clients[MAX_CLIENTS];
static pthread_mutex_t	s_lock = PTHREAD_MUTEX_INITIALIZER;

static botctl_request_t	s_req;
static qboolean			s_req_valid = qfalse;

static qboolean			s_snap_requested = qfalse;
static unsigned int		s_snap_seq = 0;
static unsigned int		s_snap_len = 0;
static byte				*snap_buf = NULL;

static int				s_listen_fd = -1;
static pthread_t		s_thread;
static qboolean			s_thread_running = qfalse;
static volatile qboolean	s_shutdown = qfalse;

static char				s_sockpath[512];
static size_t			snap_buf_cap;

// forward (defined below; Botctl_Frame reacts to the enable cvar at runtime)
static void Botctl_Start( void );
static void Botctl_Stop( void );

//=============================================================================
// little-endian buffer helpers (the sidecar unpacks with struct, x86)
//=============================================================================

typedef struct {
	byte	*buf;
	int		len;
	int		cap;
} bc_writer_t;

static void bc_w_init( bc_writer_t *w, byte *buf, int cap ) {
	w->buf = buf;
	w->len = 0;
	w->cap = cap;
}

static void bc_w_put16( bc_writer_t *w, int v ) {
	if ( w->len + 2 <= w->cap ) {
		w->buf[w->len++] = (byte)(v & 255);
		w->buf[w->len++] = (byte)((v >> 8) & 255);
	}
}

static void bc_w_put32( bc_writer_t *w, int v ) {
	if ( w->len + 4 <= w->cap ) {
		w->buf[w->len++] = (byte)(v & 255);
		w->buf[w->len++] = (byte)((v >> 8) & 255);
		w->buf[w->len++] = (byte)((v >> 16) & 255);
		w->buf[w->len++] = (byte)((v >> 24) & 255);
	}
}

static void bc_w_putf( bc_writer_t *w, float f ) {
	int		v;
	union { float f; int i; } u;
	u.f = f;
	v = u.i;
	bc_w_put32( w, v );
}

static void bc_w_puts( bc_writer_t *w, const char *s, int max ) {
	while ( w->len < w->cap && max > 0 ) {
		w->buf[w->len++] = (byte)( s[0] ? s[0] : 0 );
		s++;
		max--;
	}
	// pad to a fixed width so the sidecar can read a fixed-size field
	while ( max > 0 && w->len < w->cap ) {
		w->buf[w->len++] = 0;
		max--;
	}
}

//=============================================================================
// client allocation / connect / disconnect (SERVER THREAD ONLY)
//=============================================================================

// find + zero a free slot and set it up as an NA_BOT client (no real network).
// mirrors the human connect path (Com_Memset + Netchan_Setup) so no stale data
// from a previous occupant leaks in.
static int Botctl_AllocateClient( void ) {
	int			i;
	client_t	*cl;
	netadr_t	adr;

	if ( !svs.clients ) {
		return -1;
	}
	for ( i = 0, cl = svs.clients; i < sv.maxclients; i++, cl++ ) {
		if ( cl->state == CS_FREE ) {
			break;
		}
	}
	if ( i == sv.maxclients ) {
		return -1;	// server full
	}

	Com_Memset( cl, 0, sizeof( *cl ) );

	Com_Memset( &adr, 0, sizeof( adr ) );
	adr.type = NA_BOT;
	Netchan_Setup( NS_SERVER, &cl->netchan, &adr, 0, 0, qfalse );
	cl->netchan_end_queue = &cl->netchan_start_queue;

	cl->gentity = SV_GentityNum( i );
	cl->gentity->s.number = i;
	cl->state = CS_ACTIVE;
	cl->lastPacketTime = svs.time;
	cl->snapshotMsec = 1000 / ( sv_fps->integer ? sv_fps->integer : 20 );
	cl->rate = 0;
	cl->tld[0] = '\0';
	cl->country = "BOT";

	return i;
}

// build a minimal human-like userinfo. "ip" must be present: the engine
// inserts the real address there on normal connects, and OSP's ClientConnect
// (isBot=qfalse) rejects a human connect without it ("Bad userinfo").
// NET_AdrToString() renders our NA_BOT address as "bot".
static void Botctl_MakeUserinfo( const char *name, const char *team, char *out ) {
	out[0] = '\0';
	Info_SetValueForKey( out, "name", name );
	Info_SetValueForKey( out, "ip", "bot" );
	Info_SetValueForKey( out, "rate", "25000" );
	Info_SetValueForKey( out, "snaps", "20" );
	Info_SetValueForKey( out, "model", "visor/default" );
	Info_SetValueForKey( out, "headmodel", "visor/default" );
	Info_SetValueForKey( out, "team_model", "visor/default" );
	Info_SetValueForKey( out, "team_headmodel", "visor/default" );
	Info_SetValueForKey( out, "sex", "male" );
	Info_SetValueForKey( out, "color", "4" );
	if ( team && team[0] ) {
		Info_SetValueForKey( out, "team", team );
	}
}

static int Botctl_DoAdd( const char *name, const char *team ) {
	int			slot;
	char		userinfo[MAX_INFO_STRING];
	const char	*denied;

	slot = Botctl_AllocateClient();
	if ( slot < 0 ) {
		Com_Printf( "botctl: no free client slot\n" );
		return -1;
	}

	Botctl_MakeUserinfo( name, team, userinfo );
	SV_SetUserinfo( slot, userinfo );

	// let the game connect it as a *human* (isBot = qfalse)
	denied = (const char *)GVM_ArgPtr( VM_Call( gvm, 3, GAME_CLIENT_CONNECT, slot, qtrue, qfalse ) );
	if ( denied ) {
		Com_Printf( "botctl: game rejected client: %s\n", denied );
		SV_BotFreeClient( slot );
		return -1;
	}

	// enter the world (sets up gentity, calls GAME_CLIENT_BEGIN)
	SV_ClientEnterWorld( &svs.clients[ slot ] );

	s_clients[slot].active = qtrue;
	Q_strncpyz( s_clients[slot].name, name, sizeof( s_clients[slot].name ) );
	Q_strncpyz( s_clients[slot].team, team ? team : "", sizeof( s_clients[slot].team ) );
	s_clients[slot].qhead = 0;
	s_clients[slot].qcount = 0;
	s_clients[slot].last_pitch = 0;
	s_clients[slot].last_yaw = 0;
	s_clients[slot].last_weapon = 0;

	Com_Printf( "botctl: added %s (team %s) as client %i\n", name, team ? team : "none", slot );
	return slot;
}

static int Botctl_DoRemove( int clientNum ) {
	if ( (unsigned)clientNum >= (unsigned)sv.maxclients ) {
		return 0;
	}
	if ( !s_clients[clientNum].active ) {
		return 0;
	}
	Com_Printf( "botctl: removing %s (client %i)\n", s_clients[clientNum].name, clientNum );
	s_clients[clientNum].active = qfalse;
	// standard drop path: handles NA_BOT (frees slot + game disconnect)
	SV_DropClient( &svs.clients[clientNum], "left (botctl)" );
	return 1;
}

// run a game text command as the client (same entry point a network text
// message uses; the game module then treats it exactly like a human chat /
// command line, e.g. "ready" during warmup or "say hello").
static int Botctl_DoText( int clientNum, const char *text ) {
	client_t	*cl;

	if ( (unsigned)clientNum >= (unsigned)sv.maxclients ) {
		return 0;
	}
	cl = &svs.clients[ clientNum ];
	if ( !s_clients[clientNum].active || cl->state != CS_ACTIVE ) {
		return 0;
	}
	Com_Printf( "botctl: text as %s (client %i): '%s'\n", s_clients[clientNum].name, clientNum, text );
	return SV_ExecuteClientCommand( cl, text ) ? 1 : 0;
}

//=============================================================================
// input replay (SERVER THREAD ONLY)
//=============================================================================

// encode an absolute-angle input into a usercmd, delta-encoding the view
// against the client's current ps.delta_angles (read from the engine-side
// playerState copy -- the same memory the game writes).
static usercmd_t Botctl_Encode( int clientNum, const botctl_input_t *in, int serverTime ) {
	usercmd_t		cmd;
	playerState_t	*ps;

	ps = SV_GameClientNum( clientNum );

	Com_Memset( &cmd, 0, sizeof( cmd ) );
	cmd.serverTime = serverTime;
	cmd.forwardmove = (signed char)in->fwd;
	cmd.rightmove	= (signed char)in->right;
	cmd.upmove		= (signed char)in->up;
	cmd.buttons		= in->buttons;
	cmd.weapon		= (byte)in->weapon;
	cmd.angles[PITCH] = ( ANGLE2SHORT( in->pitch ) - ps->delta_angles[PITCH] ) & 0xFFFF;
	cmd.angles[YAW]	 = ( ANGLE2SHORT( in->yaw )	 - ps->delta_angles[YAW] ) & 0xFFFF;
	cmd.angles[ROLL]	= ( 0 - ps->delta_angles[ROLL] ) & 0xFFFF;

	return cmd;
}

// drain the staged inputs for one client and replay them across the frame.
// K staged inputs are spread over [time-frameMsec, time]; if none were staged,
// one idle cmd (last known view, no buttons) is sent so P_Think still runs.
static void Botctl_RunClient( int clientNum, int time, int frameMsec ) {
	client_t	*cl;
	botctl_client_t *bc;
	botctl_input_t	inputs[BOTCTL_MAX_QUEUE];
	int			n;
	int			k;
	int			st;
	usercmd_t	cmd;
	int			ran;

	cl = &svs.clients[ clientNum ];
	bc = &s_clients[ clientNum ];

	if ( cl->state != CS_ACTIVE ) {
		return;
	}

	// pull the staged inputs out under the lock, then run them unlocked
	pthread_mutex_lock( &s_lock );
	n = bc->qcount;
	if ( n > 0 ) {
		for ( k = 0; k < n; k++ ) {
			inputs[k] = bc->queue[ ( bc->qhead - n + k + BOTCTL_MAX_QUEUE*2 ) % BOTCTL_MAX_QUEUE ];
		}
		bc->qhead = ( bc->qhead ) % BOTCTL_MAX_QUEUE;
		bc->qcount = 0;
	}
	pthread_mutex_unlock( &s_lock );

	ran = 0;
	if ( n > 0 ) {
		for ( k = 0; k < n; k++ ) {
			// spread across the frame: k=0 -> just after the previous frame,
			// k=n-1 -> exactly at the current frame time
			st = time - frameMsec + ( (int)( ( (double)( k + 1 ) / n ) * frameMsec ) );
			if ( st <= time - frameMsec ) {
				st = time - frameMsec + 1;
			}
			cmd = Botctl_Encode( clientNum, &inputs[k], st );
			SV_ClientThink( cl, &cmd );
			bc->last_pitch = inputs[k].pitch;
			bc->last_yaw = inputs[k].yaw;
			bc->last_weapon = inputs[k].weapon;
			ran = 1;
		}
	}
	if ( !ran ) {
		// no input this frame: keep the player thinking (friction/anim) with an
		// idle cmd that holds the last view and weapon
		botctl_input_t idle;
		idle.fwd = idle.right = idle.up = 0;
		idle.buttons = 0;
		idle.weapon = bc->last_weapon;
		idle.pitch = bc->last_pitch;
		idle.yaw = bc->last_yaw;
		cmd = Botctl_Encode( clientNum, &idle, time );
		SV_ClientThink( cl, &cmd );
	}
}

//=============================================================================
// state dump (built on the SERVER THREAD for consistency)
//=============================================================================

// dump one player's key state
static void Botctl_DumpPlayer( bc_writer_t *w, int clientNum ) {
	playerState_t	*ps;
	ps = SV_GameClientNum( clientNum );
	if ( !ps ) {
		return;
	}
	bc_w_put32( w, clientNum );
	bc_w_putf( w, ps->origin[0] );
	bc_w_putf( w, ps->origin[1] );
	bc_w_putf( w, ps->origin[2] );
	bc_w_put32( w, ps->stats[STAT_HEALTH] );
	bc_w_put32( w, ps->stats[STAT_ARMOR] );
	bc_w_put32( w, ps->weapon );
	bc_w_put32( w, ps->weaponstate );
	bc_w_put32( w, ps->persistant[PERS_TEAM] );
	bc_w_put32( w, ps->persistant[PERS_SCORE] );
	bc_w_putf( w, ps->viewangles[0] );
	bc_w_putf( w, ps->viewangles[1] );
	bc_w_putf( w, ps->viewangles[2] );
	bc_w_put32( w, ps->delta_angles[PITCH] );
	bc_w_put32( w, ps->delta_angles[YAW] );
	bc_w_put32( w, ps->delta_angles[ROLL] );
	bc_w_put32( w, ps->pm_type );
	{
		int			ai;
		for ( ai = 0; ai < MAX_WEAPONS; ai++ ) {
			bc_w_put32( w, ps->ammo[ ai ] );
		}
	}
}

static qboolean Botctl_InterestingEntity( int eType ) {
	switch ( eType ) {
		case ET_PLAYER:
		case ET_ITEM:
		case ET_MISSILE:
		case ET_MOVER:
			return qtrue;
		default:
			return qfalse;
	}
}

static void Botctl_DumpEntity( bc_writer_t *w, const entityState_t *es ) {
	bc_w_put32( w, es->number );
	bc_w_put32( w, es->eType );
	bc_w_put32( w, es->eFlags );
	bc_w_putf( w, es->origin[0] );
	bc_w_putf( w, es->origin[1] );
	bc_w_putf( w, es->origin[2] );
	bc_w_put32( w, es->modelindex );
	bc_w_put32( w, es->clientNum );
	bc_w_put32( w, es->weapon );
	bc_w_put32( w, es->otherEntityNum );
	bc_w_putf( w, es->pos.trDelta[0] );
	bc_w_putf( w, es->pos.trDelta[1] );
	bc_w_putf( w, es->pos.trDelta[2] );
}

static void Botctl_BuildSnapshot( void ) {
	bc_writer_t		w;
	int				i;
	int				numPlayers = 0;
	int				numEnts = 0;

	if ( !snap_buf ) {
		return;
	}

	// first pass: count, so we can size the header
	if ( svs.clients ) {
		for ( i = 0; i < sv.maxclients; i++ ) {
			if ( svs.clients[i].state == CS_ACTIVE && svs.clients[i].gentity ) {
				numPlayers++;
			}
		}
	}
	if ( svs.currFrame ) {
		for ( i = 0; i < MAX_GENTITIES; i++ ) {
			const entityState_t *es = svs.currFrame->ents[i];
			if ( es && Botctl_InterestingEntity( es->eType ) ) {
				numEnts++;
			}
		}
	}

	bc_w_init( &w, snap_buf, (int)snap_buf_cap );

	bc_w_put32( &w, svs.time );		// game/level time
	bc_w_put32( &w, sv.restartedServerId );	// changes on every map (re)start
	bc_w_put16( &w, numPlayers );
	bc_w_put16( &w, numEnts );

	for ( i = 0; i < sv.maxclients; i++ ) {
		if ( svs.clients[i].state == CS_ACTIVE && svs.clients[i].gentity ) {
			Botctl_DumpPlayer( &w, i );
		}
	}

	if ( svs.currFrame ) {
		for ( i = 0; i < MAX_GENTITIES; i++ ) {
			const entityState_t *es = svs.currFrame->ents[i];
			if ( es && Botctl_InterestingEntity( es->eType ) ) {
				Botctl_DumpEntity( &w, es );
			}
		}
	}

	// publish under the lock
	pthread_mutex_lock( &s_lock );
	s_snap_len = (unsigned int)w.len;
	s_snap_seq++;
	s_snap_requested = qfalse;
	pthread_mutex_unlock( &s_lock );
}

// is `clientNum` a client managed by an external sidecar? The map_restart
// reconnection path (SV_MapRestart_f) must reconnect such clients as regular
// players (isBot=qfalse) -- exactly like their initial connection (see
// Botctl_DoAdd) -- because the game's AI setup path (BotAISetupClient)
// rejects them when bot_enable is 0 ("BotConnectfailed").
qboolean Botctl_IsManaged( int clientNum ) {
	if ( clientNum < 0 || clientNum >= MAX_CLIENTS ) {
		return qfalse;
	}
	return s_clients[ clientNum ].active;
}

//=============================================================================
// per-frame server-thread entry point
//=============================================================================

void Botctl_Frame( int time ) {
	static qboolean	was_enabled = qfalse;
	qboolean		now_enabled;
	int			frameMsec;
	int			i;

	if ( !botctl_enable ) {
		return;
	}

	// react to the enable cvar turning on/off at runtime
	now_enabled = botctl_enable->integer != 0;
	if ( now_enabled && !was_enabled ) {
		Botctl_Start();
	} else if ( !now_enabled && was_enabled ) {
		Botctl_Stop();
	}
	was_enabled = now_enabled;

	if ( !now_enabled ) {
		return;
	}
	if ( sv.state != SS_GAME || !svs.clients ) {
		return;
	}

	frameMsec = 1000 / ( sv_fps->integer ? sv_fps->integer : 20 );

	// 0. botctl clients exchange no real packets, so nothing would ever
	// acknowledge their server->client reliable commands (tinfo once a
	// second, cs updates, join banners, ...). Unacked commands accumulate
	// in the 64-slot ring buffer and ~1 min in the engine drops the client
	// with "Server command overflow". The sidecar consumes state via the
	// UDS channel, so ACKing everything every frame is correct here.
	// lastPacketTime is refreshed the same way (sv_bot.c does it for the
	// engine's own bots in SV_BotGetConsoleMessage) or sv_timeout (200 s
	// default) would drop the client too.
	for ( i = 0; i < sv.maxclients; i++ ) {
		if ( s_clients[i].active && svs.clients[i].state >= CS_PRIMED ) {
			svs.clients[i].reliableAcknowledge = svs.clients[i].reliableSequence;
			svs.clients[i].lastPacketTime = svs.time;
		}
	}

	// 1. service a pending add/remove/text request from the sidecar
	pthread_mutex_lock( &s_lock );
	if ( s_req_valid && !s_req.done ) {
		botctl_request_t req = s_req;
		int			res;
		pthread_mutex_unlock( &s_lock );

		if ( req.type == BOTCTL_OP_ADD ) {
			res = Botctl_DoAdd( req.name, req.team );
		} else if ( req.type == BOTCTL_OP_TEXT ) {
			res = Botctl_DoText( req.clientNum, req.text );
		} else {
			res = Botctl_DoRemove( req.clientNum );
		}

		pthread_mutex_lock( &s_lock );
		s_req.result = res;
		s_req.done = qtrue;
		s_req_valid = qfalse;
		pthread_mutex_unlock( &s_lock );
	} else {
		pthread_mutex_unlock( &s_lock );
	}

	// 2. replay staged inputs for every managed client (before the game frame)
	for ( i = 0; i < sv.maxclients; i++ ) {
		if ( s_clients[i].active && svs.clients[i].state == CS_ACTIVE ) {
			Botctl_RunClient( i, time, frameMsec );
		}
	}

}

// called from SV_RunFrame AFTER GAME_RUN_FRAME, so a requested state dump
// reflects the ps of the frame that just ran (not the previous one)
void Botctl_Snapshot( int time ) {
	if ( !botctl_enable ) {
		return;
	}
	if ( botctl_enable->integer == 0 ) {
		return;
	}
	if ( sv.state != SS_GAME || !svs.clients ) {
		return;
	}

	pthread_mutex_lock( &s_lock );
	if ( s_snap_requested ) {
		pthread_mutex_unlock( &s_lock );
		Botctl_BuildSnapshot();
	} else {
		pthread_mutex_unlock( &s_lock );
	}
}

//=============================================================================
// UDS transport helpers
//=============================================================================

static int bc_sendall( int fd, const void *buf, int len ) {
	const byte	*p = (const byte *)buf;
	int			sent = 0;
	while ( sent < len ) {
		int		n = (int)send( fd, p + sent, len - sent, 0 );
		if ( n <= 0 ) {
			if ( n < 0 && errno == EINTR ) {
				continue;
			}
			return -1;
		}
		sent += n;
	}
	return sent;
}

static int bc_recvall( int fd, void *buf, int len ) {
	byte	*p = (byte *)buf;
	int		got = 0;
	while ( got < len ) {
		int		n = (int)recv( fd, p + got, len - got, 0 );
		if ( n <= 0 ) {
			if ( n < 0 && errno == EINTR ) {
				continue;
			}
			return -1;
		}
		got += n;
	}
	return got;
}

// read one framed message: [u32 total_len][u8 op][payload...]
// returns the opcode, or -1 on disconnect/error. payload is copied into
// out (up to outcap), *outlen set.
static int bc_read_msg( int fd, byte *out, int outcap, int *outlen ) {
	uint32_t		total;
	int				op;
	int				payload;
	struct pollfd	pfd;
	int				pr;

	pfd.fd = fd;
	pfd.events = POLLIN;
	pr = poll( &pfd, 1, 50 );
	if ( pr < 0 ) {
		if ( errno == EINTR ) {
			return -2;	// retry
		}
		return -1;
	}
	if ( pr == 0 ) {
		return -2;	// timeout, retry (lets us notice s_shutdown)
	}
	if ( pfd.revents & ( POLLERR | POLLHUP | POLLNVAL ) ) {
		return -1;
	}
	if ( bc_recvall( fd, &total, 4 ) < 0 ) {
		return -1;
	}
	if ( total < 1 || total > (1u << 20) ) {
		return -1;	// malformed
	}
	if ( bc_recvall( fd, &op, 1 ) < 0 ) {
		return -1;
	}
	payload = (int)total - 1;
	if ( payload < 0 ) {
		return -1;
	}
	*outlen = 0;
	if ( payload > 0 ) {
		if ( payload <= outcap ) {
			if ( bc_recvall( fd, out, payload ) < 0 ) {
				return -1;
			}
			*outlen = payload;
		} else {
			// drain and drop an oversized payload
			byte	 scratch[256];
			int			left = payload;
			while ( left > 0 ) {
				int		chunk = left < 256 ? left : 256;
				if ( bc_recvall( fd, scratch, chunk ) < 0 ) {
					return -1;
				}
				left -= chunk;
			}
		}
	}
	return op;
}

// send one framed message
static int bc_send_msg( int fd, int op, const void *payload, int payloadlen ) {
	byte			header[5];
	uint32_t		total = 1u + (uint32_t)payloadlen;
	header[0] = (byte)(total & 255);
	header[1] = (byte)((total >> 8) & 255);
	header[2] = (byte)((total >> 16) & 255);
	header[3] = (byte)((total >> 24) & 255);
	header[4] = (byte)op;
	if ( bc_sendall( fd, header, 5 ) < 0 ) {
		return -1;
	}
	if ( payloadlen > 0 && bc_sendall( fd, payload, payloadlen ) < 0 ) {
		return -1;
	}
	return 0;
}

static void bc_sleep_ms( int ms ) {
	struct timespec ts;
	ts.tv_sec = ms / 1000;
	ts.tv_nsec = ( long )( ( ms % 1000 ) * 1000000L );
	nanosleep( &ts, NULL );
}

//=============================================================================
// request/response between the UDS thread and the server thread
//=============================================================================

// submit a request (add/remove/text) and wait (bounded) for the server
// thread's result. returns the result (client num for add, 1/0 otherwise)
// or -1 on timeout.
static int Botctl_SubmitRequest( int type, const char *name, const char *team, int clientNum, const char *text ) {
	int				timeout = 0;

	pthread_mutex_lock( &s_lock );
	if ( s_req_valid ) {
		// a request is already in flight; the sidecar is single-shot so this
		// should not happen, but be safe and drop
		pthread_mutex_unlock( &s_lock );
		return -1;
	}
	s_req.type = type;
	if ( name ) {
		Q_strncpyz( s_req.name, name, sizeof( s_req.name ) );
	} else {
		s_req.name[0] = '\0';
	}
	if ( team ) {
		Q_strncpyz( s_req.team, team, sizeof( s_req.team ) );
	} else {
		s_req.team[0] = '\0';
	}
	if ( text ) {
		Q_strncpyz( s_req.text, text, sizeof( s_req.text ) );
	} else {
		s_req.text[0] = '\0';
	}
	s_req.clientNum = clientNum;
	s_req.result = -1;
	s_req.done = qfalse;
	s_req_valid = qtrue;
	pthread_mutex_unlock( &s_lock );

	while ( !s_shutdown ) {
		int		res;
		qboolean	done;
		pthread_mutex_lock( &s_lock );
		done = s_req.done;
		res = s_req.result;
		pthread_mutex_unlock( &s_lock );
		if ( done ) {
			return res;
		}
		bc_sleep_ms( 2 );
		if ( ++timeout > 1000 ) {	// ~2 s
			return -1;
		}
	}
	return -1;
}

// ask for a state dump and wait (bounded) for the server thread to build it.
// returns 1 on success (data in snap_buf), 0 on timeout.
static int Botctl_WaitSnapshot( unsigned int *outlen ) {
	unsigned int	seen;
	int				timeout = 0;

	pthread_mutex_lock( &s_lock );
	seen = s_snap_seq;
	s_snap_requested = qtrue;
	pthread_mutex_unlock( &s_lock );

	while ( !s_shutdown ) {
		pthread_mutex_lock( &s_lock );
		if ( s_snap_seq != seen ) {
			*outlen = s_snap_len;
			pthread_mutex_unlock( &s_lock );
			return 1;
		}
		pthread_mutex_unlock( &s_lock );
		bc_sleep_ms( 2 );
		if ( ++timeout > 1000 ) {
			return 0;
		}
	}
	return 0;
}

//=============================================================================
// connection handler (runs on the UDS thread)
//=============================================================================

static void Botctl_HandleConnection( int fd ) {
	byte		payload[512];	// largest request: TEXT (4 + 255) with margin
	int			plen;
	byte		*snap_out = NULL;	// heap copy of the last snapshot (send unlocked)
	size_t		snap_cap = 0;

	Com_Printf( "botctl: sidecar connected\n" );

	while ( !s_shutdown ) {
		int		op;
		op = bc_read_msg( fd, payload, (int)sizeof( payload ), &plen );
		if ( op == -1 ) {
			break;	// disconnect
		}
		if ( op == -2 ) {
			continue;	// timeout
		}

		switch ( op ) {
		case BOTCTL_OP_PING: {
			const char *pong = "PONG";
			bc_send_msg( fd, BOTCTL_OP_PING, pong, 4 );
			break;
		}

		case BOTCTL_OP_ADD: {
			// payload: char name[32] char team[16] int32 substeps
			// (substeps is accepted for sidecar compat but ignored: the engine
			// spreads whatever inputs the sidecar stages across the frame)
			char		name[MAX_NAME_LENGTH];
			char		team[16];
			int			res;
			if ( plen < 32 + 16 + 4 ) {
				break;
			}
			memset( name, 0, sizeof( name ) );
			memset( team, 0, sizeof( team ) );
			memcpy( name, payload, 32 );
			memcpy( team, payload + 32, 16 );
			res = Botctl_SubmitRequest( BOTCTL_OP_ADD, name, team, 0, NULL );
			{
				int32_t	out = (int32_t)res;
				bc_send_msg( fd, BOTCTL_OP_ADD, &out, 4 );
			}
			break;
		}

		case BOTCTL_OP_REMOVE: {
			int32_t	clientNum = 0;
			int			res;
			if ( plen < 4 ) {
				break;
			}
			memcpy( &clientNum, payload, 4 );
			res = Botctl_SubmitRequest( BOTCTL_OP_REMOVE, NULL, NULL, (int)clientNum, NULL );
			{
				int32_t	out = (int32_t)res;
				bc_send_msg( fd, BOTCTL_OP_REMOVE, &out, 4 );
			}
			break;
		}

		case BOTCTL_OP_TEXT: {
			// payload: int32 clientNum, then the command text (NUL-stripped)
			int32_t	clientNum;
			char		text[256];
			int			tlen;
			int			res;
			if ( plen < 4 ) {
				break;
			}
			memcpy( &clientNum, payload, 4 );
			tlen = plen - 4;
			if ( tlen >= (int)sizeof( text ) ) {
				tlen = (int)sizeof( text ) - 1;
			}
			memset( text, 0, sizeof( text ) );
			memcpy( text, payload + 4, tlen );
			res = Botctl_SubmitRequest( BOTCTL_OP_TEXT, NULL, NULL, (int)clientNum, text );
			{
				int32_t	out = (int32_t)res;
				bc_send_msg( fd, BOTCTL_OP_TEXT, &out, 4 );
			}
			break;
		}

		case BOTCTL_OP_CMD: {
			// payload: int32 clientNum, int16 fwd, int16 right, int16 up,
			//          int32 buttons, int32 weapon, float32 pitch, float32 yaw
			int32_t	clientNum;
			int16_t	fwd, right, up;
			int32_t	buttons, weapon;
			float		pitch, yaw;
			if ( plen < 4 + 2 + 2 + 2 + 4 + 4 + 4 + 4 ) {
				break;
			}
			memcpy( &clientNum, payload + 0, 4 );
			memcpy( &fwd, payload + 4, 2 );
			memcpy( &right, payload + 6, 2 );
			memcpy( &up, payload + 8, 2 );
			memcpy( &buttons, payload + 10, 4 );
			memcpy( &weapon, payload + 14, 4 );
			memcpy( &pitch, payload + 18, 4 );
			memcpy( &yaw, payload + 22, 4 );

			if ( (unsigned)clientNum < (unsigned)MAX_CLIENTS ) {
				botctl_client_t	*bc = &s_clients[ clientNum ];
				pthread_mutex_lock( &s_lock );
				if ( bc->active && bc->qcount < BOTCTL_MAX_QUEUE ) {
					bc->queue[ bc->qhead ] .fwd = fwd;
					bc->queue[ bc->qhead ] .right = right;
					bc->queue[ bc->qhead ] .up = up;
					bc->queue[ bc->qhead ] .buttons = buttons;
					bc->queue[ bc->qhead ] .weapon = weapon;
					bc->queue[ bc->qhead ] .pitch = pitch;
					bc->queue[ bc->qhead ] .yaw = yaw;
					bc->qhead = ( bc->qhead + 1 ) % BOTCTL_MAX_QUEUE;
					bc->qcount++;
				}
				pthread_mutex_unlock( &s_lock );
			}
			break;
		}

		case BOTCTL_OP_SNAP: {
			unsigned int	outlen = 0;
			if ( Botctl_WaitSnapshot( &outlen ) ) {
				// copy the dump out under the lock, then send it WITHOUT the
				// lock: a slow/stalled send() must never hold s_lock, because
				// the server thread takes it every frame
				if ( outlen > snap_cap ) {
					byte	*nb = (byte *)realloc( snap_out, outlen );
					if ( !nb ) {
						bc_send_msg( fd, BOTCTL_OP_SNAP, NULL, 0 );
						break;
					}
					snap_out = nb;
					snap_cap = outlen;
				}
				pthread_mutex_lock( &s_lock );
				memcpy( snap_out, snap_buf, outlen );
				pthread_mutex_unlock( &s_lock );
				bc_send_msg( fd, BOTCTL_OP_SNAP, snap_out, (int)outlen );
			} else {
				// send an empty snap so the sidecar doesn't block
				bc_send_msg( fd, BOTCTL_OP_SNAP, NULL, 0 );
			}
			break;
		}

		case BOTCTL_OP_LIST: {
			bc_writer_t	w;
			byte			tmp[4096];
			int				count = 0;
			int				i;
			for ( i = 0; i < MAX_CLIENTS; i++ ) {
				if ( s_clients[i].active ) {
					count++;
				}
			}
			bc_w_init( &w, tmp, (int)sizeof( tmp ) );
			bc_w_put16( &w, count );
			for ( i = 0; i < MAX_CLIENTS; i++ ) {
				if ( s_clients[i].active ) {
					bc_w_put32( &w, i );
					bc_w_puts( &w, s_clients[i].name, MAX_NAME_LENGTH );
					bc_w_puts( &w, s_clients[i].team, 16 );
				}
			}
			bc_send_msg( fd, BOTCTL_OP_LIST, tmp, w.len );
			break;
		}

		default:
			break;
		}
	}

	free( snap_out );
	Com_Printf( "botctl: sidecar disconnected\n" );
	close( fd );
}

//=============================================================================
// UDS listener thread
//=============================================================================

static void *Botctl_ListenerThread( void *arg ) {
	struct sockaddr_un	addr;
	int				conn;

	(void)arg;

	// create + bind + listen
	s_listen_fd = socket( AF_UNIX, SOCK_STREAM, 0 );
	if ( s_listen_fd < 0 ) {
		Com_Printf( "botctl: socket() failed: %s\n", strerror( errno ) );
		return NULL;
	}

	if ( strlen( s_sockpath ) >= sizeof( addr.sun_path ) ) {
		Com_Printf( "botctl: socket path too long (%i bytes, max %i): %s\n",
			(int)strlen( s_sockpath ), (int)sizeof( addr.sun_path ) - 1, s_sockpath );
		close( s_listen_fd );
		s_listen_fd = -1;
		return NULL;
	}
	memset( &addr, 0, sizeof( addr ) );
	addr.sun_family = AF_UNIX;
	Q_strncpyz( addr.sun_path, s_sockpath, sizeof( addr.sun_path ) );
	// remove a stale socket file from a previous run
	unlink( s_sockpath );
	if ( bind( s_listen_fd, (struct sockaddr *)&addr, sizeof( addr ) ) < 0 ) {
		Com_Printf( "botctl: bind(%s) failed: %s\n", s_sockpath, strerror( errno ) );
		close( s_listen_fd );
		s_listen_fd = -1;
		return NULL;
	}
	if ( listen( s_listen_fd, 2 ) < 0 ) {
		Com_Printf( "botctl: listen() failed: %s\n", strerror( errno ) );
		close( s_listen_fd );
		s_listen_fd = -1;
		unlink( s_sockpath );
		return NULL;
	}

	Com_Printf( "botctl: listening on %s\n", s_sockpath );

	while ( !s_shutdown ) {
		struct pollfd	pfd;
		int				pr;
		pfd.fd = s_listen_fd;
		pfd.events = POLLIN;
		pr = poll( &pfd, 1, 50 );
		if ( pr < 0 ) {
			if ( errno == EINTR ) {
				continue;
			}
			break;
		}
		if ( pr == 0 ) {
			continue;
		}
		conn = accept( s_listen_fd, NULL, NULL );
		if ( conn < 0 ) {
			if ( errno == EINTR ) {
				continue;
			}
			if ( s_shutdown ) {
				break;
			}
			continue;
		}
		Botctl_HandleConnection( conn );
	}

	return NULL;
}

//=============================================================================
// start / stop
//=============================================================================

static void Botctl_DeriveSockpath( void ) {
	int			port;

	if ( botctl_sockpath && botctl_sockpath->string[0] ) {
		Q_strncpyz( s_sockpath, botctl_sockpath->string, sizeof( s_sockpath ) );
		return;
	}
	port = Cvar_VariableIntegerValue( "net_port" );
	if ( port <= 0 ) {
		port = 27960;
	}
	snprintf( s_sockpath, sizeof( s_sockpath ), "/tmp/q3e-botctl-%i.sock", port );
}

static void Botctl_Start( void ) {
	if ( s_thread_running ) {
		return;
	}
	if ( !snap_buf ) {
		snap_buf_cap = 512 * 1024;
		snap_buf = (byte *)malloc( snap_buf_cap );
		if ( !snap_buf ) {
			Com_Printf( "botctl: out of memory for snapshot buffer\n" );
			return;
		}
	}
	s_shutdown = qfalse;
	Botctl_DeriveSockpath();
	if ( pthread_create( &s_thread, NULL, Botctl_ListenerThread, NULL ) != 0 ) {
		Com_Printf( "botctl: pthread_create failed\n" );
		return;
	}
	s_thread_running = qtrue;
	Com_Printf( "botctl: started (socket %s)\n", s_sockpath );
}

static void Botctl_Stop( void ) {
	if ( !s_thread_running ) {
		return;
	}
	s_shutdown = qtrue;
	// join blocks until the thread exits; its poll/recv timeouts are ~50ms so
	// it notices s_shutdown quickly (its wait loops also check it every ~2ms)
	pthread_join( s_thread, NULL );
	s_thread_running = qfalse;
	if ( s_listen_fd >= 0 ) {
		close( s_listen_fd );
		s_listen_fd = -1;
	}
	if ( s_sockpath[0] ) {
		unlink( s_sockpath );
	}
	Com_Printf( "botctl: stopped\n" );
}

void Botctl_Shutdown( void ) {
	Botctl_Stop();
	if ( snap_buf ) {
		free( snap_buf );
		snap_buf = NULL;
		snap_buf_cap = 0;
	}
}

//=============================================================================
// cvar + init
//=============================================================================

void Botctl_Init( void ) {
	// Botctl_Frame (called every server frame) reacts to botctl_enable turning
	// on/off, so no cvar think callback is needed (Cvar_Get has none here).
	botctl_enable = Cvar_Get( "botctl_enable", "0", 0 );
	botctl_sockpath = Cvar_Get( "botctl_sockpath", "", CVAR_LATCH );
}
