/*
===========================================================================
Copyright (C) 1999-2005 Id Software, Inc.

This file is part of Quake III Arena source code.

Quake III Arena source code is free software; you can redistribute it
and/or modify it under the terms of the GNU General Public License as
published by the Free Software Foundation; either version 2 of the License,
or (at your option) any later version.

Quake III Arena source code is distributed in the hope that it will be
useful, but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with Quake III Arena source code; if not, write to the Free Software
Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA  02110-1301  USA
===========================================================================
*/

/*
===========================================================================
botctl.c -- external per-frame bot control channel for the RL bot project.

Build gating: this file is compiled and linked only for dedicated builds
when the Makefile is configured with USE_BOTCTL=1 (the Makefile gates
$(B)/ded/botctl.o, -lpthread and -DUSE_BOTCTL on that variable; server.h
turns every Botctl_* hook into a no-op in all other configurations, so
client / listen-server binaries never contain this code).

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

Note on the ADD "team" field: it is stored for LIST output and written to
the client's userinfo ("team"), but team assignment itself is done by the
game module when the client joins -- exactly as for humans. The sidecar
should pick a team with a TEXT command ("team red"), like a player does.

Note on the snapshot header "time": it is sv.time (level time), the same
clock GAME_RUN_FRAME / usercmd serverTime use. "restart_id"
(sv.restartedServerId) changes on every map (re)start, so the sidecar can
detect level transitions.

Note on the UDS listener thread: it never touches Com_Printf or the game
directly; log messages are queued and printed by Botctl_Frame on the
server thread, requests are executed there, and every socket operation
has a timeout so thread shutdown is bounded.

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

#if !defined(USE_BOTCTL) || !defined(DEDICATED)
#error botctl.c is compiled only for dedicated builds with USE_BOTCTL=1 (see Makefile + server.h)
#endif

#include <pthread.h>
#include <stdarg.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <fcntl.h>
#include <errno.h>
#include <sys/stat.h>
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
	unsigned int	seq;	// request generation (see Botctl_SubmitRequest)
	// result, filled in by the server thread:
	int		result;		// ADD: client num or -1 ; REMOVE/TEXT: 1 ok / 0 fail
	qboolean	done;
} botctl_request_t;

// globals
static cvar_t		*botctl_enable;
static cvar_t		*botctl_sockpath;

static botctl_client_t	s_clients[MAX_CLIENTS];
static pthread_mutex_t	s_lock = PTHREAD_MUTEX_INITIALIZER;

// channel state, driven by Botctl_Frame (server thread). s_enabled is a
// file-scope flag on purpose: Botctl_Shutdown resets it, so after a full
// server restart (SV_Restart -> SV_Shutdown + SV_Init) the enable cvar is
// seen as a fresh on-edge and the socket comes back up.
static qboolean			s_enabled = qfalse;
static volatile qboolean	s_sidecar_lost = qfalse;	// connection handler died

static botctl_request_t	s_req;
static qboolean			s_req_valid = qfalse;
static unsigned int		s_req_seq = 0;

// log lines queued by the UDS thread, printed by Botctl_Frame (Com_Printf
// is only safe on the server thread)
#define BOTCTL_LOG_LINES	16
static char				s_logq[BOTCTL_LOG_LINES][192];
static int				s_logq_head;	// next write slot
static int				s_logq_count;

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
// thread-safe log queue (UDS thread -> server thread)
//=============================================================================

// push one line; caller must hold s_lock
static void Botctl_LogPushLocked( const char *fmt, ... ) {
	char		line[192];
	va_list		argptr;

	if ( s_logq_count >= BOTCTL_LOG_LINES ) {
		return;	// drop, the queue is not a stream
	}
	va_start( argptr, fmt );
	Q_vsnprintf( line, sizeof( line ), fmt, argptr );
	va_end( argptr );

	Q_strncpyz( s_logq[s_logq_head], line, sizeof( s_logq[0] ) );
	s_logq_head = ( s_logq_head + 1 ) % BOTCTL_LOG_LINES;
	s_logq_count++;
}

// convenience wrapper for callers that do not hold s_lock
static void Botctl_LogQ( const char *fmt, ... ) {
	char		line[192];
	va_list		argptr;

	va_start( argptr, fmt );
	Q_vsnprintf( line, sizeof( line ), fmt, argptr );
	va_end( argptr );

	pthread_mutex_lock( &s_lock );
	Botctl_LogPushLocked( "%s", line );
	pthread_mutex_unlock( &s_lock );
}

// print everything the UDS thread queued (called from Botctl_Frame)
static void Botctl_DrainLog( void ) {
	for (;;) {
		char		line[192];

		pthread_mutex_lock( &s_lock );
		if ( s_logq_count <= 0 ) {
			pthread_mutex_unlock( &s_lock );
			return;
		}
		Q_strncpyz( line, s_logq[( s_logq_head - s_logq_count + BOTCTL_LOG_LINES ) % BOTCTL_LOG_LINES], sizeof( line ) );
		s_logq_count--;
		pthread_mutex_unlock( &s_lock );

		Com_Printf( "%s\n", line );
	}
}

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

// names and team tags end up in userinfo strings, so reject everything the
// userinfo parser uses as syntax (backslash separator, quote, semicolon)
// and any non-printable byte
static qboolean Botctl_ValidText( const char *s ) {
	for ( ; *s; s++ ) {
		if ( (byte)*s < 32 || (byte)*s >= 127 ) {
			return qfalse;
		}
		if ( *s == '\\' || *s == '"' || *s == ';' ) {
			return qfalse;
		}
	}
	return qtrue;
}

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

	if ( !name || !name[0] || !Botctl_ValidText( name ) ) {
		Com_Printf( "botctl: ADD rejected: empty or invalid name\n" );
		return -1;
	}
	if ( team && team[0] && !Botctl_ValidText( team ) ) {
		Com_Printf( "botctl: ADD rejected: invalid team tag\n" );
		return -1;
	}

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

	if ( svs.clients[slot].state != CS_ACTIVE ) {
		// the game dropped the client during ClientBegin: slot is free again
		return -1;
	}

	pthread_mutex_lock( &s_lock );
	s_clients[slot].active = qtrue;
	Q_strncpyz( s_clients[slot].name, name, sizeof( s_clients[slot].name ) );
	Q_strncpyz( s_clients[slot].team, team ? team : "", sizeof( s_clients[slot].team ) );
	s_clients[slot].qhead = 0;
	s_clients[slot].qcount = 0;
	s_clients[slot].last_pitch = 0;
	s_clients[slot].last_yaw = 0;
	s_clients[slot].last_weapon = 0;
	pthread_mutex_unlock( &s_lock );

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
	pthread_mutex_lock( &s_lock );
	s_clients[clientNum].active = qfalse;
	s_clients[clientNum].qhead = 0;
	s_clients[clientNum].qcount = 0;
	pthread_mutex_unlock( &s_lock );
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
	if ( !Botctl_ValidText( text ) ) {
		Com_Printf( "botctl: TEXT rejected: invalid characters\n" );
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
	int			fwd, right, up, weapon;

	ps = SV_GameClientNum( clientNum );

	// clamp to the usercmd_t field ranges (the wire format carries int32)
	fwd    = in->fwd;
	right  = in->right;
	up     = in->up;
	weapon = in->weapon;
	if ( fwd > 127 )	{ fwd = 127; }	else if ( fwd < -127 )	{ fwd = -127; }
	if ( right > 127 )	{ right = 127; }	else if ( right < -127 )	{ right = -127; }
	if ( up > 127 )		{ up = 127; }		else if ( up < -127 )		{ up = -127; }
	if ( weapon < 0 || weapon >= MAX_WEAPONS ) {
		weapon = 0;	// 0 = no weapon request
	}

	Com_Memset( &cmd, 0, sizeof( cmd ) );
	cmd.serverTime = serverTime;
	cmd.forwardmove = (signed char)fwd;
	cmd.rightmove	= (signed char)right;
	cmd.upmove		= (signed char)up;
	cmd.buttons		= in->buttons;	// the game interprets the BUTTON_* bits
	cmd.weapon		= (byte)weapon;
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

// Walk the live world the same way SV_BuildCommonSnapshot does
// (sv_snapshot.c): sv.num_entities entries in sv.gentities, r.linked and
// !SVF_NOCLIENT decide what a client sees, ent->s is the state the game
// module updated in the frame that just ran. svs.currFrame is rebuilt only
// later in SV_Frame (SV_IssueNewSnapshot), so its contents trail the
// player states dumped here, and beyond currFrame->count its slots still
// hold pointers to entities from older snapshots (ghost/duplicate items
// and missiles).
static void Botctl_BuildSnapshot( int time ) {
	bc_writer_t		w;
	sharedEntity_t	*ent;
	int				i;
	int				num;
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
	if ( sv.state != SS_DEAD ) {
		for ( num = 0; num < sv.num_entities; num++ ) {
			ent = SV_GentityNum( num );
			if ( !ent->r.linked ) {
				continue;
			}
			if ( ent->r.svFlags & SVF_NOCLIENT ) {
				continue;
			}
			if ( Botctl_InterestingEntity( ent->s.eType ) ) {
				numEnts++;
			}
		}
	}

	bc_w_init( &w, snap_buf, (int)snap_buf_cap );

	bc_w_put32( &w, time );		// sv.time: level time, the usercmd serverTime clock
	bc_w_put32( &w, sv.restartedServerId );	// changes on every map (re)start
	bc_w_put16( &w, numPlayers );
	bc_w_put16( &w, numEnts );

	for ( i = 0; i < sv.maxclients; i++ ) {
		if ( svs.clients[i].state == CS_ACTIVE && svs.clients[i].gentity ) {
			Botctl_DumpPlayer( &w, i );
		}
	}

	if ( sv.state != SS_DEAD ) {
		for ( num = 0; num < sv.num_entities; num++ ) {
			ent = SV_GentityNum( num );
			if ( !ent->r.linked ) {
				continue;
			}
			if ( ent->r.svFlags & SVF_NOCLIENT ) {
				continue;
			}
			if ( Botctl_InterestingEntity( ent->s.eType ) ) {
				Botctl_DumpEntity( &w, &ent->s );
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

// is `clientNum` a client managed by an external sidecar? The reconnection
// paths (SV_MapRestart_f, SV_SpawnServer) must reconnect such clients as
// regular players (isBot=qfalse) -- exactly like their initial connection
// (Botctl_DoAdd passes isBot=qfalse) -- because the game's AI setup path
// (BotAISetupClient) rejects them when bot_enable is 0 ("BotConnectfailed")
// and would need a botlib skill/character assignment otherwise.
qboolean Botctl_IsManaged( int clientNum ) {
	if ( clientNum < 0 || clientNum >= MAX_CLIENTS ) {
		return qfalse;
	}
	return s_clients[ clientNum ].active;
}

// A managed slot went away through an engine path we do not control
// (admin clientkick, sv_timeout drop, botlib cleanup, ...): forget the
// management state so the next occupant of the slot -- a human or an
// addbot bot -- is not mistaken for a botctl client (a phantom managed
// flag would ACK all its reliable commands and feed it a second usercmd
// stream). Called from SV_DropClient and SV_BotFreeClient (server thread).
void Botctl_ClientDropped( int clientNum ) {
	if ( clientNum < 0 || clientNum >= MAX_CLIENTS ) {
		return;
	}
	pthread_mutex_lock( &s_lock );
	if ( s_clients[clientNum].active ) {
		Botctl_LogPushLocked( "botctl: client %i (%s) left through the engine, management cleared",
			clientNum, s_clients[clientNum].name );
		s_clients[clientNum].active = qfalse;
		s_clients[clientNum].qhead = 0;
		s_clients[clientNum].qcount = 0;
	}
	pthread_mutex_unlock( &s_lock );
}

//=============================================================================
// per-frame server-thread entry point
//=============================================================================

void Botctl_Frame( int time ) {
	qboolean		now_enabled;
	int			frameMsec;
	int			i;

	if ( !botctl_enable ) {
		return;
	}

	// print what the UDS thread queued
	Botctl_DrainLog();

	// react to the enable cvar turning on/off at runtime. s_enabled is reset
	// by Botctl_Shutdown(), so after a server restart (SV_Restart runs
	// SV_Shutdown + SV_Init, which also drops all clients) the channel is
	// started again on the next frame
	now_enabled = botctl_enable->integer != 0;
	if ( now_enabled && !s_enabled ) {
		Botctl_Start();
	} else if ( !now_enabled && s_enabled ) {
		Botctl_Stop();
	}
	s_enabled = now_enabled;

	if ( !now_enabled ) {
		return;
	}
	if ( sv.state != SS_GAME || !svs.clients ) {
		return;
	}

	frameMsec = 1000 / ( sv_fps->integer ? sv_fps->integer : 20 );

	// 0. the sidecar connection died (crash, kill): the clients it drove have
	// no brain left, remove them like its own REMOVE would. SV_DropClient ->
	// Botctl_ClientDropped clears the management state.
	if ( s_sidecar_lost ) {
		s_sidecar_lost = qfalse;
		for ( i = 0; i < sv.maxclients; i++ ) {
			if ( s_clients[i].active ) {
				SV_DropClient( &svs.clients[i], "bot control connection lost" );
			}
		}
	}

	// 0b. botctl clients exchange no real packets, so nothing would ever
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
		// only publish the result if this request is still the pending one
		// (the sidecar may have timed out and withdrawn it, or - impossible
		// with the single listener thread - a newer one was submitted)
		if ( s_req_valid && s_req.seq == req.seq ) {
			s_req.result = res;
			s_req.done = qtrue;
			s_req_valid = qfalse;
		}
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
// reflects the playerState and entity states of the frame that just ran
// (not the previous one)
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
		Botctl_BuildSnapshot( time );
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
	// A peer that closed the socket must not be able to kill the server:
	// without this, send() to a closed peer raises SIGPIPE, whose default
	// action terminates the process (exit 141) BEFORE the -1/EPIPE below
	// is ever visible. macOS/BSD have no MSG_NOSIGNAL; the listener sets
	// SO_NOSIGPIPE per connection there instead.
#if defined(__linux__) || defined(__linux)
	int			flags = MSG_NOSIGNAL;
#else
	int			flags = 0;
#endif
	while ( sent < len ) {
		int		n = (int)send( fd, p + sent, len - sent, flags );
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
	byte			op;
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
	s_req.seq = ++s_req_seq;
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
			// withdraw the request: the server thread's completion check
			// (Botctl_Frame, seq compare) discards the result of a withdrawn
			// request, so a late ADD cannot resurrect a client the sidecar
			// does not know about. Narrow race that remains: if the server
			// thread had already copied the request when this timeout fires,
			// the action still happens (the client exists) but its result is
			// discarded: the client shows up in LIST and is dropped when
			// the connection ends. Harmless for the sidecar protocol (which
			// reconnects), but not strictly impossible.
			pthread_mutex_lock( &s_lock );
			if ( !s_req.done && s_req.seq == s_req_seq ) {
				s_req_valid = qfalse;
			}
			pthread_mutex_unlock( &s_lock );
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
		if ( ++timeout > 1000 ) {	// ~2 s: the server thread is stuck or gone
			pthread_mutex_lock( &s_lock );
			s_snap_requested = qfalse;
			pthread_mutex_unlock( &s_lock );
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
	qboolean	conn_broke = qfalse;

	Botctl_LogQ( "botctl: sidecar connected" );

	while ( !s_shutdown ) {
		int		op;
		op = bc_read_msg( fd, payload, (int)sizeof( payload ), &plen );
		if ( op == -1 ) {
			conn_broke = qtrue;	// disconnect
			break;
		}
		if ( op == -2 ) {
			continue;	// timeout
		}

		switch ( op ) {
		case BOTCTL_OP_PING: {
			const char *pong = "PONG";
			if ( bc_send_msg( fd, BOTCTL_OP_PING, pong, 4 ) < 0 ) {
				conn_broke = qtrue;
			}
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
				if ( bc_send_msg( fd, BOTCTL_OP_ADD, &out, 4 ) < 0 ) {
					conn_broke = qtrue;
				}
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
				if ( bc_send_msg( fd, BOTCTL_OP_REMOVE, &out, 4 ) < 0 ) {
					conn_broke = qtrue;
				}
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
				if ( bc_send_msg( fd, BOTCTL_OP_TEXT, &out, 4 ) < 0 ) {
					conn_broke = qtrue;
				}
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
						if ( bc_send_msg( fd, BOTCTL_OP_SNAP, NULL, 0 ) < 0 ) {
							conn_broke = qtrue;
						}
						break;
					}
					snap_out = nb;
					snap_cap = outlen;
				}
				pthread_mutex_lock( &s_lock );
				memcpy( snap_out, snap_buf, outlen );
				pthread_mutex_unlock( &s_lock );
				if ( bc_send_msg( fd, BOTCTL_OP_SNAP, snap_out, (int)outlen ) < 0 ) {
					conn_broke = qtrue;
				}
			} else {
				// send an empty snap so the sidecar doesn't block
				if ( bc_send_msg( fd, BOTCTL_OP_SNAP, NULL, 0 ) < 0 ) {
					conn_broke = qtrue;
				}
			}
			break;
		}

		case BOTCTL_OP_LIST: {
			bc_writer_t	w;
			byte			tmp[4096];
			int				count = 0;
			int				len;
			int				i;

			// s_clients is also mutated by the server thread: read it locked
			pthread_mutex_lock( &s_lock );
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
			len = w.len;
			pthread_mutex_unlock( &s_lock );
			if ( bc_send_msg( fd, BOTCTL_OP_LIST, tmp, len ) < 0 ) {
				conn_broke = qtrue;
			}
			break;
		}

		default:
			break;
		}

		if ( conn_broke ) {
			// a reply could not be delivered: the peer stopped consuming
			// (SO_SNDTIMEO fired) or the socket is gone, and a partially
			// sent frame may already sit on the wire: the stream can no
			// longer be trusted. Close instead of continuing with silently
			// dropped replies; the sidecar reconnects. Its managed clients
			// are dropped exactly like on any other connection loss
			// (s_sidecar_lost below).
			break;
		}
	}

	free( snap_out );
	if ( conn_broke && !s_shutdown ) {
		// the sidecar died or a reply send failed: Botctl_Frame will remove
		// the clients it drove
		Botctl_LogQ( "botctl: sidecar disconnected, removing its managed clients" );
		s_sidecar_lost = qtrue;
	} else {
		Botctl_LogQ( "botctl: sidecar disconnected" );
	}
	close( fd );
}

//=============================================================================
// UDS listener thread
//=============================================================================

static void *Botctl_ListenerThread( void *arg ) {
	struct sockaddr_un	addr;
	struct timeval		rcvtv, sndtv;
	int				conn;

	(void)arg;

	// create + bind + listen
	s_listen_fd = socket( AF_UNIX, SOCK_STREAM, 0 );
	if ( s_listen_fd < 0 ) {
		Botctl_LogQ( "botctl: socket() failed: %s", strerror( errno ) );
		return NULL;
	}

	if ( strlen( s_sockpath ) >= sizeof( addr.sun_path ) ) {
		Botctl_LogQ( "botctl: socket path too long (%i bytes, max %i): %s",
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
		Botctl_LogQ( "botctl: bind(%s) failed: %s", s_sockpath, strerror( errno ) );
		close( s_listen_fd );
		s_listen_fd = -1;
		return NULL;
	}
	// the socket drives client slots and can kick them: restrict it to the
	// server's own user (the umask default would be world-accessible)
	if ( chmod( s_sockpath, 0600 ) != 0 ) {
		Botctl_LogQ( "botctl: chmod(%s) failed: %s", s_sockpath, strerror( errno ) );
	}
	if ( listen( s_listen_fd, 2 ) < 0 ) {
		Botctl_LogQ( "botctl: listen() failed: %s", strerror( errno ) );
		close( s_listen_fd );
		s_listen_fd = -1;
		unlink( s_sockpath );
		return NULL;
	}

	Botctl_LogQ( "botctl: listening on %s", s_sockpath );

	// receive and send on the connection are bounded so this thread always
	// notices s_shutdown: a pthread_join can then never block forever, even
	// against a stalled or half-dead peer
	rcvtv.tv_sec = 0;	rcvtv.tv_usec = 500000;	// 500 ms
	sndtv.tv_sec = 0;	sndtv.tv_usec = 500000;	// 500 ms

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
		setsockopt( conn, SOL_SOCKET, SO_RCVTIMEO, &rcvtv, sizeof( rcvtv ) );
		setsockopt( conn, SOL_SOCKET, SO_SNDTIMEO, &sndtv, sizeof( sndtv ) );
#if defined(__APPLE__) || defined(__FreeBSD__) || defined(__NetBSD__) || defined(__OpenBSD__)
		{
			// no MSG_NOSIGNAL here: suppress SIGPIPE per socket
			int	no_sigpipe = 1;
			setsockopt( conn, SOL_SOCKET, SO_NOSIGPIPE, &no_sigpipe, sizeof( no_sigpipe ) );
		}
#endif
		Botctl_HandleConnection( conn );
		// keep listening: the sidecar may reconnect (it also has to survive
		// the server's own map/periodic restarts, which close this socket)
	}

	return NULL;
}

//=============================================================================
// start / stop
//=============================================================================

// Default socket path lives in the server's own home directory (where the
// installation's file permissions already protect it); botctl_sockpath
// overrides it with an absolute path of the operator's choice.
static void Botctl_DeriveSockpath( void ) {
	const char	*home;
	int			port;

	if ( botctl_sockpath && botctl_sockpath->string[0] ) {
		Q_strncpyz( s_sockpath, botctl_sockpath->string, sizeof( s_sockpath ) );
		return;
	}
	port = Cvar_VariableIntegerValue( "net_port" );
	if ( port <= 0 ) {
		port = 27960;
	}
	home = Cvar_VariableString( "fs_homepath" );
	if ( home && home[0] ) {
		Com_sprintf( s_sockpath, sizeof( s_sockpath ), "%s/botctl-%i.sock", home, port );
	} else {
		Com_sprintf( s_sockpath, sizeof( s_sockpath ), "/tmp/q3e-botctl-%i.sock", port );
	}
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
	s_sidecar_lost = qfalse;
	Botctl_DeriveSockpath();
	if ( pthread_create( &s_thread, NULL, Botctl_ListenerThread, NULL ) != 0 ) {
		Com_Printf( "botctl: pthread_create failed\n" );
		return;
	}
	s_thread_running = qtrue;
	Com_Printf( "botctl: started (socket %s)\n", s_sockpath );
}

static void Botctl_Stop( void ) {
	int i;

	if ( !s_thread_running ) {
		return;
	}
	s_shutdown = qtrue;
	// join is bounded: the listener's poll() waits are 50 ms, its request /
	// snapshot wait loops check s_shutdown every ~2 ms, and every socket op
	// on the connection has a 500 ms timeout
	pthread_join( s_thread, NULL );
	s_thread_running = qfalse;
	if ( s_listen_fd >= 0 ) {
		close( s_listen_fd );
		s_listen_fd = -1;
	}
	if ( s_sockpath[0] ) {
		unlink( s_sockpath );
	}
	// runtime botctl_enable 1->0 (and SV_Shutdown): drive the managed clients
	// out through the normal drop path, otherwise packetless clients would
	// linger until sv_timeout drops them
	if ( svs.clients ) {
		for ( i = 0; i < sv.maxclients; i++ ) {
			if ( s_clients[i].active ) {
				SV_DropClient( &svs.clients[i], "bot control disabled" );
			}
		}
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
	// reset all channel state: SV_Shutdown/SV_Init can run again (the
	// engine's time-wrap and 12h level-time restarts do exactly that), and
	// Botctl_Frame must see a clean off-state to bring the socket back up
	Com_Memset( s_clients, 0, sizeof( s_clients ) );
	s_enabled = qfalse;
	s_sidecar_lost = qfalse;
	s_snap_requested = qfalse;
	s_req_valid = qfalse;
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
