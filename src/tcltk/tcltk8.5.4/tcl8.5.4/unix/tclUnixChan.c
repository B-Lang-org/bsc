/*
 * tclUnixChan.c
 *
 *	Common channel driver for Unix channels based on files, command pipes
 *	and TCP sockets.
 *
 * Copyright (c) 1995-1997 Sun Microsystems, Inc.
 * Copyright (c) 1998-1999 by Scriptics Corporation.
 *
 * See the file "license.terms" for information on usage and redistribution of
 * this file, and for a DISCLAIMER OF ALL WARRANTIES.
 *
 * RCS: @(#) $Id: tclUnixChan.c,v 1.93 2008/03/03 14:54:43 rmax Exp $
 */

#include "tclInt.h"	/* Internal definitions for Tcl. */
#include "tclIO.h"	/* To get Channel type declaration. */

#define SUPPORTS_TTY

#undef DIRECT_BAUD
#ifdef B4800
#   if (B4800 == 4800)
#	define DIRECT_BAUD
#   endif /* B4800 == 4800 */
#endif /* B4800 */

#ifdef USE_TERMIOS
#   include <termios.h>
#   ifdef HAVE_SYS_IOCTL_H
#	include <sys/ioctl.h>
#   endif /* HAVE_SYS_IOCTL_H */
#   ifdef HAVE_SYS_MODEM_H
#	include <sys/modem.h>
#   endif /* HAVE_SYS_MODEM_H */
#   define IOSTATE			struct termios
#   define GETIOSTATE(fd, statePtr)	tcgetattr((fd), (statePtr))
#   define SETIOSTATE(fd, statePtr)	tcsetattr((fd), TCSADRAIN, (statePtr))
#   define GETCONTROL(fd, intPtr)	ioctl((fd), TIOCMGET, (intPtr))
#   define SETCONTROL(fd, intPtr)	ioctl((fd), TIOCMSET, (intPtr))

#   ifdef FIONREAD
#	define GETREADQUEUE(fd, int)	ioctl((fd), FIONREAD, &(int))
#   elif defined(FIORDCHK)
#	define GETREADQUEUE(fd, int)	int = ioctl((fd), FIORDCHK, NULL)
#   endif /* FIONREAD */
#   ifdef TIOCOUTQ
#	define GETWRITEQUEUE(fd, int)	ioctl((fd), TIOCOUTQ, &(int))
#   endif /* TIOCOUTQ */
#   if defined(TIOCSBRK) && defined(TIOCCBRK)

/*
 * Can't use ?: operator below because that messes up types on either Linux or
 * Solaris (the two are mutually exclusive!)
 */

#	define SETBREAK(fd, flag) \
		if (flag) {				\
		    ioctl((fd), TIOCSBRK, NULL);	\
		} else {				\
		    ioctl((fd), TIOCCBRK, NULL);	\
		}
#   endif /* TIOCSBRK&TIOCCBRK */
#   if !defined(CRTSCTS) && defined(CNEW_RTSCTS)
#	define CRTSCTS CNEW_RTSCTS
#   endif /* !CRTSCTS&CNEW_RTSCTS */
#   if !defined(PAREXT) && defined(CMSPAR)
#	define PAREXT CMSPAR
#   endif /* !PAREXT&&CMSPAR */
#else	/* !USE_TERMIOS */

#ifdef USE_TERMIO
#   include <termio.h>
#   define IOSTATE			struct termio
#   define GETIOSTATE(fd, statePtr)	ioctl((fd), TCGETA, (statePtr))
#   define SETIOSTATE(fd, statePtr)	ioctl((fd), TCSETAW, (statePtr))
#else	/* !USE_TERMIO */

#ifdef USE_SGTTY
#   include <sgtty.h>
#   define IOSTATE			struct sgttyb
#   define GETIOSTATE(fd, statePtr)	ioctl((fd), TIOCGETP, (statePtr))
#   define SETIOSTATE(fd, statePtr)	ioctl((fd), TIOCSETP, (statePtr))
#else	/* !USE_SGTTY */
#   undef SUPPORTS_TTY
#endif	/* !USE_SGTTY */

#endif	/* !USE_TERMIO */
#endif	/* !USE_TERMIOS */

/*
 * Helper macros to make parts of this file clearer. The macros do exactly
 * what they say on the tin. :-) They also only ever refer to their arguments
 * once, and so can be used without regard to side effects.
 */

#define SET_BITS(var, bits)	((var) |= (bits))
#define CLEAR_BITS(var, bits)	((var) &= ~(bits))

/*
 * This structure describes per-instance state of a file based channel.
 */

typedef struct FileState {
    Tcl_Channel channel;	/* Channel associated with this file. */
    int fd;			/* File handle. */
    int validMask;		/* OR'ed combination of TCL_READABLE,
				 * TCL_WRITABLE, or TCL_EXCEPTION: indicates
				 * which operations are valid on the file. */
} FileState;

#ifdef SUPPORTS_TTY

/*
 * The following structure describes per-instance state of a tty-based
 * channel.
 */

typedef struct TtyState {
    FileState fs;		/* Per-instance state of the file descriptor.
				 * Must be the first field. */
    IOSTATE savedState;		/* Initial state of device. Used to reset
				 * state when device closed. */
} TtyState;

/*
 * The following structure is used to set or get the serial port attributes in
 * a platform-independant manner.
 */

typedef struct TtyAttrs {
    int baud;
    int parity;
    int data;
    int stop;
} TtyAttrs;

#endif	/* !SUPPORTS_TTY */

#define UNSUPPORTED_OPTION(detail) \
    if (interp) {						\
	Tcl_AppendResult(interp, (detail),			\
		" not supported for this platform", NULL);	\
    }

/*
 * This structure describes per-instance state of a tcp based channel.
 */

typedef struct TcpState {
    Tcl_Channel channel;	/* Channel associated with this file. */
    int fd;			/* The socket itself. */
    int flags;			/* ORed combination of the bitfields defined
				 * below. */
    Tcl_TcpAcceptProc *acceptProc;
				/* Proc to call on accept. */
    ClientData acceptProcData;	/* The data for the accept proc. */
} TcpState;

/*
 * These bits may be ORed together into the "flags" field of a TcpState
 * structure.
 */

#define TCP_ASYNC_SOCKET	(1<<0)	/* Asynchronous socket. */
#define TCP_ASYNC_CONNECT	(1<<1)	/* Async connect in progress. */

/*
 * The following defines the maximum length of the listen queue. This is the
 * number of outstanding yet-to-be-serviced requests for a connection on a
 * server socket, more than this number of outstanding requests and the
 * connection request will fail.
 */

#ifndef SOMAXCONN
#   define SOMAXCONN	100
#endif /* SOMAXCONN */

#if (SOMAXCONN < 100)
#   undef  SOMAXCONN
#   define SOMAXCONN	100
#endif /* SOMAXCONN < 100 */

/*
 * The following defines how much buffer space the kernel should maintain for
 * a socket.
 */

#define SOCKET_BUFSIZE	4096

/*
 * Static routines for this file:
 */

static TcpState *	CreateSocket(Tcl_Interp *interp, int port,
			    const char *host, int server, const char *myaddr,
			    int myport, int async);
static int		CreateSocketAddress(struct sockaddr_in *sockaddrPtr,
			    const char *host, int port, int willBind,
			    const char **errorMsgPtr);
static int		FileBlockModeProc(ClientData instanceData, int mode);
static int		FileCloseProc(ClientData instanceData,
			    Tcl_Interp *interp);
static int		FileGetHandleProc(ClientData instanceData,
			    int direction, ClientData *handlePtr);
static int		FileInputProc(ClientData instanceData, char *buf,
			    int toRead, int *errorCode);
static int		FileOutputProc(ClientData instanceData,
			    const char *buf, int toWrite, int *errorCode);
static int		FileSeekProc(ClientData instanceData, long offset,
			    int mode, int *errorCode);
static int		FileTruncateProc(ClientData instanceData,
			    Tcl_WideInt length);
static Tcl_WideInt	FileWideSeekProc(ClientData instanceData,
			    Tcl_WideInt offset, int mode, int *errorCode);
static void		FileWatchProc(ClientData instanceData, int mask);
static void		TcpAccept(ClientData data, int mask);
static int		TcpBlockModeProc(ClientData data, int mode);
static int		TcpCloseProc(ClientData instanceData,
			    Tcl_Interp *interp);
static int		TcpGetHandleProc(ClientData instanceData,
			    int direction, ClientData *handlePtr);
static int		TcpGetOptionProc(ClientData instanceData,
			    Tcl_Interp *interp, const char *optionName,
			    Tcl_DString *dsPtr);
static int		TcpInputProc(ClientData instanceData, char *buf,
			    int toRead, int *errorCode);
static int		TcpOutputProc(ClientData instanceData,
			    const char *buf, int toWrite, int *errorCode);
static void		TcpWatchProc(ClientData instanceData, int mask);
#ifdef SUPPORTS_TTY
static void		TtyGetAttributes(int fd, TtyAttrs *ttyPtr);
static int		TtyGetOptionProc(ClientData instanceData,
			    Tcl_Interp *interp, const char *optionName,
			    Tcl_DString *dsPtr);
#ifndef DIRECT_BAUD
static int		TtyGetBaud(unsigned long speed);
static unsigned long	TtyGetSpeed(int baud);
#endif /* DIRECT_BAUD */
static FileState *	TtyInit(int fd, int initialize);
static void		TtyModemStatusStr(int status, Tcl_DString *dsPtr);
static int		TtyParseMode(Tcl_Interp *interp, const char *mode,
			    int *speedPtr, int *parityPtr, int *dataPtr,
			    int *stopPtr);
static void		TtySetAttributes(int fd, TtyAttrs *ttyPtr);
static int		TtySetOptionProc(ClientData instanceData,
			    Tcl_Interp *interp, const char *optionName,
			    const char *value);
#endif	/* SUPPORTS_TTY */
static int		WaitForConnect(TcpState *statePtr, int *errorCodePtr);
static Tcl_Channel	MakeTcpClientChannelMode(ClientData tcpSocket,
			    int mode);

/*
 * This structure describes the channel type structure for file based IO:
 */

static Tcl_ChannelType fileChannelType = {
    "file",			/* Type name. */
    TCL_CHANNEL_VERSION_5,	/* v5 channel */
    FileCloseProc,		/* Close proc. */
    FileInputProc,		/* Input proc. */
    FileOutputProc,		/* Output proc. */
    FileSeekProc,		/* Seek proc. */
    NULL,			/* Set option proc. */
    NULL,			/* Get option proc. */
    FileWatchProc,		/* Initialize notifier. */
    FileGetHandleProc,		/* Get OS handles out of channel. */
    NULL,			/* close2proc. */
    FileBlockModeProc,		/* Set blocking or non-blocking mode.*/
    NULL,			/* flush proc. */
    NULL,			/* handler proc. */
    FileWideSeekProc,		/* wide seek proc. */
    NULL,
    FileTruncateProc,		/* truncate proc. */
};

#ifdef SUPPORTS_TTY
/*
 * This structure describes the channel type structure for serial IO.
 * Note that this type is a subclass of the "file" type.
 */

static Tcl_ChannelType ttyChannelType = {
    "tty",			/* Type name. */
    TCL_CHANNEL_VERSION_5,	/* v5 channel */
    FileCloseProc,		/* Close proc. */
    FileInputProc,		/* Input proc. */
    FileOutputProc,		/* Output proc. */
    NULL,			/* Seek proc. */
    TtySetOptionProc,		/* Set option proc. */
    TtyGetOptionProc,		/* Get option proc. */
    FileWatchProc,		/* Initialize notifier. */
    FileGetHandleProc,		/* Get OS handles out of channel. */
    NULL,			/* close2proc. */
    FileBlockModeProc,		/* Set blocking or non-blocking mode.*/
    NULL,			/* flush proc. */
    NULL,			/* handler proc. */
    NULL,			/* wide seek proc. */
    NULL,			/* thread action proc. */
    NULL,			/* truncate proc. */
};
#endif	/* SUPPORTS_TTY */

/*
 * This structure describes the channel type structure for TCP socket
 * based IO:
 */

static Tcl_ChannelType tcpChannelType = {
    "tcp",			/* Type name. */
    TCL_CHANNEL_VERSION_5,	/* v5 channel */
    TcpCloseProc,		/* Close proc. */
    TcpInputProc,		/* Input proc. */
    TcpOutputProc,		/* Output proc. */
    NULL,			/* Seek proc. */
    NULL,			/* Set option proc. */
    TcpGetOptionProc,		/* Get option proc. */
    TcpWatchProc,		/* Initialize notifier. */
    TcpGetHandleProc,		/* Get OS handles out of channel. */
    NULL,			/* close2proc. */
    TcpBlockModeProc,		/* Set blocking or non-blocking mode.*/
    NULL,			/* flush proc. */
    NULL,			/* handler proc. */
    NULL,			/* wide seek proc. */
    NULL,			/* thread action proc. */
    NULL,			/* truncate proc. */
};

/*
 *----------------------------------------------------------------------
 *
 * FileBlockModeProc --
 *
 *	Helper function to set blocking and nonblocking modes on a file based
 *	channel. Invoked by generic IO level code.
 *
 * Results:
 *	0 if successful, errno when failed.
 *
 * Side effects:
 *	Sets the device into blocking or non-blocking mode.
 *
 *----------------------------------------------------------------------
 */

	/* ARGSUSED */
static int
FileBlockModeProc(
    ClientData instanceData,	/* File state. */
    int mode)			/* The mode to set. Can be one of
				 * TCL_MODE_BLOCKING or
				 * TCL_MODE_NONBLOCKING. */
{
    FileState *fsPtr = (FileState *) instanceData;

    if (TclUnixSetBlockingMode(fsPtr->fd, mode) < 0) {
	return errno;
    }

    return 0;
}

/*
 *----------------------------------------------------------------------
 *
 * FileInputProc --
 *
 *	This function is invoked from the generic IO level to read input from
 *	a file based channel.
 *
 * Results:
 *	The number of bytes read is returned or -1 on error. An output
 *	argument contains a POSIX error code if an error occurs, or zero.
 *
 * Side effects:
 *	Reads input from the input device of the channel.
 *
 *----------------------------------------------------------------------
 */

static int
FileInputProc(
    ClientData instanceData,	/* File state. */
    char *buf,			/* Where to store data read. */
    int toRead,			/* How much space is available in the
				 * buffer? */
    int *errorCodePtr)		/* Where to store error code. */
{
    FileState *fsPtr = (FileState *) instanceData;
    int bytesRead;		/* How many bytes were actually read from the
				 * input device? */

    *errorCodePtr = 0;

    /*
     * Assume there is always enough input available. This will block
     * appropriately, and read will unblock as soon as a short read is
     * possible, if the channel is in blocking mode. If the channel is
     * nonblocking, the read will never block.
     */

    bytesRead = read(fsPtr->fd, buf, (size_t) toRead);
    if (bytesRead > -1) {
	return bytesRead;
    }
    *errorCodePtr = errno;
    return -1;
}

/*
 *----------------------------------------------------------------------
 *
 * FileOutputProc--
 *
 *	This function is invoked from the generic IO level to write output to
 *	a file channel.
 *
 * Results:
 *	The number of bytes written is returned or -1 on error. An output
 *	argument contains a POSIX error code if an error occurred, or zero.
 *
 * Side effects:
 *	Writes output on the output device of the channel.
 *
 *----------------------------------------------------------------------
 */

static int
FileOutputProc(
    ClientData instanceData,	/* File state. */
    const char *buf,		/* The data buffer. */
    int toWrite,		/* How many bytes to write? */
    int *errorCodePtr)		/* Where to store error code. */
{
    FileState *fsPtr = (FileState *) instanceData;
    int written;

    *errorCodePtr = 0;

    if (toWrite == 0) {
	/*
	 * SF Tcl Bug 465765. Do not try to write nothing into a file. STREAM
	 * based implementations will considers this as EOF (if there is a
	 * pipe behind the file).
	 */

	return 0;
    }
    written = write(fsPtr->fd, buf, (size_t) toWrite);
    if (written > -1) {
	return written;
    }
    *errorCodePtr = errno;
    return -1;
}

/*
 *----------------------------------------------------------------------
 *
 * FileCloseProc --
 *
 *	This function is called from the generic IO level to perform
 *	channel-type-specific cleanup when a file based channel is closed.
 *
 * Results:
 *	0 if successful, errno if failed.
 *
 * Side effects:
 *	Closes the device of the channel.
 *
 *----------------------------------------------------------------------
 */

static int
FileCloseProc(
    ClientData instanceData,	/* File state. */
    Tcl_Interp *interp)		/* For error reporting - unused. */
{
    FileState *fsPtr = (FileState *) instanceData;
    int errorCode = 0;

    Tcl_DeleteFileHandler(fsPtr->fd);

    /*
     * Do not close standard channels while in thread-exit.
     */

    if (!TclInThreadExit()
	    || ((fsPtr->fd != 0) && (fsPtr->fd != 1) && (fsPtr->fd != 2))) {
	if (close(fsPtr->fd) < 0) {
	    errorCode = errno;
	}
    }
    ckfree((char *) fsPtr);
    return errorCode;
}

/*
 *----------------------------------------------------------------------
 *
 * FileSeekProc --
 *
 *	This function is called by the generic IO level to move the access
 *	point in a file based channel.
 *
 * Results:
 *	-1 if failed, the new position if successful. An output argument
 *	contains the POSIX error code if an error occurred, or zero.
 *
 * Side effects:
 *	Moves the location at which the channel will be accessed in future
 *	operations.
 *
 *----------------------------------------------------------------------
 */

static int
FileSeekProc(
    ClientData instanceData,	/* File state. */
    long offset,		/* Offset to seek to. */
    int mode,			/* Relative to where should we seek? Can be
				 * one of SEEK_START, SEEK_SET or SEEK_END. */
    int *errorCodePtr)		/* To store error code. */
{
    FileState *fsPtr = (FileState *) instanceData;
    Tcl_WideInt oldLoc, newLoc;

    /*
     * Save our current place in case we need to roll-back the seek.
     */

    oldLoc = TclOSseek(fsPtr->fd, (Tcl_SeekOffset) 0, SEEK_CUR);
    if (oldLoc == Tcl_LongAsWide(-1)) {
	/*
	 * Bad things are happening. Error out...
	 */

	*errorCodePtr = errno;
	return -1;
    }

    newLoc = TclOSseek(fsPtr->fd, (Tcl_SeekOffset) offset, mode);

    /*
     * Check for expressability in our return type, and roll-back otherwise.
     */

    if (newLoc > Tcl_LongAsWide(INT_MAX)) {
	*errorCodePtr = EOVERFLOW;
	TclOSseek(fsPtr->fd, (Tcl_SeekOffset) oldLoc, SEEK_SET);
	return -1;
    } else {
	*errorCodePtr = (newLoc == Tcl_LongAsWide(-1)) ? errno : 0;
    }
    return (int) Tcl_WideAsLong(newLoc);
}

/*
 *----------------------------------------------------------------------
 *
 * FileWideSeekProc --
 *
 *	This function is called by the generic IO level to move the access
 *	point in a file based channel, with offsets expressed as wide
 *	integers.
 *
 * Results:
 *	-1 if failed, the new position if successful. An output argument
 *	contains the POSIX error code if an error occurred, or zero.
 *
 * Side effects:
 *	Moves the location at which the channel will be accessed in future
 *	operations.
 *
 *----------------------------------------------------------------------
 */

static Tcl_WideInt
FileWideSeekProc(
    ClientData instanceData,	/* File state. */
    Tcl_WideInt offset,		/* Offset to seek to. */
    int mode,			/* Relative to where should we seek? Can be
				 * one of SEEK_START, SEEK_CUR or SEEK_END. */
    int *errorCodePtr)		/* To store error code. */
{
    FileState *fsPtr = (FileState *) instanceData;
    Tcl_WideInt newLoc;

    newLoc = TclOSseek(fsPtr->fd, (Tcl_SeekOffset) offset, mode);

    *errorCodePtr = (newLoc == -1) ? errno : 0;
    return newLoc;
}

/*
 *----------------------------------------------------------------------
 *
 * FileWatchProc --
 *
 *	Initialize the notifier to watch the fd from this channel.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	Sets up the notifier so that a future event on the channel will
 *	be seen by Tcl.
 *
 *----------------------------------------------------------------------
 */

static void
FileWatchProc(
    ClientData instanceData,	/* The file state. */
    int mask)			/* Events of interest; an OR-ed combination of
				 * TCL_READABLE, TCL_WRITABLE and
				 * TCL_EXCEPTION. */
{
    FileState *fsPtr = (FileState *) instanceData;

    /*
     * Make sure we only register for events that are valid on this file. Note
     * that we are passing Tcl_NotifyChannel directly to Tcl_CreateFileHandler
     * with the channel pointer as the client data.
     */

    mask &= fsPtr->validMask;
    if (mask) {
	Tcl_CreateFileHandler(fsPtr->fd, mask,
		(Tcl_FileProc *) Tcl_NotifyChannel,
		(ClientData) fsPtr->channel);
    } else {
	Tcl_DeleteFileHandler(fsPtr->fd);
    }
}

/*
 *----------------------------------------------------------------------
 *
 * FileGetHandleProc --
 *
 *	Called from Tcl_GetChannelHandle to retrieve OS handles from a file
 *	based channel.
 *
 * Results:
 *	Returns TCL_OK with the fd in handlePtr, or TCL_ERROR if there is no
 *	handle for the specified direction.
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */

static int
FileGetHandleProc(
    ClientData instanceData,	/* The file state. */
    int direction,		/* TCL_READABLE or TCL_WRITABLE */
    ClientData *handlePtr)	/* Where to store the handle. */
{
    FileState *fsPtr = (FileState *) instanceData;

    if (direction & fsPtr->validMask) {
	*handlePtr = (ClientData) INT2PTR(fsPtr->fd);
	return TCL_OK;
    }
    return TCL_ERROR;
}

#ifdef SUPPORTS_TTY
#ifdef USE_TERMIOS
/*
 *----------------------------------------------------------------------
 *
 * TtyModemStatusStr --
 *
 *	Converts a RS232 modem status list of readable flags
 *
 *----------------------------------------------------------------------
 */

static void
TtyModemStatusStr(
    int status,			/* RS232 modem status */
    Tcl_DString *dsPtr)		/* Where to store string */
{
#ifdef TIOCM_CTS
    Tcl_DStringAppendElement(dsPtr, "CTS");
    Tcl_DStringAppendElement(dsPtr, (status & TIOCM_CTS) ? "1" : "0");
#endif /* TIOCM_CTS */
#ifdef TIOCM_DSR
    Tcl_DStringAppendElement(dsPtr, "DSR");
    Tcl_DStringAppendElement(dsPtr, (status & TIOCM_DSR) ? "1" : "0");
#endif /* TIOCM_DSR */
#ifdef TIOCM_RNG
    Tcl_DStringAppendElement(dsPtr, "RING");
    Tcl_DStringAppendElement(dsPtr, (status & TIOCM_RNG) ? "1" : "0");
#endif /* TIOCM_RNG */
#ifdef TIOCM_CD
    Tcl_DStringAppendElement(dsPtr, "DCD");
    Tcl_DStringAppendElement(dsPtr, (status & TIOCM_CD) ? "1" : "0");
#endif /* TIOCM_CD */
}
#endif /* USE_TERMIOS */

/*
 *----------------------------------------------------------------------
 *
 * TtySetOptionProc --
 *
 *	Sets an option on a channel.
 *
 * Results:
 *	A standard Tcl result. Also sets the interp's result on error if
 *	interp is not NULL.
 *
 * Side effects:
 *	May modify an option on a device. Sets Error message if needed (by
 *	calling Tcl_BadChannelOption).
 *
 *----------------------------------------------------------------------
 */

static int
TtySetOptionProc(
    ClientData instanceData,	/* File state. */
    Tcl_Interp *interp,		/* For error reporting - can be NULL. */
    const char *optionName,	/* Which option to set? */
    const char *value)		/* New value for option. */
{
    FileState *fsPtr = (FileState *) instanceData;
    unsigned int len, vlen;
    TtyAttrs tty;
#ifdef USE_TERMIOS
    int flag, control, argc;
    const char **argv;
    IOSTATE iostate;
#endif /* USE_TERMIOS */

    len = strlen(optionName);
    vlen = strlen(value);

    /*
     * Option -mode baud,parity,databits,stopbits
     */
    if ((len > 2) && (strncmp(optionName, "-mode", len) == 0)) {
	if (TtyParseMode(interp, value, &tty.baud, &tty.parity, &tty.data,
		&tty.stop) != TCL_OK) {
	    return TCL_ERROR;
	}

	/*
	 * system calls results should be checked there. - dl
	 */

	TtySetAttributes(fsPtr->fd, &tty);
	return TCL_OK;
    }

#ifdef USE_TERMIOS

    /*
     * Option -handshake none|xonxoff|rtscts|dtrdsr
     */

    if ((len > 1) && (strncmp(optionName, "-handshake", len) == 0)) {
	/*
	 * Reset all handshake options. DTR and RTS are ON by default.
	 */

	GETIOSTATE(fsPtr->fd, &iostate);
	CLEAR_BITS(iostate.c_iflag, IXON | IXOFF | IXANY);
#ifdef CRTSCTS
	CLEAR_BITS(iostate.c_cflag, CRTSCTS);
#endif /* CRTSCTS */
	if (strncasecmp(value, "NONE", vlen) == 0) {
	    /* leave all handshake options disabled */
	} else if (strncasecmp(value, "XONXOFF", vlen) == 0) {
	    SET_BITS(iostate.c_iflag, IXON | IXOFF | IXANY);
	} else if (strncasecmp(value, "RTSCTS", vlen) == 0) {
#ifdef CRTSCTS
	    SET_BITS(iostate.c_cflag, CRTSCTS);
#else /* !CRTSTS */
	    UNSUPPORTED_OPTION("-handshake RTSCTS");
	    return TCL_ERROR;
#endif /* CRTSCTS */
	} else if (strncasecmp(value, "DTRDSR", vlen) == 0) {
	    UNSUPPORTED_OPTION("-handshake DTRDSR");
	    return TCL_ERROR;
	} else {
	    if (interp) {
		Tcl_AppendResult(interp, "bad value for -handshake: "
			"must be one of xonxoff, rtscts, dtrdsr or none",
			NULL);
	    }
	    return TCL_ERROR;
	}
	SETIOSTATE(fsPtr->fd, &iostate);
	return TCL_OK;
    }

    /*
     * Option -xchar {\x11 \x13}
     */

    if ((len > 1) && (strncmp(optionName, "-xchar", len) == 0)) {
	GETIOSTATE(fsPtr->fd, &iostate);
	if (Tcl_SplitList(interp, value, &argc, &argv) == TCL_ERROR) {
	    return TCL_ERROR;
	}
	if (argc == 2) {
	    Tcl_DString ds;
	    Tcl_DStringInit(&ds);

	    Tcl_UtfToExternalDString(NULL, argv[0], -1, &ds);
	    iostate.c_cc[VSTART] = *(const cc_t *) Tcl_DStringValue(&ds);
	    Tcl_DStringSetLength(&ds, 0);

	    Tcl_UtfToExternalDString(NULL, argv[1], -1, &ds);
	    iostate.c_cc[VSTOP] = *(const cc_t *) Tcl_DStringValue(&ds);
	    Tcl_DStringFree(&ds);
	} else {
	    if (interp) {
		Tcl_AppendResult(interp, "bad value for -xchar: "
			"should be a list of two elements", NULL);
	    }
	    ckfree((char *) argv);
	    return TCL_ERROR;
	}
	SETIOSTATE(fsPtr->fd, &iostate);
	ckfree((char *) argv);
	return TCL_OK;
    }

    /*
     * Option -timeout msec
     */

    if ((len > 2) && (strncmp(optionName, "-timeout", len) == 0)) {
	int msec;

	GETIOSTATE(fsPtr->fd, &iostate);
	if (Tcl_GetInt(interp, value, &msec) != TCL_OK) {
	    return TCL_ERROR;
	}
	iostate.c_cc[VMIN] = 0;
	iostate.c_cc[VTIME] = (msec==0) ? 0 : (msec<100) ? 1 : (msec+50)/100;
	SETIOSTATE(fsPtr->fd, &iostate);
	return TCL_OK;
    }

    /*
     * Option -ttycontrol {DTR 1 RTS 0 BREAK 0}
     */

    if ((len > 4) && (strncmp(optionName, "-ttycontrol", len) == 0)) {
	int i;

	if (Tcl_SplitList(interp, value, &argc, &argv) == TCL_ERROR) {
	    return TCL_ERROR;
	}
	if ((argc % 2) == 1) {
	    if (interp) {
		Tcl_AppendResult(interp, "bad value for -ttycontrol: "
			"should be a list of signal,value pairs", NULL);
	    }
	    ckfree((char *) argv);
	    return TCL_ERROR;
	}

	GETCONTROL(fsPtr->fd, &control);
	for (i = 0; i < argc-1; i += 2) {
	    if (Tcl_GetBoolean(interp, argv[i+1], &flag) == TCL_ERROR) {
		ckfree((char *) argv);
		return TCL_ERROR;
	    }
	    if (strncasecmp(argv[i], "DTR", strlen(argv[i])) == 0) {
#ifdef TIOCM_DTR
		if (flag) {
		    SET_BITS(control, TIOCM_DTR);
		} else {
		    CLEAR_BITS(control, TIOCM_DTR);
		}
#else /* !TIOCM_DTR */
		UNSUPPORTED_OPTION("-ttycontrol DTR");
		ckfree((char *) argv);
		return TCL_ERROR;
#endif /* TIOCM_DTR */
	    } else if (strncasecmp(argv[i], "RTS", strlen(argv[i])) == 0) {
#ifdef TIOCM_RTS
		if (flag) {
		    SET_BITS(control, TIOCM_RTS);
		} else {
		    CLEAR_BITS(control, TIOCM_RTS);
		}
#else /* !TIOCM_RTS*/
		UNSUPPORTED_OPTION("-ttycontrol RTS");
		ckfree((char *) argv);
		return TCL_ERROR;
#endif /* TIOCM_RTS*/
	    } else if (strncasecmp(argv[i], "BREAK", strlen(argv[i])) == 0) {
#ifdef SETBREAK
		SETBREAK(fsPtr->fd, flag);
#else /* !SETBREAK */
		UNSUPPORTED_OPTION("-ttycontrol BREAK");
		ckfree((char *) argv);
		return TCL_ERROR;
#endif /* SETBREAK */
	    } else {
		if (interp) {
		    Tcl_AppendResult(interp, "bad signal \"", argv[i],
			    "\" for -ttycontrol: must be "
			    "DTR, RTS or BREAK", NULL);
		}
		ckfree((char *) argv);
		return TCL_ERROR;
	    }
	} /* -ttycontrol options loop */

	SETCONTROL(fsPtr->fd, &control);
	ckfree((char *) argv);
	return TCL_OK;
    }

    return Tcl_BadChannelOption(interp, optionName,
	    "mode handshake timeout ttycontrol xchar");

#else /* !USE_TERMIOS */
    return Tcl_BadChannelOption(interp, optionName, "mode");
#endif /* USE_TERMIOS */
}

/*
 *----------------------------------------------------------------------
 *
 * TtyGetOptionProc --
 *
 *	Gets a mode associated with an IO channel. If the optionName arg is
 *	non-NULL, retrieves the value of that option. If the optionName arg is
 *	NULL, retrieves a list of alternating option names and values for the
 *	given channel.
 *
 * Results:
 *	A standard Tcl result. Also sets the supplied DString to the string
 *	value of the option(s) returned.
 *
 * Side effects:
 *	The string returned by this function is in static storage and may be
 *	reused at any time subsequent to the call. Sets error message if
 *	needed (by calling Tcl_BadChannelOption).
 *
 *----------------------------------------------------------------------
 */

static int
TtyGetOptionProc(
    ClientData instanceData,	/* File state. */
    Tcl_Interp *interp,		/* For error reporting - can be NULL. */
    const char *optionName,	/* Option to get. */
    Tcl_DString *dsPtr)		/* Where to store value(s). */
{
    FileState *fsPtr = (FileState *) instanceData;
    unsigned int len;
    char buf[3*TCL_INTEGER_SPACE + 16];
    int valid = 0;		/* Flag if valid option parsed. */

    if (optionName == NULL) {
	len = 0;
    } else {
	len = strlen(optionName);
    }
    if (len == 0) {
	Tcl_DStringAppendElement(dsPtr, "-mode");
    }
    if (len==0 || (len>2 && strncmp(optionName, "-mode", len)==0)) {
	TtyAttrs tty;

	valid = 1;
	TtyGetAttributes(fsPtr->fd, &tty);
	sprintf(buf, "%d,%c,%d,%d", tty.baud, tty.parity, tty.data, tty.stop);
	Tcl_DStringAppendElement(dsPtr, buf);
    }

#ifdef USE_TERMIOS
    /*
     * Get option -xchar
     */

    if (len == 0) {
	Tcl_DStringAppendElement(dsPtr, "-xchar");
	Tcl_DStringStartSublist(dsPtr);
    }
    if (len==0 || (len>1 && strncmp(optionName, "-xchar", len)==0)) {
	IOSTATE iostate;
	Tcl_DString ds;
	valid = 1;

	GETIOSTATE(fsPtr->fd, &iostate);
	Tcl_DStringInit(&ds);

	Tcl_ExternalToUtfDString(NULL,  (const char *) &iostate.c_cc[VSTART], 1, &ds);
	Tcl_DStringAppendElement(dsPtr, (const char *) Tcl_DStringValue(&ds));
	Tcl_DStringSetLength(&ds, 0);

	Tcl_ExternalToUtfDString(NULL,  (const char *) &iostate.c_cc[VSTOP], 1, &ds);
	Tcl_DStringAppendElement(dsPtr, (const char *) Tcl_DStringValue(&ds));
	Tcl_DStringFree(&ds);
    }
    if (len == 0) {
	Tcl_DStringEndSublist(dsPtr);
    }

    /*
     * Get option -queue
     * Option is readonly and returned by [fconfigure chan -queue] but not
     * returned by unnamed [fconfigure chan].
     */

    if ((len > 1) && (strncmp(optionName, "-queue", len) == 0)) {
	int inQueue=0, outQueue=0, inBuffered, outBuffered;

	valid = 1;
#ifdef GETREADQUEUE
	GETREADQUEUE(fsPtr->fd, inQueue);
#endif /* GETREADQUEUE */
#ifdef GETWRITEQUEUE
	GETWRITEQUEUE(fsPtr->fd, outQueue);
#endif /* GETWRITEQUEUE */
	inBuffered = Tcl_InputBuffered(fsPtr->channel);
	outBuffered = Tcl_OutputBuffered(fsPtr->channel);

	sprintf(buf, "%d", inBuffered+inQueue);
	Tcl_DStringAppendElement(dsPtr, buf);
	sprintf(buf, "%d", outBuffered+outQueue);
	Tcl_DStringAppendElement(dsPtr, buf);
    }

    /*
     * Get option -ttystatus
     * Option is readonly and returned by [fconfigure chan -ttystatus] but not
     * returned by unnamed [fconfigure chan].
     */
    if ((len > 4) && (strncmp(optionName, "-ttystatus", len) == 0)) {
	int status;

	valid = 1;
	GETCONTROL(fsPtr->fd, &status);
	TtyModemStatusStr(status, dsPtr);
    }
#endif /* USE_TERMIOS */

    if (valid) {
	return TCL_OK;
    }
    return Tcl_BadChannelOption(interp, optionName, "mode"
#ifdef USE_TERMIOS
	    " queue ttystatus xchar"
#endif /* USE_TERMIOS */
	    );
}

#ifdef DIRECT_BAUD
#   define TtyGetSpeed(baud)	((unsigned) (baud))
#   define TtyGetBaud(speed)	((int) (speed))
#else /* !DIRECT_BAUD */

static struct {int baud; unsigned long speed;} speeds[] = {
#ifdef B0
    {0, B0},
#endif
#ifdef B50
    {50, B50},
#endif
#ifdef B75
    {75, B75},
#endif
#ifdef B110
    {110, B110},
#endif
#ifdef B134
    {134, B134},
#endif
#ifdef B150
    {150, B150},
#endif
#ifdef B200
    {200, B200},
#endif
#ifdef B300
    {300, B300},
#endif
#ifdef B600
    {600, B600},
#endif
#ifdef B1200
    {1200, B1200},
#endif
#ifdef B1800
    {1800, B1800},
#endif
#ifdef B2400
    {2400, B2400},
#endif
#ifdef B4800
    {4800, B4800},
#endif
#ifdef B9600
    {9600, B9600},
#endif
#ifdef B14400
    {14400, B14400},
#endif
#ifdef B19200
    {19200, B19200},
#endif
#ifdef EXTA
    {19200, EXTA},
#endif
#ifdef B28800
    {28800, B28800},
#endif
#ifdef B38400
    {38400, B38400},
#endif
#ifdef EXTB
    {38400, EXTB},
#endif
#ifdef B57600
    {57600, B57600},
#endif
#ifdef _B57600
    {57600, _B57600},
#endif
#ifdef B76800
    {76800, B76800},
#endif
#ifdef B115200
    {115200, B115200},
#endif
#ifdef _B115200
    {115200, _B115200},
#endif
#ifdef B153600
    {153600, B153600},
#endif
#ifdef B230400
    {230400, B230400},
#endif
#ifdef B307200
    {307200, B307200},
#endif
#ifdef B460800
    {460800, B460800},
#endif
    {-1, 0}
};

/*
 *---------------------------------------------------------------------------
 *
 * TtyGetSpeed --
 *
 *	Given a baud rate, get the mask value that should be stored in the
 *	termios, termio, or sgttyb structure in order to select that baud
 *	rate.
 *
 * Results:
 *	As above.
 *
 * Side effects:
 *	None.
 *
 *---------------------------------------------------------------------------
 */

static unsigned long
TtyGetSpeed(
    int baud)			/* The baud rate to look up. */
{
    int bestIdx, bestDiff, i, diff;

    bestIdx = 0;
    bestDiff = 1000000;

    /*
     * If the baud rate does not correspond to one of the known mask values,
     * choose the mask value whose baud rate is closest to the specified baud
     * rate.
     */

    for (i = 0; speeds[i].baud >= 0; i++) {
	diff = speeds[i].baud - baud;
	if (diff < 0) {
	    diff = -diff;
	}
	if (diff < bestDiff) {
	    bestIdx = i;
	    bestDiff = diff;
	}
    }
    return speeds[bestIdx].speed;
}

/*
 *---------------------------------------------------------------------------
 *
 * TtyGetBaud --
 *
 *	Given a speed mask value from a termios, termio, or sgttyb structure,
 *	get the baus rate that corresponds to that mask value.
 *
 * Results:
 *	As above. If the mask value was not recognized, 0 is returned.
 *
 * Side effects:
 *	None.
 *
 *---------------------------------------------------------------------------
 */

static int
TtyGetBaud(
    unsigned long speed)	/* Speed mask value to look up. */
{
    int i;

    for (i = 0; speeds[i].baud >= 0; i++) {
	if (speeds[i].speed == speed) {
	    return speeds[i].baud;
	}
    }
    return 0;
}
#endif /* !DIRECT_BAUD */

/*
 *---------------------------------------------------------------------------
 *
 * TtyGetAttributes --
 *
 *	Get the current attributes of the specified serial device.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	None.
 *
 *---------------------------------------------------------------------------
 */

static void
TtyGetAttributes(
    int fd,			/* Open file descriptor for serial port to be
				 * queried. */
    TtyAttrs *ttyPtr)		/* Buffer filled with serial port
				 * attributes. */
{
    IOSTATE iostate;
    int baud, parity, data, stop;

    GETIOSTATE(fd, &iostate);

#ifdef USE_TERMIOS
    baud = TtyGetBaud(cfgetospeed(&iostate));

    parity = 'n';
#ifdef PAREXT
    switch ((int) (iostate.c_cflag & (PARENB | PARODD | PAREXT))) {
    case PARENB			  : parity = 'e'; break;
    case PARENB | PARODD	  : parity = 'o'; break;
    case PARENB |	   PAREXT : parity = 's'; break;
    case PARENB | PARODD | PAREXT : parity = 'm'; break;
    }
#else /* !PAREXT */
    switch ((int) (iostate.c_cflag & (PARENB | PARODD))) {
    case PARENB		 : parity = 'e'; break;
    case PARENB | PARODD : parity = 'o'; break;
    }
#endif /* !PAREXT */

    data = iostate.c_cflag & CSIZE;
    data = (data == CS5) ? 5 : (data == CS6) ? 6 : (data == CS7) ? 7 : 8;

    stop = (iostate.c_cflag & CSTOPB) ? 2 : 1;
#endif /* USE_TERMIOS */

#ifdef USE_TERMIO
    baud = TtyGetBaud(iostate.c_cflag & CBAUD);

    parity = 'n';
    switch (iostate.c_cflag & (PARENB | PARODD | PAREXT)) {
    case PARENB			  : parity = 'e'; break;
    case PARENB | PARODD	  : parity = 'o'; break;
    case PARENB |	   PAREXT : parity = 's'; break;
    case PARENB | PARODD | PAREXT : parity = 'm'; break;
    }

    data = iostate.c_cflag & CSIZE;
    data = (data == CS5) ? 5 : (data == CS6) ? 6 : (data == CS7) ? 7 : 8;

    stop = (iostate.c_cflag & CSTOPB) ? 2 : 1;
#endif /* USE_TERMIO */

#ifdef USE_SGTTY
    baud = TtyGetBaud(iostate.sg_ospeed);

    parity = 'n';
    if (iostate.sg_flags & EVENP) {
	parity = 'e';
    } else if (iostate.sg_flags & ODDP) {
	parity = 'o';
    }

    data = (iostate.sg_flags & (EVENP | ODDP)) ? 7 : 8;

    stop = 1;
#endif /* USE_SGTTY */

    ttyPtr->baud    = baud;
    ttyPtr->parity  = parity;
    ttyPtr->data    = data;
    ttyPtr->stop    = stop;
}

/*
 *---------------------------------------------------------------------------
 *
 * TtySetAttributes --
 *
 *	Set the current attributes of the specified serial device.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	None.
 *
 *---------------------------------------------------------------------------
 */

static void
TtySetAttributes(
    int fd,			/* Open file descriptor for serial port to be
				 * modified. */
    TtyAttrs *ttyPtr)		/* Buffer containing new attributes for serial
				 * port. */
{
    IOSTATE iostate;

#ifdef USE_TERMIOS
    int parity, data, flag;

    GETIOSTATE(fd, &iostate);
    cfsetospeed(&iostate, TtyGetSpeed(ttyPtr->baud));
    cfsetispeed(&iostate, TtyGetSpeed(ttyPtr->baud));

    flag = 0;
    parity = ttyPtr->parity;
    if (parity != 'n') {
	SET_BITS(flag, PARENB);
#ifdef PAREXT
	CLEAR_BITS(iostate.c_cflag, PAREXT);
	if ((parity == 'm') || (parity == 's')) {
	    SET_BITS(flag, PAREXT);
	}
#endif /* PAREXT */
	if ((parity == 'm') || (parity == 'o')) {
	    SET_BITS(flag, PARODD);
	}
    }
    data = ttyPtr->data;
    SET_BITS(flag,
	    (data == 5) ? CS5 :
	    (data == 6) ? CS6 :
	    (data == 7) ? CS7 : CS8);
    if (ttyPtr->stop == 2) {
	SET_BITS(flag, CSTOPB);
    }

    CLEAR_BITS(iostate.c_cflag, PARENB | PARODD | CSIZE | CSTOPB);
    SET_BITS(iostate.c_cflag, flag);

#endif	/* USE_TERMIOS */

#ifdef USE_TERMIO
    int parity, data, flag;

    GETIOSTATE(fd, &iostate);
    CLEAR_BITS(iostate.c_cflag, CBAUD);
    SET_BITS(iostate.c_cflag, TtyGetSpeed(ttyPtr->baud));

    flag = 0;
    parity = ttyPtr->parity;
    if (parity != 'n') {
	SET_BITS(flag, PARENB);
	if ((parity == 'm') || (parity == 's')) {
	    SET_BITS(flag, PAREXT);
	}
	if ((parity == 'm') || (parity == 'o')) {
	    SET_BITS(flag, PARODD);
	}
    }
    data = ttyPtr->data;
    SET_BITS(flag,
	    (data == 5) ? CS5 :
	    (data == 6) ? CS6 :
	    (data == 7) ? CS7 : CS8);
    if (ttyPtr->stop == 2) {
	SET_BITS(flag, CSTOPB);
    }

    CLEAR_BITS(iostate.c_cflag, PARENB | PARODD | PAREXT | CSIZE | CSTOPB);
    SET_BITS(iostate.c_cflag, flag);

#endif	/* USE_TERMIO */

#ifdef USE_SGTTY
    int parity;

    GETIOSTATE(fd, &iostate);
    iostate.sg_ospeed = TtyGetSpeed(ttyPtr->baud);
    iostate.sg_ispeed = TtyGetSpeed(ttyPtr->baud);

    parity = ttyPtr->parity;
    if (parity == 'e') {
	CLEAR_BITS(iostate.sg_flags, ODDP);
	SET_BITS(iostate.sg_flags, EVENP);
    } else if (parity == 'o') {
	CLEAR_BITS(iostate.sg_flags, EVENP);
	SET_BITS(iostate.sg_flags, ODDP);
    }
#endif	/* USE_SGTTY */

    SETIOSTATE(fd, &iostate);
}

/*
 *---------------------------------------------------------------------------
 *
 * TtyParseMode --
 *
 *	Parse the "-mode" argument to the fconfigure command. The argument is
 *	of the form baud,parity,data,stop.
 *
 * Results:
 *	The return value is TCL_OK if the argument was successfully parsed,
 *	TCL_ERROR otherwise. If TCL_ERROR is returned, an error message is
 *	left in the interp's result (if interp is non-NULL).
 *
 * Side effects:
 *	None.
 *
 *---------------------------------------------------------------------------
 */

static int
TtyParseMode(
    Tcl_Interp *interp,		/* If non-NULL, interp for error return. */
    const char *mode,		/* Mode string to be parsed. */
    int *speedPtr,		/* Filled with baud rate from mode string. */
    int *parityPtr,		/* Filled with parity from mode string. */
    int *dataPtr,		/* Filled with data bits from mode string. */
    int *stopPtr)		/* Filled with stop bits from mode string. */
{
    int i, end;
    char parity;
    static const char *bad = "bad value for -mode";

    i = sscanf(mode, "%d,%c,%d,%d%n", speedPtr, &parity, dataPtr,
	    stopPtr, &end);
    if ((i != 4) || (mode[end] != '\0')) {
	if (interp != NULL) {
	    Tcl_AppendResult(interp, bad, ": should be baud,parity,data,stop",
		    NULL);
	}
	return TCL_ERROR;
    }

    /*
     * Only allow setting mark/space parity on platforms that support it Make
     * sure to allow for the case where strchr is a macro. [Bug: 5089]
     */

#if defined(PAREXT) || defined(USE_TERMIO)
    if (strchr("noems", parity) == NULL) {
#else
    if (strchr("noe", parity) == NULL) {
#endif /* PAREXT|USE_TERMIO */
	if (interp != NULL) {
	    Tcl_AppendResult(interp, bad, " parity: should be ",
#if defined(PAREXT) || defined(USE_TERMIO)
		    "n, o, e, m, or s",
#else
		    "n, o, or e",
#endif /* PAREXT|USE_TERMIO */
		    NULL);
	}
	return TCL_ERROR;
    }
    *parityPtr = parity;
    if ((*dataPtr < 5) || (*dataPtr > 8)) {
	if (interp != NULL) {
	    Tcl_AppendResult(interp, bad, " data: should be 5, 6, 7, or 8",
		    NULL);
	}
	return TCL_ERROR;
    }
    if ((*stopPtr < 0) || (*stopPtr > 2)) {
	if (interp != NULL) {
	    Tcl_AppendResult(interp, bad, " stop: should be 1 or 2", NULL);
	}
	return TCL_ERROR;
    }
    return TCL_OK;
}

/*
 *---------------------------------------------------------------------------
 *
 * TtyInit --
 *
 *	Given file descriptor that refers to a serial port, initialize the
 *	serial port to a set of sane values so that Tcl can talk to a device
 *	located on the serial port. Note that no initialization happens if the
 *	initialize flag is not set; this is necessary for the correct handling
 *	of UNIX console TTYs at startup.
 *
 * Results:
 *	A pointer to a FileState suitable for use with Tcl_CreateChannel and
 *	the ttyChannelType structure.
 *
 * Side effects:
 *	Serial device initialized to non-blocking raw mode, similar to sockets
 *	(if initialize flag is non-zero.) All other modes can be simulated on
 *	top of this in Tcl.
 *
 *---------------------------------------------------------------------------
 */

static FileState *
TtyInit(
    int fd,			/* Open file descriptor for serial port to be
				 * initialized. */
    int initialize)
{
    TtyState *ttyPtr;
    int stateUpdated = 0;

    ttyPtr = (TtyState *) ckalloc((unsigned) sizeof(TtyState));
    GETIOSTATE(fd, &ttyPtr->savedState);
    if (initialize) {
	IOSTATE iostate = ttyPtr->savedState;

#if defined(USE_TERMIOS) || defined(USE_TERMIO)
	if (iostate.c_iflag != IGNBRK ||
		iostate.c_oflag != 0 ||
		iostate.c_lflag != 0 ||
		iostate.c_cflag & CREAD ||
		iostate.c_cc[VMIN] != 1 ||
		iostate.c_cc[VTIME] != 0) {
	    stateUpdated = 1;
	}
	iostate.c_iflag = IGNBRK;
	iostate.c_oflag = 0;
	iostate.c_lflag = 0;
	SET_BITS(iostate.c_cflag, CREAD);
	iostate.c_cc[VMIN] = 1;
	iostate.c_cc[VTIME] = 0;
#endif	/* USE_TERMIOS|USE_TERMIO */

#ifdef USE_SGTTY
	if ((iostate.sg_flags & (EVENP | ODDP)) ||
		!(iostate.sg_flags & RAW)) {
	    ttyPtr->stateUpdated = 1;
	}
	iostate.sg_flags &= EVENP | ODDP;
	SET_BITS(iostate.sg_flags, RAW);
#endif	/* USE_SGTTY */

	/*
	 * Only update if we're changing anything to avoid possible blocking.
	 */

	if (stateUpdated) {
	    SETIOSTATE(fd, &iostate);
	}
    }

    return &ttyPtr->fs;
}
#endif	/* SUPPORTS_TTY */

/*
 *----------------------------------------------------------------------
 *
 * TclpOpenFileChannel --
 *
 *	Open an file based channel on Unix systems.
 *
 * Results:
 *	The new channel or NULL. If NULL, the output argument errorCodePtr is
 *	set to a POSIX error and an error message is left in the interp's
 *	result if interp is not NULL.
 *
 * Side effects:
 *	May open the channel and may cause creation of a file on the file
 *	system.
 *
 *----------------------------------------------------------------------
 */

Tcl_Channel
TclpOpenFileChannel(
    Tcl_Interp *interp,		/* Interpreter for error reporting; can be
				 * NULL. */
    Tcl_Obj *pathPtr,		/* Name of file to open. */
    int mode,			/* POSIX open mode. */
    int permissions)		/* If the open involves creating a file, with
				 * what modes to create it? */
{
    int fd, channelPermissions;
    FileState *fsPtr;
    const char *native, *translation;
    char channelName[16 + TCL_INTEGER_SPACE];
    Tcl_ChannelType *channelTypePtr;

    switch (mode & (O_RDONLY | O_WRONLY | O_RDWR)) {
    case O_RDONLY:
	channelPermissions = TCL_READABLE;
	break;
    case O_WRONLY:
	channelPermissions = TCL_WRITABLE;
	break;
    case O_RDWR:
	channelPermissions = (TCL_READABLE | TCL_WRITABLE);
	break;
    default:
	/*
	 * This may occurr if modeString was "", for example.
	 */

	Tcl_Panic("TclpOpenFileChannel: invalid mode value");
	return NULL;
    }

    native = Tcl_FSGetNativePath(pathPtr);
    if (native == NULL) {
	return NULL;
    }

#ifdef DJGPP
    SET_BITS(mode, O_BINARY);
#endif

    fd = TclOSopen(native, mode, permissions);

    if (fd < 0) {
	if (interp != NULL) {
	    Tcl_AppendResult(interp, "couldn't open \"", TclGetString(pathPtr),
		    "\": ", Tcl_PosixError(interp), NULL);
	}
	return NULL;
    }

    /*
     * Set close-on-exec flag on the fd so that child processes will not
     * inherit this fd.
     */

    fcntl(fd, F_SETFD, FD_CLOEXEC);

    sprintf(channelName, "file%d", fd);

#ifdef SUPPORTS_TTY
    if (strcmp(native, "/dev/tty") != 0 && isatty(fd)) {
	/*
	 * Initialize the serial port to a set of sane parameters. Especially
	 * important if the remote device is set to echo and the serial port
	 * driver was also set to echo -- as soon as a char were sent to the
	 * serial port, the remote device would echo it, then the serial
	 * driver would echo it back to the device, etc.
	 *
	 * Note that we do not do this if we're dealing with /dev/tty itself,
	 * as that tends to cause Bad Things To Happen when you're working
	 * interactively. Strictly a better check would be to see if the FD
	 * being set up is a device and has the same major/minor as the
	 * initial std FDs (beware reopening!) but that's nearly as messy.
	 */

	translation = "auto crlf";
	channelTypePtr = &ttyChannelType;
	fsPtr = TtyInit(fd, 1);
    } else
#endif	/* SUPPORTS_TTY */
    {
	translation = NULL;
	channelTypePtr = &fileChannelType;
	fsPtr = (FileState *) ckalloc((unsigned) sizeof(FileState));
    }

    fsPtr->validMask = channelPermissions | TCL_EXCEPTION;
    fsPtr->fd = fd;

    fsPtr->channel = Tcl_CreateChannel(channelTypePtr, channelName,
	    (ClientData) fsPtr, channelPermissions);

    if (translation != NULL) {
	/*
	 * Gotcha. Most modems need a "\r" at the end of the command sequence.
	 * If you just send "at\n", the modem will not respond with "OK"
	 * because it never got a "\r" to actually invoke the command. So, by
	 * default, newlines are translated to "\r\n" on output to avoid "bug"
	 * reports that the serial port isn't working.
	 */

	if (Tcl_SetChannelOption(interp, fsPtr->channel, "-translation",
		translation) != TCL_OK) {
	    Tcl_Close(NULL, fsPtr->channel);
	    return NULL;
	}
    }

    return fsPtr->channel;
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_MakeFileChannel --
 *
 *	Makes a Tcl_Channel from an existing OS level file handle.
 *
 * Results:
 *	The Tcl_Channel created around the preexisting OS level file handle.
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */

Tcl_Channel
Tcl_MakeFileChannel(
    ClientData handle,		/* OS level handle. */
    int mode)			/* ORed combination of TCL_READABLE and
				 * TCL_WRITABLE to indicate file mode. */
{
    FileState *fsPtr;
    char channelName[16 + TCL_INTEGER_SPACE];
    int fd = PTR2INT(handle);
    Tcl_ChannelType *channelTypePtr;
    struct sockaddr sockaddr;
    socklen_t sockaddrLen = sizeof(sockaddr);

    if (mode == 0) {
	return NULL;
    }

    sockaddr.sa_family = AF_UNSPEC;

#ifdef SUPPORTS_TTY
    if (isatty(fd)) {
	fsPtr = TtyInit(fd, 0);
	channelTypePtr = &ttyChannelType;
	sprintf(channelName, "serial%d", fd);
    } else
#endif /* SUPPORTS_TTY */
    if (getsockname(fd, (struct sockaddr *)&sockaddr, &sockaddrLen) == 0
	    && sockaddrLen > 0
	    && sockaddr.sa_family == AF_INET) {
	return MakeTcpClientChannelMode((ClientData) INT2PTR(fd), mode);
    } else {
	channelTypePtr = &fileChannelType;
	fsPtr = (FileState *) ckalloc((unsigned) sizeof(FileState));
	sprintf(channelName, "file%d", fd);
    }

    fsPtr->fd = fd;
    fsPtr->validMask = mode | TCL_EXCEPTION;
    fsPtr->channel = Tcl_CreateChannel(channelTypePtr, channelName,
	    (ClientData) fsPtr, mode);

    return fsPtr->channel;
}

/*
 *----------------------------------------------------------------------
 *
 * TcpBlockModeProc --
 *
 *	This function is invoked by the generic IO level to set blocking and
 *	nonblocking mode on a TCP socket based channel.
 *
 * Results:
 *	0 if successful, errno when failed.
 *
 * Side effects:
 *	Sets the device into blocking or nonblocking mode.
 *
 *----------------------------------------------------------------------
 */

	/* ARGSUSED */
static int
TcpBlockModeProc(
    ClientData instanceData,	/* Socket state. */
    int mode)			/* The mode to set. Can be one of
				 * TCL_MODE_BLOCKING or
				 * TCL_MODE_NONBLOCKING. */
{
    TcpState *statePtr = (TcpState *) instanceData;

    if (mode == TCL_MODE_BLOCKING) {
	CLEAR_BITS(statePtr->flags, TCP_ASYNC_SOCKET);
    } else {
	SET_BITS(statePtr->flags, TCP_ASYNC_SOCKET);
    }
    if (TclUnixSetBlockingMode(statePtr->fd, mode) < 0) {
	return errno;
    }
    return 0;
}

/*
 *----------------------------------------------------------------------
 *
 * WaitForConnect --
 *
 *	Waits for a connection on an asynchronously opened socket to be
 *	completed.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	The socket is connected after this function returns.
 *
 *----------------------------------------------------------------------
 */

static int
WaitForConnect(
    TcpState *statePtr,		/* State of the socket. */
    int *errorCodePtr)		/* Where to store errors? */
{
    int timeOut;		/* How long to wait. */
    int state;			/* Of calling TclWaitForFile. */

    /*
     * If an asynchronous connect is in progress, attempt to wait for it to
     * complete before reading.
     */

    if (statePtr->flags & TCP_ASYNC_CONNECT) {
	if (statePtr->flags & TCP_ASYNC_SOCKET) {
	    timeOut = 0;
	} else {
	    timeOut = -1;
	}
	errno = 0;
	state = TclUnixWaitForFile(statePtr->fd,
		TCL_WRITABLE | TCL_EXCEPTION, timeOut);
	if (!(statePtr->flags & TCP_ASYNC_SOCKET)) {
	    (void) TclUnixSetBlockingMode(statePtr->fd, TCL_MODE_BLOCKING);
	}
	if (state & TCL_EXCEPTION) {
	    return -1;
	}
	if (state & TCL_WRITABLE) {
	    CLEAR_BITS(statePtr->flags, TCP_ASYNC_CONNECT);
	} else if (timeOut == 0) {
	    *errorCodePtr = errno = EWOULDBLOCK;
	    return -1;
	}
    }
    return 0;
}

/*
 *----------------------------------------------------------------------
 *
 * TcpInputProc --
 *
 *	This function is invoked by the generic IO level to read input from a
 *	TCP socket based channel.
 *
 *	NOTE: We cannot share code with FilePipeInputProc because here we must
 *	use recv to obtain the input from the channel, not read.
 *
 * Results:
 *	The number of bytes read is returned or -1 on error. An output
 *	argument contains the POSIX error code on error, or zero if no error
 *	occurred.
 *
 * Side effects:
 *	Reads input from the input device of the channel.
 *
 *----------------------------------------------------------------------
 */

	/* ARGSUSED */
static int
TcpInputProc(
    ClientData instanceData,	/* Socket state. */
    char *buf,			/* Where to store data read. */
    int bufSize,		/* How much space is available in the
				 * buffer? */
    int *errorCodePtr)		/* Where to store error code. */
{
    TcpState *statePtr = (TcpState *) instanceData;
    int bytesRead, state;

    *errorCodePtr = 0;
    state = WaitForConnect(statePtr, errorCodePtr);
    if (state != 0) {
	return -1;
    }
    bytesRead = recv(statePtr->fd, buf, (size_t) bufSize, 0);
    if (bytesRead > -1) {
	return bytesRead;
    }
    if (errno == ECONNRESET) {
	/*
	 * Turn ECONNRESET into a soft EOF condition.
	 */

	return 0;
    }
    *errorCodePtr = errno;
    return -1;
}

/*
 *----------------------------------------------------------------------
 *
 * TcpOutputProc --
 *
 *	This function is invoked by the generic IO level to write output to a
 *	TCP socket based channel.
 *
 *	NOTE: We cannot share code with FilePipeOutputProc because here we
 *	must use send, not write, to get reliable error reporting.
 *
 * Results:
 *	The number of bytes written is returned. An output argument is set to
 *	a POSIX error code if an error occurred, or zero.
 *
 * Side effects:
 *	Writes output on the output device of the channel.
 *
 *----------------------------------------------------------------------
 */

static int
TcpOutputProc(
    ClientData instanceData,	/* Socket state. */
    const char *buf,		/* The data buffer. */
    int toWrite,		/* How many bytes to write? */
    int *errorCodePtr)		/* Where to store error code. */
{
    TcpState *statePtr = (TcpState *) instanceData;
    int written;
    int state;				/* Of waiting for connection. */

    *errorCodePtr = 0;
    state = WaitForConnect(statePtr, errorCodePtr);
    if (state != 0) {
	return -1;
    }
    written = send(statePtr->fd, buf, (size_t) toWrite, 0);
    if (written > -1) {
	return written;
    }
    *errorCodePtr = errno;
    return -1;
}

/*
 *----------------------------------------------------------------------
 *
 * TcpCloseProc --
 *
 *	This function is invoked by the generic IO level to perform
 *	channel-type-specific cleanup when a TCP socket based channel is
 *	closed.
 *
 * Results:
 *	0 if successful, the value of errno if failed.
 *
 * Side effects:
 *	Closes the socket of the channel.
 *
 *----------------------------------------------------------------------
 */

	/* ARGSUSED */
static int
TcpCloseProc(
    ClientData instanceData,	/* The socket to close. */
    Tcl_Interp *interp)		/* For error reporting - unused. */
{
    TcpState *statePtr = (TcpState *) instanceData;
    int errorCode = 0;

    /*
     * Delete a file handler that may be active for this socket if this is a
     * server socket - the file handler was created automatically by Tcl as
     * part of the mechanism to accept new client connections. Channel
     * handlers are already deleted in the generic IO channel closing code
     * that called this function, so we do not have to delete them here.
     */

    Tcl_DeleteFileHandler(statePtr->fd);

    if (close(statePtr->fd) < 0) {
	errorCode = errno;
    }
    ckfree((char *) statePtr);

    return errorCode;
}

/*
 *----------------------------------------------------------------------
 *
 * TcpGetOptionProc --
 *
 *	Computes an option value for a TCP socket based channel, or a list of
 *	all options and their values.
 *
 *	Note: This code is based on code contributed by John Haxby.
 *
 * Results:
 *	A standard Tcl result. The value of the specified option or a list of
 *	all options and their values is returned in the supplied DString. Sets
 *	Error message if needed.
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */

static int
TcpGetOptionProc(
    ClientData instanceData,	/* Socket state. */
    Tcl_Interp *interp,		/* For error reporting - can be NULL. */
    const char *optionName,	/* Name of the option to retrieve the value
				 * for, or NULL to get all options and their
				 * values. */
    Tcl_DString *dsPtr)		/* Where to store the computed value;
				 * initialized by caller. */
{
    TcpState *statePtr = (TcpState *) instanceData;
    struct sockaddr_in sockname;
    struct sockaddr_in peername;
    struct hostent *hostEntPtr;
    socklen_t size = sizeof(struct sockaddr_in);
    size_t len = 0;
    char buf[TCL_INTEGER_SPACE];

    if (optionName != NULL) {
	len = strlen(optionName);
    }

    if ((len > 1) && (optionName[1] == 'e') &&
	    (strncmp(optionName, "-error", len) == 0)) {
	socklen_t optlen = sizeof(int);
	int err, ret;

	ret = getsockopt(statePtr->fd, SOL_SOCKET, SO_ERROR,
		(char *)&err, &optlen);
	if (ret < 0) {
	    err = errno;
	}
	if (err != 0) {
	    Tcl_DStringAppend(dsPtr, Tcl_ErrnoMsg(err), -1);
	}
	return TCL_OK;
    }

    if ((len == 0) ||
	    ((len > 1) && (optionName[1] == 'p') &&
		    (strncmp(optionName, "-peername", len) == 0))) {
	if (getpeername(statePtr->fd, (struct sockaddr *) &peername,
		&size) >= 0) {
	    if (len == 0) {
		Tcl_DStringAppendElement(dsPtr, "-peername");
		Tcl_DStringStartSublist(dsPtr);
	    }
	    Tcl_DStringAppendElement(dsPtr, inet_ntoa(peername.sin_addr));
	    hostEntPtr = TclpGetHostByAddr(			/* INTL: Native. */
		    (char *) &peername.sin_addr,
		    sizeof(peername.sin_addr), AF_INET);
	    if (hostEntPtr != NULL) {
		Tcl_DString ds;

		Tcl_ExternalToUtfDString(NULL, hostEntPtr->h_name, -1, &ds);
		Tcl_DStringAppendElement(dsPtr, Tcl_DStringValue(&ds));
		Tcl_DStringFree(&ds);
	    } else {
		Tcl_DStringAppendElement(dsPtr, inet_ntoa(peername.sin_addr));
	    }
	    TclFormatInt(buf, ntohs(peername.sin_port));
	    Tcl_DStringAppendElement(dsPtr, buf);
	    if (len == 0) {
		Tcl_DStringEndSublist(dsPtr);
	    } else {
		return TCL_OK;
	    }
	} else {
	    /*
	     * getpeername failed - but if we were asked for all the options
	     * (len==0), don't flag an error at that point because it could be
	     * an fconfigure request on a server socket (which have no peer).
	     * Same must be done on win&mac.
	     */

	    if (len) {
		if (interp) {
		    Tcl_AppendResult(interp, "can't get peername: ",
			    Tcl_PosixError(interp), NULL);
		}
		return TCL_ERROR;
	    }
	}
    }

    if ((len == 0) ||
	    ((len > 1) && (optionName[1] == 's') &&
	    (strncmp(optionName, "-sockname", len) == 0))) {
	if (getsockname(statePtr->fd, (struct sockaddr *) &sockname,
		&size) >= 0) {
	    if (len == 0) {
		Tcl_DStringAppendElement(dsPtr, "-sockname");
		Tcl_DStringStartSublist(dsPtr);
	    }
	    Tcl_DStringAppendElement(dsPtr, inet_ntoa(sockname.sin_addr));
	    hostEntPtr = TclpGetHostByAddr(			/* INTL: Native. */
		    (char *) &sockname.sin_addr,
		    sizeof(sockname.sin_addr), AF_INET);
	    if (hostEntPtr != NULL) {
		Tcl_DString ds;

		Tcl_ExternalToUtfDString(NULL, hostEntPtr->h_name, -1, &ds);
		Tcl_DStringAppendElement(dsPtr, Tcl_DStringValue(&ds));
		Tcl_DStringFree(&ds);
	    } else {
		Tcl_DStringAppendElement(dsPtr, inet_ntoa(sockname.sin_addr));
	    }
	    TclFormatInt(buf, ntohs(sockname.sin_port));
	    Tcl_DStringAppendElement(dsPtr, buf);
	    if (len == 0) {
		Tcl_DStringEndSublist(dsPtr);
	    } else {
		return TCL_OK;
	    }
	} else {
	    if (interp) {
		Tcl_AppendResult(interp, "can't get sockname: ",
			Tcl_PosixError(interp), NULL);
	    }
	    return TCL_ERROR;
	}
    }

    if (len > 0) {
	return Tcl_BadChannelOption(interp, optionName, "peername sockname");
    }

    return TCL_OK;
}

/*
 *----------------------------------------------------------------------
 *
 * TcpWatchProc --
 *
 *	Initialize the notifier to watch the fd from this channel.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	Sets up the notifier so that a future event on the channel will be
 *	seen by Tcl.
 *
 *----------------------------------------------------------------------
 */

static void
TcpWatchProc(
    ClientData instanceData,	/* The socket state. */
    int mask)			/* Events of interest; an OR-ed combination of
				 * TCL_READABLE, TCL_WRITABLE and
				 * TCL_EXCEPTION. */
{
    TcpState *statePtr = (TcpState *) instanceData;

    /*
     * Make sure we don't mess with server sockets since they will never be
     * readable or writable at the Tcl level. This keeps Tcl scripts from
     * interfering with the -accept behavior.
     */

    if (!statePtr->acceptProc) {
	if (mask) {
	    Tcl_CreateFileHandler(statePtr->fd, mask,
		    (Tcl_FileProc *) Tcl_NotifyChannel,
		    (ClientData) statePtr->channel);
	} else {
	    Tcl_DeleteFileHandler(statePtr->fd);
	}
    }
}

/*
 *----------------------------------------------------------------------
 *
 * TcpGetHandleProc --
 *
 *	Called from Tcl_GetChannelHandle to retrieve OS handles from inside a
 *	TCP socket based channel.
 *
 * Results:
 *	Returns TCL_OK with the fd in handlePtr, or TCL_ERROR if there is no
 *	handle for the specified direction.
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */

	/* ARGSUSED */
static int
TcpGetHandleProc(
    ClientData instanceData,	/* The socket state. */
    int direction,		/* Not used. */
    ClientData *handlePtr)	/* Where to store the handle. */
{
    TcpState *statePtr = (TcpState *) instanceData;

    *handlePtr = (ClientData) INT2PTR(statePtr->fd);
    return TCL_OK;
}

/*
 *----------------------------------------------------------------------
 *
 * CreateSocket --
 *
 *	This function opens a new socket in client or server mode and
 *	initializes the TcpState structure.
 *
 * Results:
 *	Returns a new TcpState, or NULL with an error in the interp's result,
 *	if interp is not NULL.
 *
 * Side effects:
 *	Opens a socket.
 *
 *----------------------------------------------------------------------
 */

static TcpState *
CreateSocket(
    Tcl_Interp *interp,		/* For error reporting; can be NULL. */
    int port,			/* Port number to open. */
    const char *host,		/* Name of host on which to open port. NULL
				 * implies INADDR_ANY */
    int server,			/* 1 if socket should be a server socket, else
				 * 0 for a client socket. */
    const char *myaddr,		/* Optional client-side address */
    int myport,			/* Optional client-side port */
    int async)			/* If nonzero and creating a client socket,
				 * attempt to do an async connect. Otherwise
				 * do a synchronous connect or bind. */
{
    int status, sock, asyncConnect, curState, origState;
    struct sockaddr_in sockaddr;	/* socket address */
    struct sockaddr_in mysockaddr;	/* Socket address for client */
    TcpState *statePtr;
    const char *errorMsg = NULL;

    sock = -1;
    origState = 0;
    if (!CreateSocketAddress(&sockaddr, host, port, 0, &errorMsg)) {
	goto addressError;
    }
    if ((myaddr != NULL || myport != 0) &&
	    !CreateSocketAddress(&mysockaddr, myaddr, myport, 1, &errorMsg)) {
	goto addressError;
    }

    sock = socket(AF_INET, SOCK_STREAM, 0);
    if (sock < 0) {
	goto addressError;
    }

    /*
     * Set the close-on-exec flag so that the socket will not get inherited by
     * child processes.
     */

    fcntl(sock, F_SETFD, FD_CLOEXEC);

    /*
     * Set kernel space buffering
     */

    TclSockMinimumBuffers(sock, SOCKET_BUFSIZE);

    asyncConnect = 0;
    status = 0;
    if (server) {
	/*
	 * Set up to reuse server addresses automatically and bind to the
	 * specified port.
	 */

	status = 1;
	(void) setsockopt(sock, SOL_SOCKET, SO_REUSEADDR, (char *) &status,
		sizeof(status));
	status = bind(sock, (struct sockaddr *) &sockaddr,
		sizeof(struct sockaddr));
	if (status != -1) {
	    status = listen(sock, SOMAXCONN);
	}
    } else {
	if (myaddr != NULL || myport != 0) {
	    curState = 1;
	    (void) setsockopt(sock, SOL_SOCKET, SO_REUSEADDR,
		    (char *) &curState, sizeof(curState));
	    status = bind(sock, (struct sockaddr *) &mysockaddr,
		    sizeof(struct sockaddr));
	    if (status < 0) {
		goto bindError;
	    }
	}

	/*
	 * Attempt to connect. The connect may fail at present with an
	 * EINPROGRESS but at a later time it will complete. The caller will
	 * set up a file handler on the socket if she is interested in being
	 * informed when the connect completes.
	 */

	if (async) {
	    status = TclUnixSetBlockingMode(sock, TCL_MODE_NONBLOCKING);
	} else {
	    status = 0;
	}
	if (status > -1) {
	    status = connect(sock, (struct sockaddr *) &sockaddr,
		    sizeof(sockaddr));
	    if (status < 0) {
		if (errno == EINPROGRESS) {
		    asyncConnect = 1;
		    status = 0;
		}
	    } else {
		/*
		 * Here we are if the connect succeeds. In case of an
		 * asynchronous connect we have to reset the channel to
		 * blocking mode. This appears to happen not very often, but
		 * e.g. on a HP 9000/800 under HP-UX B.11.00 we enter this
		 * stage. [Bug: 4388]
		 */

		if (async) {
		    status = TclUnixSetBlockingMode(sock, TCL_MODE_BLOCKING);
		}
	    }
	}
    }

  bindError:
    if (status < 0) {
	if (interp != NULL) {
	    Tcl_AppendResult(interp, "couldn't open socket: ",
		    Tcl_PosixError(interp), NULL);
	}
	if (sock != -1) {
	    close(sock);
	}
	return NULL;
    }

    /*
     * Allocate a new TcpState for this socket.
     */

    statePtr = (TcpState *) ckalloc((unsigned) sizeof(TcpState));
    statePtr->flags = 0;
    if (asyncConnect) {
	statePtr->flags = TCP_ASYNC_CONNECT;
    }
    statePtr->fd = sock;

    return statePtr;

  addressError:
    if (sock != -1) {
	close(sock);
    }
    if (interp != NULL) {
	Tcl_AppendResult(interp, "couldn't open socket: ",
		Tcl_PosixError(interp), NULL);
	if (errorMsg != NULL) {
	    Tcl_AppendResult(interp, " (", errorMsg, ")", NULL);
	}
    }
    return NULL;
}

/*
 *----------------------------------------------------------------------
 *
 * CreateSocketAddress --
 *
 *	This function initializes a sockaddr structure for a host and port.
 *
 * Results:
 *	1 if the host was valid, 0 if the host could not be converted to an IP
 *	address.
 *
 * Side effects:
 *	Fills in the *sockaddrPtr structure.
 *
 *----------------------------------------------------------------------
 */

static int
CreateSocketAddress(
    struct sockaddr_in *sockaddrPtr,	/* Socket address */
    const char *host,			/* Host. NULL implies INADDR_ANY */
    int port,				/* Port number */
    int willBind,			/* Is this an address to bind() to or
					 * to connect() to? */
    const char **errorMsgPtr)		/* Place to store the error message
					 * detail, if available. */
{
#ifdef HAVE_GETADDRINFO
    struct addrinfo hints, *resPtr = NULL;
    char *native;
    Tcl_DString ds;
    int result;

    if (host == NULL) {
	sockaddrPtr->sin_family = AF_INET;
	sockaddrPtr->sin_addr.s_addr = INADDR_ANY;
    addPort:
	sockaddrPtr->sin_port = htons((unsigned short) (port & 0xFFFF));
	return 1;
    }

    (void) memset(&hints, 0, sizeof(struct addrinfo));
    hints.ai_family = AF_INET;
    hints.ai_socktype = SOCK_STREAM;
    if (willBind) {
	hints.ai_flags |= AI_PASSIVE;
    }

    /*
     * Note that getaddrinfo() *is* thread-safe. If a platform doesn't get
     * that right, it shouldn't use this part of the code.
     */

    native = Tcl_UtfToExternalDString(NULL, host, -1, &ds);
    result = getaddrinfo(native, NULL, &hints, &resPtr);
    Tcl_DStringFree(&ds);
    if (result == 0) {
	memcpy(sockaddrPtr, resPtr->ai_addr, sizeof(struct sockaddr_in));
	freeaddrinfo(resPtr);
	goto addPort;
    }

    /*
     * Ought to use gai_strerror() here...
     */

    switch (result) {
    case EAI_NONAME:
    case EAI_SERVICE:
#if defined(EAI_ADDRFAMILY) && EAI_ADDRFAMILY != EAI_NONAME
    case EAI_ADDRFAMILY:
#endif
#if defined(EAI_NODATA) && EAI_NODATA != EAI_NONAME
    case EAI_NODATA:
#endif
	*errorMsgPtr = gai_strerror(result);
	errno = EHOSTUNREACH;
	return 0;
    case EAI_SYSTEM:
	return 0;
    default:
	*errorMsgPtr = gai_strerror(result);
	errno = ENXIO;
	return 0;
    }
#else /* !HAVE_GETADDRINFO */
    struct in_addr addr;		/* For 64/32 bit madness */

    (void) memset(sockaddrPtr, '\0', sizeof(struct sockaddr_in));
    sockaddrPtr->sin_family = AF_INET;
    sockaddrPtr->sin_port = htons((unsigned short) (port & 0xFFFF));
    if (host == NULL) {
	addr.s_addr = INADDR_ANY;
    } else {
	struct hostent *hostent;	/* Host database entry */
	Tcl_DString ds;
	const char *native;

	if (host == NULL) {
	    native = NULL;
	} else {
	    native = Tcl_UtfToExternalDString(NULL, host, -1, &ds);
	}
	addr.s_addr = inet_addr(native);		/* INTL: Native. */

	/*
	 * This is 0xFFFFFFFF to ensure that it compares as a 32bit -1 on
	 * either 32 or 64 bits systems.
	 */

	if (addr.s_addr == 0xFFFFFFFF) {
	    hostent = TclpGetHostByName(native);	/* INTL: Native. */
	    if (hostent != NULL) {
		memcpy(&addr, hostent->h_addr_list[0],
			(size_t) hostent->h_length);
	    } else {
#ifdef	EHOSTUNREACH
		errno = EHOSTUNREACH;
#else /* !EHOSTUNREACH */
#ifdef ENXIO
		errno = ENXIO;
#endif /* ENXIO */
#endif /* EHOSTUNREACH */
		if (native != NULL) {
		    Tcl_DStringFree(&ds);
		}
		return 0;	/* Error. */
	    }
	}
	if (native != NULL) {
	    Tcl_DStringFree(&ds);
	}
    }

    /*
     * NOTE: On 64 bit machines the assignment below is rumored to not do the
     * right thing. Please report errors related to this if you observe
     * incorrect behavior on 64 bit machines such as DEC Alphas. Should we
     * modify this code to do an explicit memcpy?
     */

    sockaddrPtr->sin_addr.s_addr = addr.s_addr;
    return 1;			/* Success. */
#endif /* HAVE_GETADDRINFO */
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_OpenTcpClient --
 *
 *	Opens a TCP client socket and creates a channel around it.
 *
 * Results:
 *	The channel or NULL if failed. An error message is returned in the
 *	interpreter on failure.
 *
 * Side effects:
 *	Opens a client socket and creates a new channel.
 *
 *----------------------------------------------------------------------
 */

Tcl_Channel
Tcl_OpenTcpClient(
    Tcl_Interp *interp,		/* For error reporting; can be NULL. */
    int port,			/* Port number to open. */
    const char *host,		/* Host on which to open port. */
    const char *myaddr,		/* Client-side address */
    int myport,			/* Client-side port */
    int async)			/* If nonzero, attempt to do an asynchronous
				 * connect. Otherwise we do a blocking
				 * connect. */
{
    TcpState *statePtr;
    char channelName[16 + TCL_INTEGER_SPACE];

    /*
     * Create a new client socket and wrap it in a channel.
     */

    statePtr = CreateSocket(interp, port, host, 0, myaddr, myport, async);
    if (statePtr == NULL) {
	return NULL;
    }

    statePtr->acceptProc = NULL;
    statePtr->acceptProcData = NULL;

    sprintf(channelName, "sock%d", statePtr->fd);

    statePtr->channel = Tcl_CreateChannel(&tcpChannelType, channelName,
	    (ClientData) statePtr, (TCL_READABLE | TCL_WRITABLE));
    if (Tcl_SetChannelOption(interp, statePtr->channel, "-translation",
	    "auto crlf") == TCL_ERROR) {
	Tcl_Close(NULL, statePtr->channel);
	return NULL;
    }
    return statePtr->channel;
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_MakeTcpClientChannel --
 *
 *	Creates a Tcl_Channel from an existing client TCP socket.
 *
 * Results:
 *	The Tcl_Channel wrapped around the preexisting TCP socket.
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */

Tcl_Channel
Tcl_MakeTcpClientChannel(
    ClientData sock)		/* The socket to wrap up into a channel. */
{
    return MakeTcpClientChannelMode(sock, (TCL_READABLE | TCL_WRITABLE));
}

/*
 *----------------------------------------------------------------------
 *
 * MakeTcpClientChannelMode --
 *
 *	Creates a Tcl_Channel from an existing client TCP socket
 *	with given mode.
 *
 * Results:
 *	The Tcl_Channel wrapped around the preexisting TCP socket.
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */

static Tcl_Channel
MakeTcpClientChannelMode(
    ClientData sock,		/* The socket to wrap up into a channel. */
    int mode)			/* ORed combination of TCL_READABLE and
				 * TCL_WRITABLE to indicate file mode. */
{
    TcpState *statePtr;
    char channelName[16 + TCL_INTEGER_SPACE];

    statePtr = (TcpState *) ckalloc((unsigned) sizeof(TcpState));
    statePtr->fd = PTR2INT(sock);
    statePtr->flags = 0;
    statePtr->acceptProc = NULL;
    statePtr->acceptProcData = NULL;

    sprintf(channelName, "sock%d", statePtr->fd);

    statePtr->channel = Tcl_CreateChannel(&tcpChannelType, channelName,
	    (ClientData) statePtr, mode);
    if (Tcl_SetChannelOption(NULL, statePtr->channel, "-translation",
	    "auto crlf") == TCL_ERROR) {
	Tcl_Close(NULL, statePtr->channel);
	return NULL;
    }
    return statePtr->channel;
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_OpenTcpServer --
 *
 *	Opens a TCP server socket and creates a channel around it.
 *
 * Results:
 *	The channel or NULL if failed. If an error occurred, an error message
 *	is left in the interp's result if interp is not NULL.
 *
 * Side effects:
 *	Opens a server socket and creates a new channel.
 *
 *----------------------------------------------------------------------
 */

Tcl_Channel
Tcl_OpenTcpServer(
    Tcl_Interp *interp,		/* For error reporting - may be NULL. */
    int port,			/* Port number to open. */
    const char *myHost,		/* Name of local host. */
    Tcl_TcpAcceptProc *acceptProc,
				/* Callback for accepting connections from new
				 * clients. */
    ClientData acceptProcData)	/* Data for the callback. */
{
    TcpState *statePtr;
    char channelName[16 + TCL_INTEGER_SPACE];

    /*
     * Create a new client socket and wrap it in a channel.
     */

    statePtr = CreateSocket(interp, port, myHost, 1, NULL, 0, 0);
    if (statePtr == NULL) {
	return NULL;
    }

    statePtr->acceptProc = acceptProc;
    statePtr->acceptProcData = acceptProcData;

    /*
     * Set up the callback mechanism for accepting connections from new
     * clients.
     */

    Tcl_CreateFileHandler(statePtr->fd, TCL_READABLE, TcpAccept,
	    (ClientData) statePtr);
    sprintf(channelName, "sock%d", statePtr->fd);
    statePtr->channel = Tcl_CreateChannel(&tcpChannelType, channelName,
	    (ClientData) statePtr, 0);
    return statePtr->channel;
}

/*
 *----------------------------------------------------------------------
 *
 * TcpAccept --
 *	Accept a TCP socket connection.	 This is called by the event loop.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	Creates a new connection socket. Calls the registered callback for the
 *	connection acceptance mechanism.
 *
 *----------------------------------------------------------------------
 */

	/* ARGSUSED */
static void
TcpAccept(
    ClientData data,		/* Callback token. */
    int mask)			/* Not used. */
{
    TcpState *sockState;	/* Client data of server socket. */
    int newsock;		/* The new client socket */
    TcpState *newSockState;	/* State for new socket. */
    struct sockaddr_in addr;	/* The remote address */
    socklen_t len;		/* For accept interface */
    char channelName[16 + TCL_INTEGER_SPACE];

    sockState = (TcpState *) data;

    len = sizeof(struct sockaddr_in);
    newsock = accept(sockState->fd, (struct sockaddr *) &addr, &len);
    if (newsock < 0) {
	return;
    }

    /*
     * Set close-on-exec flag to prevent the newly accepted socket from being
     * inherited by child processes.
     */

    (void) fcntl(newsock, F_SETFD, FD_CLOEXEC);

    newSockState = (TcpState *) ckalloc((unsigned) sizeof(TcpState));

    newSockState->flags = 0;
    newSockState->fd = newsock;
    newSockState->acceptProc = NULL;
    newSockState->acceptProcData = NULL;

    sprintf(channelName, "sock%d", newsock);
    newSockState->channel = Tcl_CreateChannel(&tcpChannelType, channelName,
	    (ClientData) newSockState, (TCL_READABLE | TCL_WRITABLE));

    Tcl_SetChannelOption(NULL, newSockState->channel, "-translation",
	    "auto crlf");

    if (sockState->acceptProc != NULL) {
	(*sockState->acceptProc)(sockState->acceptProcData,
		newSockState->channel, inet_ntoa(addr.sin_addr),
		ntohs(addr.sin_port));
    }
}

/*
 *----------------------------------------------------------------------
 *
 * TclpGetDefaultStdChannel --
 *
 *	Creates channels for standard input, standard output or standard error
 *	output if they do not already exist.
 *
 * Results:
 *	Returns the specified default standard channel, or NULL.
 *
 * Side effects:
 *	May cause the creation of a standard channel and the underlying file.
 *
 *----------------------------------------------------------------------
 */

Tcl_Channel
TclpGetDefaultStdChannel(
    int type)			/* One of TCL_STDIN, TCL_STDOUT, TCL_STDERR. */
{
    Tcl_Channel channel = NULL;
    int fd = 0;			/* Initializations needed to prevent */
    int mode = 0;		/* compiler warning (used before set). */
    char *bufMode = NULL;

    /*
     * Some #def's to make the code a little clearer!
     */

#define ZERO_OFFSET	((Tcl_SeekOffset) 0)
#define ERROR_OFFSET	((Tcl_SeekOffset) -1)

    switch (type) {
    case TCL_STDIN:
	if ((TclOSseek(0, ZERO_OFFSET, SEEK_CUR) == ERROR_OFFSET)
		&& (errno == EBADF)) {
	    return NULL;
	}
	fd = 0;
	mode = TCL_READABLE;
	bufMode = "line";
	break;
    case TCL_STDOUT:
	if ((TclOSseek(1, ZERO_OFFSET, SEEK_CUR) == ERROR_OFFSET)
		&& (errno == EBADF)) {
	    return NULL;
	}
	fd = 1;
	mode = TCL_WRITABLE;
	bufMode = "line";
	break;
    case TCL_STDERR:
	if ((TclOSseek(2, ZERO_OFFSET, SEEK_CUR) == ERROR_OFFSET)
		&& (errno == EBADF)) {
	    return NULL;
	}
	fd = 2;
	mode = TCL_WRITABLE;
	bufMode = "none";
	break;
    default:
	Tcl_Panic("TclGetDefaultStdChannel: Unexpected channel type");
	break;
    }

#undef ZERO_OFFSET
#undef ERROR_OFFSET

    channel = Tcl_MakeFileChannel((ClientData) INT2PTR(fd), mode);
    if (channel == NULL) {
	return NULL;
    }

    /*
     * Set up the normal channel options for stdio handles.
     */

    if (Tcl_GetChannelType(channel) == &fileChannelType) {
	Tcl_SetChannelOption(NULL, channel, "-translation", "auto");
    } else {
	Tcl_SetChannelOption(NULL, channel, "-translation", "auto crlf");
    }
    Tcl_SetChannelOption(NULL, channel, "-buffering", bufMode);
    return channel;
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_GetOpenFile --
 *
 *	Given a name of a channel registered in the given interpreter, returns
 *	a FILE * for it.
 *
 * Results:
 *	A standard Tcl result. If the channel is registered in the given
 *	interpreter and it is managed by the "file" channel driver, and it is
 *	open for the requested mode, then the output parameter filePtr is set
 *	to a FILE * for the underlying file. On error, the filePtr is not set,
 *	TCL_ERROR is returned and an error message is left in the interp's
 *	result.
 *
 * Side effects:
 *	May invoke fdopen to create the FILE * for the requested file.
 *
 *----------------------------------------------------------------------
 */

int
Tcl_GetOpenFile(
    Tcl_Interp *interp,		/* Interpreter in which to find file. */
    const char *chanID,		/* String that identifies file. */
    int forWriting,		/* 1 means the file is going to be used for
				 * writing, 0 means for reading. */
    int checkUsage,		/* 1 means verify that the file was opened in
				 * a mode that allows the access specified by
				 * "forWriting". Ignored, we always check that
				 * the channel is open for the requested
				 * mode. */
    ClientData *filePtr)	/* Store pointer to FILE structure here. */
{
    Tcl_Channel chan;
    int chanMode, fd;
    const Tcl_ChannelType *chanTypePtr;
    ClientData data;
    FILE *f;

    chan = Tcl_GetChannel(interp, chanID, &chanMode);
    if (chan == (Tcl_Channel) NULL) {
	return TCL_ERROR;
    }
    if ((forWriting) && ((chanMode & TCL_WRITABLE) == 0)) {
	Tcl_AppendResult(interp, "\"", chanID, "\" wasn't opened for writing",
		NULL);
	return TCL_ERROR;
    } else if ((!forWriting) && ((chanMode & TCL_READABLE) == 0)) {
	Tcl_AppendResult(interp, "\"", chanID, "\" wasn't opened for reading",
		NULL);
	return TCL_ERROR;
    }

    /*
     * We allow creating a FILE * out of file based, pipe based and socket
     * based channels. We currently do not allow any other channel types,
     * because it is likely that stdio will not know what to do with them.
     */

    chanTypePtr = Tcl_GetChannelType(chan);
    if ((chanTypePtr == &fileChannelType)
#ifdef SUPPORTS_TTY
	    || (chanTypePtr == &ttyChannelType)
#endif /* SUPPORTS_TTY */
	    || (chanTypePtr == &tcpChannelType)
	    || (strcmp(chanTypePtr->typeName, "pipe") == 0)) {
	if (Tcl_GetChannelHandle(chan,
		(forWriting ? TCL_WRITABLE : TCL_READABLE),
		(ClientData*) &data) == TCL_OK) {
	    fd = PTR2INT(data);

	    /*
	     * The call to fdopen below is probably dangerous, since it will
	     * truncate an existing file if the file is being opened for
	     * writing....
	     */

	    f = fdopen(fd, (forWriting ? "w" : "r"));
	    if (f == NULL) {
		Tcl_AppendResult(interp, "cannot get a FILE * for \"", chanID,
			"\"", NULL);
		return TCL_ERROR;
	    }
	    *filePtr = (ClientData) f;
	    return TCL_OK;
	}
    }

    Tcl_AppendResult(interp, "\"", chanID,
	    "\" cannot be used to get a FILE *", NULL);
    return TCL_ERROR;
}

/*
 *----------------------------------------------------------------------
 *
 * TclUnixWaitForFile --
 *
 *	This function waits synchronously for a file to become readable or
 *	writable, with an optional timeout.
 *
 * Results:
 *	The return value is an OR'ed combination of TCL_READABLE,
 *	TCL_WRITABLE, and TCL_EXCEPTION, indicating the conditions that are
 *	present on file at the time of the return. This function will not
 *	return until either "timeout" milliseconds have elapsed or at least
 *	one of the conditions given by mask has occurred for file (a return
 *	value of 0 means that a timeout occurred). No normal events will be
 *	serviced during the execution of this function.
 *
 * Side effects:
 *	Time passes.
 *
 *----------------------------------------------------------------------
 */

int
TclUnixWaitForFile(
    int fd,			/* Handle for file on which to wait. */
    int mask,			/* What to wait for: OR'ed combination of
				 * TCL_READABLE, TCL_WRITABLE, and
				 * TCL_EXCEPTION. */
    int timeout)		/* Maximum amount of time to wait for one of
				 * the conditions in mask to occur, in
				 * milliseconds. A value of 0 means don't wait
				 * at all, and a value of -1 means wait
				 * forever. */
{
    Tcl_Time abortTime = {0, 0}, now; /* silence gcc 4 warning */
    struct timeval blockTime, *timeoutPtr;
    int index, numFound, result = 0;
    fd_mask bit;
    fd_mask readyMasks[3*MASK_SIZE];
    fd_mask *maskp[3];		/* This array reflects the readable/writable
				 * conditions that were found to exist by the
				 * last call to select. */

    /*
     * If there is a non-zero finite timeout, compute the time when we give
     * up.
     */

    if (timeout > 0) {
	Tcl_GetTime(&now);
	abortTime.sec = now.sec + timeout/1000;
	abortTime.usec = now.usec + (timeout%1000)*1000;
	if (abortTime.usec >= 1000000) {
	    abortTime.usec -= 1000000;
	    abortTime.sec += 1;
	}
	timeoutPtr = &blockTime;
    } else if (timeout == 0) {
	timeoutPtr = &blockTime;
	blockTime.tv_sec = 0;
	blockTime.tv_usec = 0;
    } else {
	timeoutPtr = NULL;
    }

    /*
     * Initialize the ready masks and compute the mask offsets.
     */

    if (fd >= FD_SETSIZE) {
	Tcl_Panic("TclWaitForFile can't handle file id %d", fd);
	/* must never get here, or readyMasks overrun will occur below */
    }
    memset(readyMasks, 0, 3*MASK_SIZE*sizeof(fd_mask));
    index = fd / (NBBY*sizeof(fd_mask));
    bit = ((fd_mask)1) << (fd % (NBBY*sizeof(fd_mask)));

    /*
     * Loop in a mini-event loop of our own, waiting for either the file to
     * become ready or a timeout to occur.
     */

    while (1) {
	if (timeout > 0) {
	    blockTime.tv_sec = abortTime.sec - now.sec;
	    blockTime.tv_usec = abortTime.usec - now.usec;
	    if (blockTime.tv_usec < 0) {
		blockTime.tv_sec -= 1;
		blockTime.tv_usec += 1000000;
	    }
	    if (blockTime.tv_sec < 0) {
		blockTime.tv_sec = 0;
		blockTime.tv_usec = 0;
	    }
	}

	/*
	 * Set the appropriate bit in the ready masks for the fd.
	 */

	if (mask & TCL_READABLE) {
	    readyMasks[index] |= bit;
	}
	if (mask & TCL_WRITABLE) {
	    (readyMasks+MASK_SIZE)[index] |= bit;
	}
	if (mask & TCL_EXCEPTION) {
	    (readyMasks+2*(MASK_SIZE))[index] |= bit;
	}

	/*
	 * Wait for the event or a timeout.
	 */

	/*
	 * This is needed to satisfy GCC 3.3's strict aliasing rules.
	 */

	maskp[0] = &readyMasks[0];
	maskp[1] = &readyMasks[MASK_SIZE];
	maskp[2] = &readyMasks[2*MASK_SIZE];
	numFound = select(fd+1, (SELECT_MASK *) maskp[0],
		(SELECT_MASK *) maskp[1],
		(SELECT_MASK *) maskp[2], timeoutPtr);
	if (numFound == 1) {
	    if (readyMasks[index] & bit) {
		SET_BITS(result, TCL_READABLE);
	    }
	    if ((readyMasks+MASK_SIZE)[index] & bit) {
		SET_BITS(result, TCL_WRITABLE);
	    }
	    if ((readyMasks+2*(MASK_SIZE))[index] & bit) {
		SET_BITS(result, TCL_EXCEPTION);
	    }
	    result &= mask;
	    if (result) {
		break;
	    }
	}
	if (timeout == 0) {
	    break;
	}
	if (timeout < 0) {
	    continue;
	}

	/*
	 * The select returned early, so we need to recompute the timeout.
	 */

	Tcl_GetTime(&now);
	if ((abortTime.sec < now.sec)
		|| (abortTime.sec==now.sec && abortTime.usec<=now.usec)) {
	    break;
	}
    }
    return result;
}

/*
 *----------------------------------------------------------------------
 *
 * FileTruncateProc --
 *
 *	Truncates a file to a given length.
 *
 * Results:
 *	0 if the operation succeeded, and -1 if it failed (in which case
 *	*errorCodePtr will be set to errno).
 *
 * Side effects:
 *	The underlying file is potentially truncated. This can have a wide
 *	variety of side effects, including moving file pointers that point at
 *	places later in the file than the truncate point.
 *
 *----------------------------------------------------------------------
 */

static int
FileTruncateProc(
    ClientData instanceData,
    Tcl_WideInt length)
{
    FileState *fsPtr = (FileState *) instanceData;
    int result;

#ifdef HAVE_TYPE_OFF64_T
    /*
     * We assume this goes with the type for now...
     */

    result = ftruncate64(fsPtr->fd, (off64_t) length);
#else
    result = ftruncate(fsPtr->fd, (off_t) length);
#endif
    if (result) {
	return errno;
    }
    return 0;
}

/*
 * Local Variables:
 * mode: c
 * c-basic-offset: 4
 * fill-column: 78
 * End:
 */
