/*
 * tclMacOSXNotify.c --
 *
 *	This file contains the implementation of a merged CFRunLoop/select()
 *	based notifier, which is the lowest-level part of the Tcl event loop.
 *	This file works together with generic/tclNotify.c.
 *
 * Copyright (c) 1995-1997 Sun Microsystems, Inc.
 * Copyright 2001, Apple Computer, Inc.
 * Copyright (c) 2005-2008 Daniel A. Steffen <das@users.sourceforge.net>
 *
 * See the file "license.terms" for information on usage and redistribution of
 * this file, and for a DISCLAIMER OF ALL WARRANTIES.
 *
 * RCS: @(#) $Id: tclMacOSXNotify.c,v 1.18 2008/03/11 22:24:17 das Exp $
 */

#include "tclInt.h"
#ifdef HAVE_COREFOUNDATION	/* Traditional unix select-based notifier is
				 * in tclUnixNotfy.c */
#include <CoreFoundation/CoreFoundation.h>
#include <pthread.h>

extern TclStubs tclStubs;
extern Tcl_NotifierProcs tclOriginalNotifier;

/*
 * This structure is used to keep track of the notifier info for a registered
 * file.
 */

typedef struct FileHandler {
    int fd;
    int mask;			/* Mask of desired events: TCL_READABLE,
				 * etc. */
    int readyMask;		/* Mask of events that have been seen since
				 * the last time file handlers were invoked
				 * for this file. */
    Tcl_FileProc *proc;		/* Function to call, in the style of
				 * Tcl_CreateFileHandler. */
    ClientData clientData;	/* Argument to pass to proc. */
    struct FileHandler *nextPtr;/* Next in list of all files we care about. */
} FileHandler;

/*
 * The following structure is what is added to the Tcl event queue when file
 * handlers are ready to fire.
 */

typedef struct FileHandlerEvent {
    Tcl_Event header;		/* Information that is standard for all
				 * events. */
    int fd;			/* File descriptor that is ready. Used to find
				 * the FileHandler structure for the file
				 * (can't point directly to the FileHandler
				 * structure because it could go away while
				 * the event is queued). */
} FileHandlerEvent;

/*
 * The following structure contains a set of select() masks to track readable,
 * writable, and exceptional conditions.
 */

typedef struct SelectMasks {
    fd_set readable;
    fd_set writable;
    fd_set exceptional;
} SelectMasks;

/*
 * The following static structure contains the state information for the
 * select based implementation of the Tcl notifier. One of these structures is
 * created for each thread that is using the notifier.
 */

typedef struct ThreadSpecificData {
    FileHandler *firstFileHandlerPtr;
				/* Pointer to head of file handler list. */
    SelectMasks checkMasks;	/* This structure is used to build up the
				 * masks to be used in the next call to
				 * select. Bits are set in response to calls
				 * to Tcl_CreateFileHandler. */
    SelectMasks readyMasks;	/* This array reflects the readable/writable
				 * conditions that were found to exist by the
				 * last call to select. */
    int numFdBits;		/* Number of valid bits in checkMasks (one
				 * more than highest fd for which
				 * Tcl_WatchFile has been called). */
    int onList;			/* True if it is in this list */
    unsigned int pollState;	/* pollState is used to implement a polling
				 * handshake between each thread and the
				 * notifier thread. Bits defined below. */
    struct ThreadSpecificData *nextPtr, *prevPtr;
				/* All threads that are currently waiting on
				 * an event have their ThreadSpecificData
				 * structure on a doubly-linked listed formed
				 * from these pointers. You must hold the
				 * notifierLock before accessing these
				 * fields. */
    CFRunLoopSourceRef runLoopSource;
				/* Any other thread alerts a notifier that an
				 * event is ready to be processed by signaling
				 * this CFRunLoopSource. */
    CFRunLoopRef runLoop;	/* This thread's CFRunLoop, needs to be woken
				 * up whenever the runLoopSource is
				 * signaled. */
    int eventReady;		/* True if an event is ready to be
				 * processed. */
} ThreadSpecificData;

static Tcl_ThreadDataKey dataKey;

/*
 * The following static indicates the number of threads that have initialized
 * notifiers.
 *
 * You must hold the notifierInitLock before accessing this variable.
 */

static int notifierCount = 0;

/*
 * The following variable points to the head of a doubly-linked list of
 * ThreadSpecificData structures for all threads that are currently waiting on
 * an event.
 *
 * You must hold the notifierLock before accessing this list.
 */

static ThreadSpecificData *waitingListPtr = NULL;

/*
 * The notifier thread spends all its time in select() waiting for a file
 * descriptor associated with one of the threads on the waitingListPtr list to
 * do something interesting. But if the contents of the waitingListPtr list
 * ever changes, we need to wake up and restart the select() system call. You
 * can wake up the notifier thread by writing a single byte to the file
 * descriptor defined below. This file descriptor is the input-end of a pipe
 * and the notifier thread is listening for data on the output-end of the same
 * pipe. Hence writing to this file descriptor will cause the select() system
 * call to return and wake up the notifier thread.
 *
 * You must hold the notifierLock lock before writing to the pipe.
 */

static int triggerPipe = -1;
static int receivePipe = -1; /* Output end of triggerPipe */

/*
 * We use the Darwin-native spinlock API rather than pthread mutexes for
 * notifier locking: this radically simplifies the implementation and lowers
 * overhead. Note that these are not pure spinlocks, they employ various
 * strategies to back off and relinquish the processor, making them immune to
 * most priority-inversion livelocks (c.f. 'man 3 OSSpinLockLock' and Darwin
 * sources: xnu/osfmk/{ppc,i386}/commpage/spinlocks.s).
 */

#if defined(HAVE_LIBKERN_OSATOMIC_H) && defined(HAVE_OSSPINLOCKLOCK)
/*
 * Use OSSpinLock API where available (Tiger or later).
 */

#include <libkern/OSAtomic.h>

#if defined(HAVE_WEAK_IMPORT) && MAC_OS_X_VERSION_MIN_REQUIRED < 1040
/*
 * Support for weakly importing spinlock API.
 */
#define WEAK_IMPORT_SPINLOCKLOCK
#if MAC_OS_X_VERSION_MAX_ALLOWED >= 1050
#define VOLATILE volatile
#else
#define VOLATILE
#endif
#ifndef bool
#define bool int
#endif
extern void OSSpinLockLock(VOLATILE OSSpinLock *lock) WEAK_IMPORT_ATTRIBUTE;
extern void OSSpinLockUnlock(VOLATILE OSSpinLock *lock) WEAK_IMPORT_ATTRIBUTE;
extern bool OSSpinLockTry(VOLATILE OSSpinLock *lock) WEAK_IMPORT_ATTRIBUTE;
extern void _spin_lock(VOLATILE OSSpinLock *lock) WEAK_IMPORT_ATTRIBUTE;
extern void _spin_unlock(VOLATILE OSSpinLock *lock) WEAK_IMPORT_ATTRIBUTE;
extern bool _spin_lock_try(VOLATILE OSSpinLock *lock) WEAK_IMPORT_ATTRIBUTE;
static void (* lockLock)(VOLATILE OSSpinLock *lock) = NULL;
static void (* lockUnlock)(VOLATILE OSSpinLock *lock) = NULL;
static bool (* lockTry)(VOLATILE OSSpinLock *lock) = NULL;
#undef VOLATILE
static pthread_once_t spinLockLockInitControl = PTHREAD_ONCE_INIT;
static void SpinLockLockInit(void) {
    lockLock   = OSSpinLockLock   != NULL ? OSSpinLockLock   : _spin_lock;
    lockUnlock = OSSpinLockUnlock != NULL ? OSSpinLockUnlock : _spin_unlock;
    lockTry    = OSSpinLockTry    != NULL ? OSSpinLockTry    : _spin_lock_try;
    if (lockLock == NULL || lockUnlock == NULL) {
	Tcl_Panic("SpinLockLockInit: no spinlock API available");
    }
}
#define SpinLockLock(p) 	lockLock(p)
#define SpinLockUnlock(p)	lockUnlock(p)
#define SpinLockTry(p)  	lockTry(p)
#else
#define SpinLockLock(p) 	OSSpinLockLock(p)
#define SpinLockUnlock(p)	OSSpinLockUnlock(p)
#define SpinLockTry(p)  	OSSpinLockTry(p)
#endif /* HAVE_WEAK_IMPORT */
#define SPINLOCK_INIT   	OS_SPINLOCK_INIT

#else
/*
 * Otherwise, use commpage spinlock SPI directly.
 */

typedef uint32_t OSSpinLock;
extern void _spin_lock(OSSpinLock *lock);
extern void _spin_unlock(OSSpinLock *lock);
extern int  _spin_lock_try(OSSpinLock *lock);
#define SpinLockLock(p) 	_spin_lock(p)
#define SpinLockUnlock(p)	_spin_unlock(p)
#define SpinLockTry(p)  	_spin_lock_try(p)
#define SPINLOCK_INIT   	0

#endif /* HAVE_LIBKERN_OSATOMIC_H && HAVE_OSSPINLOCKLOCK */

/*
 * These spinlocks lock access to the global notifier state.
 */

static OSSpinLock notifierInitLock = SPINLOCK_INIT;
static OSSpinLock notifierLock     = SPINLOCK_INIT;

/*
 * Macros abstracting notifier locking/unlocking
 */

#define LOCK_NOTIFIER_INIT	SpinLockLock(&notifierInitLock)
#define UNLOCK_NOTIFIER_INIT	SpinLockUnlock(&notifierInitLock)
#define LOCK_NOTIFIER		SpinLockLock(&notifierLock)
#define UNLOCK_NOTIFIER		SpinLockUnlock(&notifierLock)

#ifdef TCL_MAC_DEBUG_NOTIFIER
/*
 * Debug version of SpinLockLock that logs the time spent waiting for the lock
 */

#define SpinLockLockDbg(p)	if(!SpinLockTry(p)) { \
				    Tcl_WideInt s = TclpGetWideClicks(), e; \
				    SpinLockLock(p); e = TclpGetWideClicks(); \
				    fprintf(notifierLog, "tclMacOSXNotify.c:" \
				    "%4d: thread %10p waited on %s for " \
				    "%8llu ns\n", __LINE__, pthread_self(), \
				    #p, TclpWideClicksToNanoseconds(e-s)); \
				    fflush(notifierLog); \
				}
#undef LOCK_NOTIFIER_INIT
#define LOCK_NOTIFIER_INIT	SpinLockLockDbg(&notifierInitLock)
#undef LOCK_NOTIFIER
#define LOCK_NOTIFIER		SpinLockLockDbg(&notifierLock)
static FILE *notifierLog = stderr;
#ifndef NOTIFIER_LOG
#define NOTIFIER_LOG "/tmp/tclMacOSXNotify.log"
#endif
#define OPEN_NOTIFIER_LOG	if (notifierLog == stderr) { \
				    notifierLog = fopen(NOTIFIER_LOG, "a"); \
				}
#define CLOSE_NOTIFIER_LOG	if (notifierLog != stderr) { \
				    fclose(notifierLog); \
				    notifierLog = stderr; \
				}
#endif /* TCL_MAC_DEBUG_NOTIFIER */

/*
 * The pollState bits
 *	POLL_WANT is set by each thread before it waits on its condition
 *		variable. It is checked by the notifier before it does select.
 *	POLL_DONE is set by the notifier if it goes into select after seeing
 *		POLL_WANT. The idea is to ensure it tries a select with the
 *		same bits the initial thread had set.
 */

#define POLL_WANT	0x1
#define POLL_DONE	0x2

/*
 * This is the thread ID of the notifier thread that does select.
 */

static pthread_t notifierThread;

/*
 * Custom run loop mode containing only the run loop source for the
 * notifier thread.
 */

#ifndef TCL_EVENTS_ONLY_RUN_LOOP_MODE
#define TCL_EVENTS_ONLY_RUN_LOOP_MODE "com.tcltk.tclEventsOnlyRunLoopMode"
#endif
#ifdef __CONSTANT_CFSTRINGS__
#define tclEventsOnlyRunLoopMode CFSTR(TCL_EVENTS_ONLY_RUN_LOOP_MODE)
#else
static CFStringRef tclEventsOnlyRunLoopMode = NULL;
#endif

/*
 * Static routines defined in this file.
 */

static void	NotifierThreadProc(ClientData clientData)
	__attribute__ ((__noreturn__));
static int	FileHandlerEventProc(Tcl_Event *evPtr, int flags);

#ifdef HAVE_PTHREAD_ATFORK
static int	atForkInit = 0;
static void	AtForkPrepare(void);
static void	AtForkParent(void);
static void	AtForkChild(void);
#if defined(HAVE_WEAK_IMPORT) && MAC_OS_X_VERSION_MIN_REQUIRED < 1040
/* Support for weakly importing pthread_atfork. */
#define WEAK_IMPORT_PTHREAD_ATFORK
extern int pthread_atfork(void (*prepare)(void), void (*parent)(void),
                          void (*child)(void)) WEAK_IMPORT_ATTRIBUTE;
#endif /* HAVE_WEAK_IMPORT */
/*
 * On Darwin 9 and later, it is not possible to call CoreFoundation after
 * a fork.
 */
#if !defined(MAC_OS_X_VERSION_MIN_REQUIRED) || \
	MAC_OS_X_VERSION_MIN_REQUIRED < 1050
MODULE_SCOPE long tclMacOSXDarwinRelease;
#define noCFafterFork (tclMacOSXDarwinRelease >= 9)
#else /* MAC_OS_X_VERSION_MIN_REQUIRED */
#define noCFafterFork 1
#endif /* MAC_OS_X_VERSION_MIN_REQUIRED */
#endif /* HAVE_PTHREAD_ATFORK */

/*
 *----------------------------------------------------------------------
 *
 * Tcl_InitNotifier --
 *
 *	Initializes the platform specific notifier state.
 *
 * Results:
 *	Returns a handle to the notifier state for this thread.
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */

ClientData
Tcl_InitNotifier(void)
{
    ThreadSpecificData *tsdPtr = TCL_TSD_INIT(&dataKey);

    tsdPtr->eventReady = 0;

#ifdef WEAK_IMPORT_SPINLOCKLOCK
    /*
     * Initialize support for weakly imported spinlock API.
     */
    if (pthread_once(&spinLockLockInitControl, SpinLockLockInit)) {
	Tcl_Panic("Tcl_InitNotifier: pthread_once failed");
    }
#endif

#ifndef __CONSTANT_CFSTRINGS__
    if (!tclEventsOnlyRunLoopMode) {
	tclEventsOnlyRunLoopMode = CFSTR(TCL_EVENTS_ONLY_RUN_LOOP_MODE);
    }
#endif

    /*
     * Initialize CFRunLoopSource and add it to CFRunLoop of this thread.
     */

    if (!tsdPtr->runLoop) {
	CFRunLoopRef runLoop = CFRunLoopGetCurrent();
	CFRunLoopSourceRef runLoopSource;
	CFRunLoopSourceContext runLoopSourceContext;

	bzero(&runLoopSourceContext, sizeof(CFRunLoopSourceContext));
	runLoopSourceContext.info = tsdPtr;
	runLoopSource = CFRunLoopSourceCreate(NULL, 0, &runLoopSourceContext);
	if (!runLoopSource) {
	    Tcl_Panic("Tcl_InitNotifier: could not create CFRunLoopSource");
	}
	CFRunLoopAddSource(runLoop, runLoopSource, kCFRunLoopCommonModes);
	CFRunLoopAddSource(runLoop, runLoopSource, tclEventsOnlyRunLoopMode);
	tsdPtr->runLoopSource = runLoopSource;
	tsdPtr->runLoop = runLoop;
    }

    LOCK_NOTIFIER_INIT;
#ifdef HAVE_PTHREAD_ATFORK
    /*
     * Install pthread_atfork handlers to reinitialize the notifier in the
     * child of a fork.
     */

    if (
#ifdef WEAK_IMPORT_PTHREAD_ATFORK
	    pthread_atfork != NULL &&
#endif
	    !atForkInit) {
	int result = pthread_atfork(AtForkPrepare, AtForkParent, AtForkChild);
	if (result) {
	    Tcl_Panic("Tcl_InitNotifier: pthread_atfork failed");
	}
	atForkInit = 1;
    }
#endif
    if (notifierCount == 0) {
	int fds[2], status;

	/*
	 * Initialize trigger pipe.
	 */

	if (pipe(fds) != 0) {
	    Tcl_Panic("Tcl_InitNotifier: could not create trigger pipe");
	}

	status = fcntl(fds[0], F_GETFL);
	status |= O_NONBLOCK;
	if (fcntl(fds[0], F_SETFL, status) < 0) {
	    Tcl_Panic("Tcl_InitNotifier: could not make receive pipe non blocking");
	}
	status = fcntl(fds[1], F_GETFL);
	status |= O_NONBLOCK;
	if (fcntl(fds[1], F_SETFL, status) < 0) {
	    Tcl_Panic("Tcl_InitNotifier: could not make trigger pipe non blocking");
	}

	receivePipe = fds[0];
	triggerPipe = fds[1];

	/*
	 * Create notifier thread lazily in Tcl_WaitForEvent() to avoid
	 * interfering with fork() followed immediately by execve()
	 * (cannot execve() when more than one thread is present).
	 */

	notifierThread = 0;
#ifdef TCL_MAC_DEBUG_NOTIFIER
	OPEN_NOTIFIER_LOG;
#endif
    }
    notifierCount++;
    UNLOCK_NOTIFIER_INIT;

    return (ClientData) tsdPtr;
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_FinalizeNotifier --
 *
 *	This function is called to cleanup the notifier state before a thread
 *	is terminated.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	May terminate the background notifier thread if this is the last
 *	notifier instance.
 *
 *----------------------------------------------------------------------
 */

void
Tcl_FinalizeNotifier(
    ClientData clientData)		/* Not used. */
{
    ThreadSpecificData *tsdPtr = TCL_TSD_INIT(&dataKey);

    LOCK_NOTIFIER_INIT;
    notifierCount--;

    /*
     * If this is the last thread to use the notifier, close the notifier pipe
     * and wait for the background thread to terminate.
     */

    if (notifierCount == 0) {
	int result;

	if (triggerPipe < 0) {
	    Tcl_Panic("Tcl_FinalizeNotifier: notifier pipe not initialized");
	}

	/*
	 * Send "q" message to the notifier thread so that it will terminate.
	 * The notifier will return from its call to select() and notice that
	 * a "q" message has arrived, it will then close its side of the pipe
	 * and terminate its thread. Note the we can not just close the pipe
	 * and check for EOF in the notifier thread because if a background
	 * child process was created with exec, select() would not register
	 * the EOF on the pipe until the child processes had terminated. [Bug:
	 * 4139] [Bug: 1222872]
	 */

	write(triggerPipe, "q", 1);
	close(triggerPipe);

	if (notifierThread) {
	    result = pthread_join(notifierThread, NULL);
	    if (result) {
		Tcl_Panic("Tcl_FinalizeNotifier: unable to join notifier thread");
	    }
	    notifierThread = 0;
	}

	close(receivePipe);
	triggerPipe = -1;
#ifdef TCL_MAC_DEBUG_NOTIFIER
	CLOSE_NOTIFIER_LOG;
#endif
    }
    UNLOCK_NOTIFIER_INIT;

    LOCK_NOTIFIER;		/* for concurrency with Tcl_AlertNotifier */
    if (tsdPtr->runLoop) {
	tsdPtr->runLoop = NULL;

	/*
	 * Remove runLoopSource from all CFRunLoops and release it.
	 */

	CFRunLoopSourceInvalidate(tsdPtr->runLoopSource);
	CFRelease(tsdPtr->runLoopSource);
	tsdPtr->runLoopSource = NULL;
    }
    UNLOCK_NOTIFIER;
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_AlertNotifier --
 *
 *	Wake up the specified notifier from any thread. This routine is called
 *	by the platform independent notifier code whenever the Tcl_ThreadAlert
 *	routine is called. This routine is guaranteed not to be called on a
 *	given notifier after Tcl_FinalizeNotifier is called for that notifier.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	Signals the notifier condition variable for the specified notifier.
 *
 *----------------------------------------------------------------------
 */

void
Tcl_AlertNotifier(
    ClientData clientData)
{
    ThreadSpecificData *tsdPtr = (ThreadSpecificData *) clientData;

    LOCK_NOTIFIER;
    if (tsdPtr->runLoop) {
	tsdPtr->eventReady = 1;
	CFRunLoopSourceSignal(tsdPtr->runLoopSource);
	CFRunLoopWakeUp(tsdPtr->runLoop);
    }
    UNLOCK_NOTIFIER;
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_SetTimer --
 *
 *	This function sets the current notifier timer value. This interface is
 *	not implemented in this notifier because we are always running inside
 *	of Tcl_DoOneEvent.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */

void
Tcl_SetTimer(
    Tcl_Time *timePtr)		/* Timeout value, may be NULL. */
{
    /*
     * The interval timer doesn't do anything in this implementation, because
     * the only event loop is via Tcl_DoOneEvent, which passes timeout values
     * to Tcl_WaitForEvent.
     */

    if (tclStubs.tcl_SetTimer != tclOriginalNotifier.setTimerProc) {
	tclStubs.tcl_SetTimer(timePtr);
    }
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_ServiceModeHook --
 *
 *	This function is invoked whenever the service mode changes.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */

void
Tcl_ServiceModeHook(
    int mode)			/* Either TCL_SERVICE_ALL, or
				 * TCL_SERVICE_NONE. */
{
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_CreateFileHandler --
 *
 *	This function registers a file handler with the select notifier.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	Creates a new file handler structure.
 *
 *----------------------------------------------------------------------
 */

void
Tcl_CreateFileHandler(
    int fd,			/* Handle of stream to watch. */
    int mask,			/* OR'ed combination of TCL_READABLE,
				 * TCL_WRITABLE, and TCL_EXCEPTION: indicates
				 * conditions under which proc should be
				 * called. */
    Tcl_FileProc *proc,		/* Function to call for each selected
				 * event. */
    ClientData clientData)	/* Arbitrary data to pass to proc. */
{
    ThreadSpecificData *tsdPtr = TCL_TSD_INIT(&dataKey);
    FileHandler *filePtr;

    if (tclStubs.tcl_CreateFileHandler !=
	    tclOriginalNotifier.createFileHandlerProc) {
	tclStubs.tcl_CreateFileHandler(fd, mask, proc, clientData);
	return;
    }

    for (filePtr = tsdPtr->firstFileHandlerPtr; filePtr != NULL;
	    filePtr = filePtr->nextPtr) {
	if (filePtr->fd == fd) {
	    break;
	}
    }
    if (filePtr == NULL) {
	filePtr = (FileHandler*) ckalloc(sizeof(FileHandler));
	filePtr->fd = fd;
	filePtr->readyMask = 0;
	filePtr->nextPtr = tsdPtr->firstFileHandlerPtr;
	tsdPtr->firstFileHandlerPtr = filePtr;
    }
    filePtr->proc = proc;
    filePtr->clientData = clientData;
    filePtr->mask = mask;

    /*
     * Update the check masks for this file.
     */

    if (mask & TCL_READABLE) {
	FD_SET(fd, &(tsdPtr->checkMasks.readable));
    } else {
	FD_CLR(fd, &(tsdPtr->checkMasks.readable));
    }
    if (mask & TCL_WRITABLE) {
	FD_SET(fd, &(tsdPtr->checkMasks.writable));
    } else {
	FD_CLR(fd, &(tsdPtr->checkMasks.writable));
    }
    if (mask & TCL_EXCEPTION) {
	FD_SET(fd, &(tsdPtr->checkMasks.exceptional));
    } else {
	FD_CLR(fd, &(tsdPtr->checkMasks.exceptional));
    }
    if (tsdPtr->numFdBits <= fd) {
	tsdPtr->numFdBits = fd+1;
    }
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_DeleteFileHandler --
 *
 *	Cancel a previously-arranged callback arrangement for a file.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	If a callback was previously registered on file, remove it.
 *
 *----------------------------------------------------------------------
 */

void
Tcl_DeleteFileHandler(
    int fd)			/* Stream id for which to remove callback
				 * function. */
{
    FileHandler *filePtr, *prevPtr;
    int i;
    ThreadSpecificData *tsdPtr = TCL_TSD_INIT(&dataKey);

    if (tclStubs.tcl_DeleteFileHandler !=
	    tclOriginalNotifier.deleteFileHandlerProc) {
	tclStubs.tcl_DeleteFileHandler(fd);
	return;
    }

    /*
     * Find the entry for the given file (and return if there isn't one).
     */

    for (prevPtr = NULL, filePtr = tsdPtr->firstFileHandlerPtr; ;
	 prevPtr = filePtr, filePtr = filePtr->nextPtr) {
	if (filePtr == NULL) {
	    return;
	}
	if (filePtr->fd == fd) {
	    break;
	}
    }

    /*
     * Update the check masks for this file.
     */

    if (filePtr->mask & TCL_READABLE) {
	FD_CLR(fd, &(tsdPtr->checkMasks.readable));
    }
    if (filePtr->mask & TCL_WRITABLE) {
	FD_CLR(fd, &(tsdPtr->checkMasks.writable));
    }
    if (filePtr->mask & TCL_EXCEPTION) {
	FD_CLR(fd, &(tsdPtr->checkMasks.exceptional));
    }

    /*
     * Find current max fd.
     */

    if (fd+1 == tsdPtr->numFdBits) {
	tsdPtr->numFdBits = 0;
	for (i = fd-1; i >= 0; i--) {
	    if (FD_ISSET(i, &(tsdPtr->checkMasks.readable))
		    || FD_ISSET(i, &(tsdPtr->checkMasks.writable))
		    || FD_ISSET(i, &(tsdPtr->checkMasks.exceptional))) {
		tsdPtr->numFdBits = i+1;
		break;
	    }
	}
    }

    /*
     * Clean up information in the callback record.
     */

    if (prevPtr == NULL) {
	tsdPtr->firstFileHandlerPtr = filePtr->nextPtr;
    } else {
	prevPtr->nextPtr = filePtr->nextPtr;
    }
    ckfree((char *) filePtr);
}

/*
 *----------------------------------------------------------------------
 *
 * FileHandlerEventProc --
 *
 *	This function is called by Tcl_ServiceEvent when a file event reaches
 *	the front of the event queue. This function is responsible for
 *	actually handling the event by invoking the callback for the file
 *	handler.
 *
 * Results:
 *	Returns 1 if the event was handled, meaning it should be removed from
 *	the queue. Returns 0 if the event was not handled, meaning it should
 *	stay on the queue. The only time the event isn't handled is if the
 *	TCL_FILE_EVENTS flag bit isn't set.
 *
 * Side effects:
 *	Whatever the file handler's callback function does.
 *
 *----------------------------------------------------------------------
 */

static int
FileHandlerEventProc(
    Tcl_Event *evPtr,		/* Event to service. */
    int flags)			/* Flags that indicate what events to handle,
				 * such as TCL_FILE_EVENTS. */
{
    int mask;
    FileHandler *filePtr;
    FileHandlerEvent *fileEvPtr = (FileHandlerEvent *) evPtr;
    ThreadSpecificData *tsdPtr;

    if (!(flags & TCL_FILE_EVENTS)) {
	return 0;
    }

    /*
     * Search through the file handlers to find the one whose handle matches
     * the event. We do this rather than keeping a pointer to the file handler
     * directly in the event, so that the handler can be deleted while the
     * event is queued without leaving a dangling pointer.
     */

    tsdPtr = TCL_TSD_INIT(&dataKey);
    for (filePtr = tsdPtr->firstFileHandlerPtr; filePtr != NULL;
	    filePtr = filePtr->nextPtr) {
	if (filePtr->fd != fileEvPtr->fd) {
	    continue;
	}

	/*
	 * The code is tricky for two reasons:
	 * 1. The file handler's desired events could have changed since the
	 *    time when the event was queued, so AND the ready mask with the
	 *    desired mask.
	 * 2. The file could have been closed and re-opened since the time
	 *    when the event was queued. This is why the ready mask is stored
	 *    in the file handler rather than the queued event: it will be
	 *    zeroed when a new file handler is created for the newly opened
	 *    file.
	 */

	mask = filePtr->readyMask & filePtr->mask;
	filePtr->readyMask = 0;
	if (mask != 0) {
	    (*filePtr->proc)(filePtr->clientData, mask);
	}
	break;
    }
    return 1;
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_WaitForEvent --
 *
 *	This function is called by Tcl_DoOneEvent to wait for new events on
 *	the message queue. If the block time is 0, then Tcl_WaitForEvent just
 *	polls without blocking.
 *
 * Results:
 *	Returns -1 if the select would block forever, otherwise returns 0.
 *
 * Side effects:
 *	Queues file events that are detected by the select.
 *
 *----------------------------------------------------------------------
 */

int
Tcl_WaitForEvent(
    Tcl_Time *timePtr)		/* Maximum block time, or NULL. */
{
    FileHandler *filePtr;
    FileHandlerEvent *fileEvPtr;
    int mask;
    Tcl_Time myTime;
    int waitForFiles;
    Tcl_Time *myTimePtr;
    ThreadSpecificData *tsdPtr = TCL_TSD_INIT(&dataKey);

    if (tclStubs.tcl_WaitForEvent != tclOriginalNotifier.waitForEventProc) {
	return tclStubs.tcl_WaitForEvent(timePtr);
    }

    if (timePtr != NULL) {
	/*
	 * TIP #233 (Virtualized Time). Is virtual time in effect? And do we
	 * actually have something to scale? If yes to both then we call the
	 * handler to do this scaling.
	 */

	myTime.sec  = timePtr->sec;
	myTime.usec = timePtr->usec;

	if (myTime.sec != 0 || myTime.usec != 0) {
	    (*tclScaleTimeProcPtr) (&myTime, tclTimeClientData);
	}

	myTimePtr = &myTime;
    } else {
	myTimePtr = NULL;
    }

    /*
     * Start notifier thread if necessary.
     */

    LOCK_NOTIFIER_INIT;
    if (!notifierCount) {
        Tcl_Panic("Tcl_WaitForEvent: notifier not initialized");
    }
    if (!notifierThread) {
	int result;
	pthread_attr_t attr;

	pthread_attr_init(&attr);
	pthread_attr_setscope(&attr, PTHREAD_SCOPE_SYSTEM);
	pthread_attr_setdetachstate(&attr, PTHREAD_CREATE_JOINABLE);
	pthread_attr_setstacksize(&attr, 60 * 1024);
	result = pthread_create(&notifierThread, &attr,
		(void * (*)(void *))NotifierThreadProc, NULL);
	pthread_attr_destroy(&attr);
	if (result || !notifierThread) {
	    Tcl_Panic("Tcl_WaitForEvent: unable to start notifier thread");
	}
    }
    UNLOCK_NOTIFIER_INIT;

    /*
     * Place this thread on the list of interested threads, signal the
     * notifier thread, and wait for a response or a timeout.
     */

    LOCK_NOTIFIER;
    if (!tsdPtr->runLoop) {
        Tcl_Panic("Tcl_WaitForEvent: CFRunLoop not initialized");
    }
    waitForFiles = (tsdPtr->numFdBits > 0);
    if (myTimePtr != NULL && myTimePtr->sec == 0 && myTimePtr->usec == 0) {
	/*
	 * Cannot emulate a polling select with a polling condition variable.
	 * Instead, pretend to wait for files and tell the notifier thread
	 * what we are doing. The notifier thread makes sure it goes through
	 * select with its select mask in the same state as ours currently is.
	 * We block until that happens.
	 */

	waitForFiles = 1;
	tsdPtr->pollState = POLL_WANT;
	myTimePtr = NULL;
    } else {
	tsdPtr->pollState = 0;
    }

    if (waitForFiles) {
	/*
	 * Add the ThreadSpecificData structure of this thread to the list of
	 * ThreadSpecificData structures of all threads that are waiting on
	 * file events.
	 */

	tsdPtr->nextPtr = waitingListPtr;
	if (waitingListPtr) {
	    waitingListPtr->prevPtr = tsdPtr;
	}
	tsdPtr->prevPtr = 0;
	waitingListPtr = tsdPtr;
	tsdPtr->onList = 1;

	write(triggerPipe, "", 1);
    }

    FD_ZERO(&(tsdPtr->readyMasks.readable));
    FD_ZERO(&(tsdPtr->readyMasks.writable));
    FD_ZERO(&(tsdPtr->readyMasks.exceptional));

    if (!tsdPtr->eventReady) {
	CFTimeInterval waitTime;
	CFStringRef runLoopMode;

	if (myTimePtr == NULL) {
	    waitTime = 1.0e10; /* Wait forever, as per CFRunLoop.c */
	} else {
	    waitTime = myTimePtr->sec + 1.0e-6 * myTimePtr->usec;
	}
	/*
	 * If the run loop is already running (e.g. if Tcl_WaitForEvent was
	 * called recursively), re-run it in a custom run loop mode containing
	 * only the source for the notifier thread, otherwise wakeups from other
	 * sources added to the common run loop modes might get lost.
	 */
	if ((runLoopMode = CFRunLoopCopyCurrentMode(tsdPtr->runLoop))) {
	    CFRelease(runLoopMode);
	    runLoopMode = tclEventsOnlyRunLoopMode;
	} else {
	    runLoopMode = kCFRunLoopDefaultMode;
	}
	UNLOCK_NOTIFIER;
	CFRunLoopRunInMode(runLoopMode, waitTime, TRUE);
	LOCK_NOTIFIER;
    }
    tsdPtr->eventReady = 0;

    if (waitForFiles && tsdPtr->onList) {
	/*
	 * Remove the ThreadSpecificData structure of this thread from the
	 * waiting list. Alert the notifier thread to recompute its select
	 * masks - skipping this caused a hang when trying to close a pipe
	 * which the notifier thread was still doing a select on.
	 */

	if (tsdPtr->prevPtr) {
	    tsdPtr->prevPtr->nextPtr = tsdPtr->nextPtr;
	} else {
	    waitingListPtr = tsdPtr->nextPtr;
	}
	if (tsdPtr->nextPtr) {
	    tsdPtr->nextPtr->prevPtr = tsdPtr->prevPtr;
	}
	tsdPtr->nextPtr = tsdPtr->prevPtr = NULL;
	tsdPtr->onList = 0;
	write(triggerPipe, "", 1);
    }

    /*
     * Queue all detected file events before returning.
     */

    for (filePtr = tsdPtr->firstFileHandlerPtr; (filePtr != NULL);
	    filePtr = filePtr->nextPtr) {

	mask = 0;
	if (FD_ISSET(filePtr->fd, &(tsdPtr->readyMasks.readable))) {
	    mask |= TCL_READABLE;
	}
	if (FD_ISSET(filePtr->fd, &(tsdPtr->readyMasks.writable))) {
	    mask |= TCL_WRITABLE;
	}
	if (FD_ISSET(filePtr->fd, &(tsdPtr->readyMasks.exceptional))) {
	    mask |= TCL_EXCEPTION;
	}

	if (!mask) {
	    continue;
	}

	/*
	 * Don't bother to queue an event if the mask was previously non-zero
	 * since an event must still be on the queue.
	 */

	if (filePtr->readyMask == 0) {
	    fileEvPtr = (FileHandlerEvent *) ckalloc(sizeof(FileHandlerEvent));
	    fileEvPtr->header.proc = FileHandlerEventProc;
	    fileEvPtr->fd = filePtr->fd;
	    Tcl_QueueEvent((Tcl_Event *) fileEvPtr, TCL_QUEUE_TAIL);
	}
	filePtr->readyMask = mask;
    }
    UNLOCK_NOTIFIER;
    return 0;
}

/*
 *----------------------------------------------------------------------
 *
 * NotifierThreadProc --
 *
 *	This routine is the initial (and only) function executed by the
 *	special notifier thread. Its job is to wait for file descriptors to
 *	become readable or writable or to have an exception condition and then
 *	to notify other threads who are interested in this information by
 *	signalling a condition variable. Other threads can signal this
 *	notifier thread of a change in their interests by writing a single
 *	byte to a special pipe that the notifier thread is monitoring.
 *
 * Result:
 *	None. Once started, this routine never exits. It dies with the overall
 *	process.
 *
 * Side effects:
 *	The trigger pipe used to signal the notifier thread is created when
 *	the notifier thread first starts.
 *
 *----------------------------------------------------------------------
 */

static void
NotifierThreadProc(
    ClientData clientData)	/* Not used. */
{
    ThreadSpecificData *tsdPtr;
    fd_set readableMask;
    fd_set writableMask;
    fd_set exceptionalMask;
    int i, numFdBits = 0;
    long found;
    struct timeval poll = {0., 0.}, *timePtr;
    char buf[2];

    /*
     * Look for file events and report them to interested threads.
     */

    while (1) {
	FD_ZERO(&readableMask);
	FD_ZERO(&writableMask);
	FD_ZERO(&exceptionalMask);

	/*
	 * Compute the logical OR of the select masks from all the waiting
	 * notifiers.
	 */

	LOCK_NOTIFIER;
	timePtr = NULL;
	for (tsdPtr = waitingListPtr; tsdPtr; tsdPtr = tsdPtr->nextPtr) {
	    for (i = tsdPtr->numFdBits-1; i >= 0; --i) {
		if (FD_ISSET(i, &(tsdPtr->checkMasks.readable))) {
		    FD_SET(i, &readableMask);
		}
		if (FD_ISSET(i, &(tsdPtr->checkMasks.writable))) {
		    FD_SET(i, &writableMask);
		}
		if (FD_ISSET(i, &(tsdPtr->checkMasks.exceptional))) {
		    FD_SET(i, &exceptionalMask);
		}
	    }
	    if (tsdPtr->numFdBits > numFdBits) {
		numFdBits = tsdPtr->numFdBits;
	    }
	    if (tsdPtr->pollState & POLL_WANT) {
		/*
		 * Here we make sure we go through select() with the same mask
		 * bits that were present when the thread tried to poll.
		 */

		tsdPtr->pollState |= POLL_DONE;
		timePtr = &poll;
	    }
	}
	UNLOCK_NOTIFIER;

	/*
	 * Set up the select mask to include the receive pipe.
	 */

	if (receivePipe >= numFdBits) {
	    numFdBits = receivePipe + 1;
	}
	FD_SET(receivePipe, &readableMask);

	if (select(numFdBits, &readableMask, &writableMask, &exceptionalMask,
		timePtr) == -1) {
	    /*
	     * Try again immediately on an error.
	     */

	    continue;
	}

	/*
	 * Alert any threads that are waiting on a ready file descriptor.
	 */

	LOCK_NOTIFIER;
	for (tsdPtr = waitingListPtr; tsdPtr; tsdPtr = tsdPtr->nextPtr) {
	    found = 0;

	    for (i = tsdPtr->numFdBits-1; i >= 0; --i) {
		if (FD_ISSET(i, &(tsdPtr->checkMasks.readable))
			&& FD_ISSET(i, &readableMask)) {
		    FD_SET(i, &(tsdPtr->readyMasks.readable));
		    found = 1;
		}
		if (FD_ISSET(i, &(tsdPtr->checkMasks.writable))
			&& FD_ISSET(i, &writableMask)) {
		    FD_SET(i, &(tsdPtr->readyMasks.writable));
		    found = 1;
		}
		if (FD_ISSET(i, &(tsdPtr->checkMasks.exceptional))
			&& FD_ISSET(i, &exceptionalMask)) {
		    FD_SET(i, &(tsdPtr->readyMasks.exceptional));
		    found = 1;
		}
	    }

	    if (found || (tsdPtr->pollState & POLL_DONE)) {
		tsdPtr->eventReady = 1;
		if (tsdPtr->onList) {
		    /*
		     * Remove the ThreadSpecificData structure of this thread
		     * from the waiting list. This prevents us from
		     * continuously spining on select until the other threads
		     * runs and services the file event.
		     */

		    if (tsdPtr->prevPtr) {
			tsdPtr->prevPtr->nextPtr = tsdPtr->nextPtr;
		    } else {
			waitingListPtr = tsdPtr->nextPtr;
		    }
		    if (tsdPtr->nextPtr) {
			tsdPtr->nextPtr->prevPtr = tsdPtr->prevPtr;
		    }
		    tsdPtr->nextPtr = tsdPtr->prevPtr = NULL;
		    tsdPtr->onList = 0;
		    tsdPtr->pollState = 0;
		}
		if (tsdPtr->runLoop) {
		    CFRunLoopSourceSignal(tsdPtr->runLoopSource);
		    CFRunLoopWakeUp(tsdPtr->runLoop);
		}
	    }
	}
	UNLOCK_NOTIFIER;

	/*
	 * Consume the next byte from the notifier pipe if the pipe was
	 * readable. Note that there may be multiple bytes pending, but to
	 * avoid a race condition we only read one at a time.
	 */

	if (FD_ISSET(receivePipe, &readableMask)) {
	    i = read(receivePipe, buf, 1);

	    if ((i == 0) || ((i == 1) && (buf[0] == 'q'))) {
		/*
		 * Someone closed the write end of the pipe or sent us a Quit
		 * message [Bug: 4139] and then closed the write end of the
		 * pipe so we need to shut down the notifier thread.
		 */

		break;
	    }
	}
    }
    pthread_exit(0);
}

#ifdef HAVE_PTHREAD_ATFORK
/*
 *----------------------------------------------------------------------
 *
 * AtForkPrepare --
 *
 *	Lock the notifier in preparation for a fork.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */

static void
AtForkPrepare(void)
{
    LOCK_NOTIFIER_INIT;
    LOCK_NOTIFIER;
}

/*
 *----------------------------------------------------------------------
 *
 * AtForkParent --
 *
 *	Unlock the notifier in the parent after a fork.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */

static void
AtForkParent(void)
{
    UNLOCK_NOTIFIER;
    UNLOCK_NOTIFIER_INIT;
}

/*
 *----------------------------------------------------------------------
 *
 * AtForkChild --
 *
 *	Unlock and reinstall the notifier in the child after a fork.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */

static void
AtForkChild(void)
{
    ThreadSpecificData *tsdPtr = TCL_TSD_INIT(&dataKey);

    UNLOCK_NOTIFIER;
    UNLOCK_NOTIFIER_INIT;
    if (tsdPtr->runLoop) {
	tsdPtr->runLoop = NULL;
	if (!noCFafterFork) {
	    CFRunLoopSourceInvalidate(tsdPtr->runLoopSource);
	}
	CFRelease(tsdPtr->runLoopSource);
	tsdPtr->runLoopSource = NULL;
    }
    if (notifierCount > 0) {
	notifierCount = 0;

	/*
	 * Assume that the return value of Tcl_InitNotifier in the child will
	 * be identical to the one stored as clientData in tclNotify.c's
	 * ThreadSpecificData by the parent's TclInitNotifier, so discard the
	 * return value here. This assumption may require the fork() to be
	 * executed in the main thread of the parent, otherwise
	 * Tcl_AlertNotifier may break in the child.
	 */

	if (!noCFafterFork) {
	    Tcl_InitNotifier();
	}
    }
}
#endif /* HAVE_PTHREAD_ATFORK */

#endif /* HAVE_COREFOUNDATION */

/*
 * Local Variables:
 * mode: c
 * c-basic-offset: 4
 * fill-column: 78
 * End:
 */
