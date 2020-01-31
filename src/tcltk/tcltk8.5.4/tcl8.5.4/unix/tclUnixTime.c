/*
 * tclUnixTime.c --
 *
 *	Contains Unix specific versions of Tcl functions that obtain time
 *	values from the operating system.
 *
 * Copyright (c) 1995 Sun Microsystems, Inc.
 *
 * See the file "license.terms" for information on usage and redistribution of
 * this file, and for a DISCLAIMER OF ALL WARRANTIES.
 *
 * RCS: @(#) $Id: tclUnixTime.c,v 1.33.2.1 2008/04/14 17:49:59 kennykb Exp $
 */

#include "tclInt.h"
#include <locale.h>
#if defined(TCL_WIDE_CLICKS) && defined(MAC_OSX_TCL)
#include <mach/mach_time.h>
#endif

#define TM_YEAR_BASE 1900
#define IsLeapYear(x)	(((x)%4 == 0) && ((x)%100 != 0 || (x)%400 == 0))

/*
 * TclpGetDate is coded to return a pointer to a 'struct tm'. For thread
 * safety, this structure must be in thread-specific data. The 'tmKey'
 * variable is the key to this buffer.
 */

static Tcl_ThreadDataKey tmKey;
typedef struct ThreadSpecificData {
    struct tm gmtime_buf;
    struct tm localtime_buf;
} ThreadSpecificData;

/*
 * If we fall back on the thread-unsafe versions of gmtime and localtime, use
 * this mutex to try to protect them.
 */

TCL_DECLARE_MUTEX(tmMutex)

static char *lastTZ = NULL;	/* Holds the last setting of the TZ
				 * environment variable, or an empty string if
				 * the variable was not set. */

/*
 * Static functions declared in this file.
 */

static void		SetTZIfNecessary(void);
static void		CleanupMemory(ClientData clientData);
static void		NativeScaleTime(Tcl_Time *timebuf,
			    ClientData clientData);
static void		NativeGetTime(Tcl_Time *timebuf,
			    ClientData clientData);

/*
 * TIP #233 (Virtualized Time): Data for the time hooks, if any.
 */

Tcl_GetTimeProc *tclGetTimeProcPtr = NativeGetTime;
Tcl_ScaleTimeProc *tclScaleTimeProcPtr = NativeScaleTime;
ClientData tclTimeClientData = NULL;

/*
 *-----------------------------------------------------------------------------
 *
 * TclpGetSeconds --
 *
 *	This procedure returns the number of seconds from the epoch. On most
 *	Unix systems the epoch is Midnight Jan 1, 1970 GMT.
 *
 * Results:
 *	Number of seconds from the epoch.
 *
 * Side effects:
 *	None.
 *
 *-----------------------------------------------------------------------------
 */

unsigned long
TclpGetSeconds(void)
{
    return time(NULL);
}

/*
 *-----------------------------------------------------------------------------
 *
 * TclpGetClicks --
 *
 *	This procedure returns a value that represents the highest resolution
 *	clock available on the system. There are no garantees on what the
 *	resolution will be. In Tcl we will call this value a "click". The
 *	start time is also system dependant.
 *
 * Results:
 *	Number of clicks from some start time.
 *
 * Side effects:
 *	None.
 *
 *-----------------------------------------------------------------------------
 */

unsigned long
TclpGetClicks(void)
{
    unsigned long now;

#ifdef NO_GETTOD
    if (tclGetTimeProcPtr != NativeGetTime) {
	Tcl_Time time;

	(*tclGetTimeProcPtr) (&time, tclTimeClientData);
	now = time.sec*1000000 + time.usec;
    } else {
	/*
	 * A semi-NativeGetTime, specialized to clicks.
	 */
	struct tms dummy;

	now = (unsigned long) times(&dummy);
    }
#else
    Tcl_Time time;

    (*tclGetTimeProcPtr) (&time, tclTimeClientData);
    now = time.sec*1000000 + time.usec;
#endif

    return now;
}
#ifdef TCL_WIDE_CLICKS

/*
 *-----------------------------------------------------------------------------
 *
 * TclpGetWideClicks --
 *
 *	This procedure returns a WideInt value that represents the highest
 *	resolution clock available on the system. There are no garantees on
 *	what the resolution will be. In Tcl we will call this value a "click".
 *	The start time is also system dependant.
 *
 * Results:
 *	Number of WideInt clicks from some start time.
 *
 * Side effects:
 *	None.
 *
 *-----------------------------------------------------------------------------
 */

Tcl_WideInt
TclpGetWideClicks(void)
{
    Tcl_WideInt now;

    if (tclGetTimeProcPtr != NativeGetTime) {
	Tcl_Time time;

	(*tclGetTimeProcPtr) (&time, tclTimeClientData);
	now = (Tcl_WideInt) (time.sec*1000000 + time.usec);
    } else {
#ifdef MAC_OSX_TCL
	now = (Tcl_WideInt) (mach_absolute_time() & INT64_MAX);
#else
#error Wide high-resolution clicks not implemented on this platform
#endif
    }

    return now;
}

/*
 *-----------------------------------------------------------------------------
 *
 * TclpWideClicksToNanoseconds --
 *
 *	This procedure converts click values from the TclpGetWideClicks native
 *	resolution to nanosecond resolution.
 *
 * Results:
 *	Number of nanoseconds from some start time.
 *
 * Side effects:
 *	None.
 *
 *-----------------------------------------------------------------------------
 */

double
TclpWideClicksToNanoseconds(
    Tcl_WideInt clicks)
{
    double nsec;

    if (tclGetTimeProcPtr != NativeGetTime) {
	nsec = clicks * 1000;
    } else {
#ifdef MAC_OSX_TCL
	static mach_timebase_info_data_t tb;
	static uint64_t maxClicksForUInt64;
	
	if (!tb.denom) {
	    mach_timebase_info(&tb);
	    maxClicksForUInt64 = UINT64_MAX / tb.numer;
	}
	if ((uint64_t) clicks < maxClicksForUInt64) {
	    nsec = ((uint64_t) clicks) * tb.numer / tb.denom;
	} else {
	    nsec = ((long double) (uint64_t) clicks) * tb.numer / tb.denom;
	}
#else
#error Wide high-resolution clicks not implemented on this platform
#endif
    }

    return nsec;
}
#endif /* TCL_WIDE_CLICKS */

/*
 *----------------------------------------------------------------------
 *
 * TclpGetTimeZone --
 *
 *	Determines the current timezone. The method varies wildly between
 *	different platform implementations, so its hidden in this function.
 *
 * Results:
 *	The return value is the local time zone, measured in minutes away from
 *	GMT (-ve for east, +ve for west).
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */

int
TclpGetTimeZone(
    unsigned long currentTime)
{
    int timeZone;

    /*
     * We prefer first to use the time zone in "struct tm" if the structure
     * contains such a member. Following that, we try to locate the external
     * 'timezone' variable and use its value. If both of those methods fail,
     * we attempt to convert a known time to local time and use the difference
     * from UTC as the local time zone. In all cases, we need to undo any
     * Daylight Saving Time adjustment.
     */

#if defined(HAVE_TM_TZADJ)
#define TCL_GOT_TIMEZONE
    /*
     * Struct tm contains tm_tzadj - that value may be used.
     */

    time_t curTime = (time_t) currentTime;
    struct tm *timeDataPtr = TclpLocaltime(&curTime);

    timeZone = timeDataPtr->tm_tzadj / 60;
    if (timeDataPtr->tm_isdst) {
	timeZone += 60;
    }
#endif

#if defined(HAVE_TM_GMTOFF) && !defined (TCL_GOT_TIMEZONE)
#define TCL_GOT_TIMEZONE
    /*
     * Struct tm contains tm_gmtoff - that value may be used.
     */

    time_t curTime = (time_t) currentTime;
    struct tm *timeDataPtr = TclpLocaltime(&curTime);

    timeZone = -(timeDataPtr->tm_gmtoff / 60);
    if (timeDataPtr->tm_isdst) {
	timeZone += 60;
    }
#endif

#if defined(HAVE_TIMEZONE_VAR) && !defined(TCL_GOT_TIMEZONE) && !defined(USE_DELTA_FOR_TZ)
#define TCL_GOT_TIMEZONE
    /*
     * The 'timezone' external var is present and may be used.
     */

    SetTZIfNecessary();

    /*
     * Note: this is not a typo in "timezone" below! See tzset documentation
     * for details.
     */

    timeZone = timezone / 60;
#endif

#if !defined(TCL_GOT_TIMEZONE)
#define TCL_GOT_TIMEZONE
    /*
     * Fallback - determine time zone with a known reference time.
     */

    time_t tt;
    struct tm *stm;

    tt = 849268800L;		/* 1996-11-29 12:00:00  GMT */
    stm = TclpLocaltime(&tt);	/* eg 1996-11-29  6:00:00  CST6CDT */

    /*
     * The calculation below assumes a max of +12 or -12 hours from GMT.
     */

    timeZone = (12 - stm->tm_hour)*60 + (0 - stm->tm_min);
    if (stm->tm_isdst) {
	timeZone += 60;
    }

    /*
     * Now have offset for our known reference time, eg +360 for CST6CDT.
     */
#endif

#ifndef TCL_GOT_TIMEZONE
    /*
     * Cause fatal compile error, we don't know how to get timezone.
     */

#error autoconf did not figure out how to determine the timezone.
#endif

    return timeZone;
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_GetTime --
 *
 *	Gets the current system time in seconds and microseconds since the
 *	beginning of the epoch: 00:00 UCT, January 1, 1970.
 *
 *	This function is hooked, allowing users to specify their own virtual
 *	system time.
 *
 * Results:
 *	Returns the current time in timePtr.
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */

void
Tcl_GetTime(
    Tcl_Time *timePtr)		/* Location to store time information. */
{
    (*tclGetTimeProcPtr) (timePtr, tclTimeClientData);
}

/*
 *----------------------------------------------------------------------
 *
 * TclpGetDate --
 *
 *	This function converts between seconds and struct tm. If useGMT is
 *	true, then the returned date will be in Greenwich Mean Time (GMT).
 *	Otherwise, it will be in the local time zone.
 *
 * Results:
 *	Returns a static tm structure.
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */

struct tm *
TclpGetDate(
    CONST time_t *time,
    int useGMT)
{
    if (useGMT) {
	return TclpGmtime(time);
    } else {
	return TclpLocaltime(time);
    }
}

/*
 *----------------------------------------------------------------------
 *
 * TclpGmtime --
 *
 *	Wrapper around the 'gmtime' library function to make it thread safe.
 *
 * Results:
 *	Returns a pointer to a 'struct tm' in thread-specific data.
 *
 * Side effects:
 *	Invokes gmtime or gmtime_r as appropriate.
 *
 *----------------------------------------------------------------------
 */

struct tm *
TclpGmtime(
    CONST time_t *timePtr)	/* Pointer to the number of seconds since the
				 * local system's epoch */
{
    /*
     * Get a thread-local buffer to hold the returned time.
     */

    ThreadSpecificData *tsdPtr = TCL_TSD_INIT(&tmKey);

#ifdef HAVE_GMTIME_R
    gmtime_r(timePtr, &(tsdPtr->gmtime_buf));
#else
    Tcl_MutexLock(&tmMutex);
    memcpy(&(tsdPtr->gmtime_buf), gmtime(timePtr), sizeof(struct tm));
    Tcl_MutexUnlock(&tmMutex);
#endif

    return &(tsdPtr->gmtime_buf);
}

/*
 * Forwarder for obsolete item in Stubs
 */

struct tm *
TclpGmtime_unix(
    CONST time_t *timePtr)
{
    return TclpGmtime(timePtr);
}

/*
 *----------------------------------------------------------------------
 *
 * TclpLocaltime --
 *
 *	Wrapper around the 'localtime' library function to make it thread
 *	safe.
 *
 * Results:
 *	Returns a pointer to a 'struct tm' in thread-specific data.
 *
 * Side effects:
 *	Invokes localtime or localtime_r as appropriate.
 *
 *----------------------------------------------------------------------
 */

struct tm *
TclpLocaltime(
    CONST time_t *timePtr)	/* Pointer to the number of seconds since the
				 * local system's epoch */
{
    /*
     * Get a thread-local buffer to hold the returned time.
     */

    ThreadSpecificData *tsdPtr = TCL_TSD_INIT(&tmKey);

    SetTZIfNecessary();
#ifdef HAVE_LOCALTIME_R
    localtime_r(timePtr, &(tsdPtr->localtime_buf));
#else
    Tcl_MutexLock(&tmMutex);
    memcpy(&(tsdPtr->localtime_buf), localtime(timePtr), sizeof(struct tm));
    Tcl_MutexUnlock(&tmMutex);
#endif

    return &(tsdPtr->localtime_buf);
}
/*
 * Forwarder for obsolete item in Stubs
 */
struct tm*
TclpLocaltime_unix(
    CONST time_t *timePtr)
{
    return TclpLocaltime(timePtr);
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_SetTimeProc --
 *
 *	TIP #233 (Virtualized Time): Registers two handlers for the
 *	virtualization of Tcl's access to time information.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	Remembers the handlers, alters core behaviour.
 *
 *----------------------------------------------------------------------
 */

void
Tcl_SetTimeProc(
    Tcl_GetTimeProc *getProc,
    Tcl_ScaleTimeProc *scaleProc,
    ClientData clientData)
{
    tclGetTimeProcPtr = getProc;
    tclScaleTimeProcPtr = scaleProc;
    tclTimeClientData = clientData;
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_QueryTimeProc --
 *
 *	TIP #233 (Virtualized Time): Query which time handlers are registered.
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
Tcl_QueryTimeProc(
    Tcl_GetTimeProc **getProc,
    Tcl_ScaleTimeProc **scaleProc,
    ClientData *clientData)
{
    if (getProc) {
	*getProc = tclGetTimeProcPtr;
    }
    if (scaleProc) {
	*scaleProc = tclScaleTimeProcPtr;
    }
    if (clientData) {
	*clientData = tclTimeClientData;
    }
}

/*
 *----------------------------------------------------------------------
 *
 * NativeScaleTime --
 *
 *	TIP #233: Scale from virtual time to the real-time. For native scaling
 *	the relationship is 1:1 and nothing has to be done.
 *
 * Results:
 *	Scales the time in timePtr.
 *
 * Side effects:
 *	See above.
 *
 *----------------------------------------------------------------------
 */

static void
NativeScaleTime(
    Tcl_Time *timePtr,
    ClientData clientData)
{
    /* Native scale is 1:1. Nothing is done */
}

/*
 *----------------------------------------------------------------------
 *
 * NativeGetTime --
 *
 *	TIP #233: Gets the current system time in seconds and microseconds
 *	since the beginning of the epoch: 00:00 UCT, January 1, 1970.
 *
 * Results:
 *	Returns the current time in timePtr.
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */

static void
NativeGetTime(
    Tcl_Time *timePtr,
    ClientData clientData)
{
    struct timeval tv;

    (void) gettimeofday(&tv, NULL);
    timePtr->sec = tv.tv_sec;
    timePtr->usec = tv.tv_usec;
}
/*
 *----------------------------------------------------------------------
 *
 * SetTZIfNecessary --
 *
 *	Determines whether a call to 'tzset' is needed prior to the next call
 *	to 'localtime' or examination of the 'timezone' variable.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	If 'tzset' has never been called in the current process, or if the
 *	value of the environment variable TZ has changed since the last call
 *	to 'tzset', then 'tzset' is called again.
 *
 *----------------------------------------------------------------------
 */

static void
SetTZIfNecessary(void)
{
    CONST char *newTZ = getenv("TZ");

    Tcl_MutexLock(&tmMutex);
    if (newTZ == NULL) {
	newTZ = "";
    }
    if (lastTZ == NULL || strcmp(lastTZ, newTZ)) {
	tzset();
	if (lastTZ == NULL) {
	    Tcl_CreateExitHandler(CleanupMemory, (ClientData) NULL);
	} else {
	    Tcl_Free(lastTZ);
	}
	lastTZ = ckalloc(strlen(newTZ) + 1);
	strcpy(lastTZ, newTZ);
    }
    Tcl_MutexUnlock(&tmMutex);
}

/*
 *----------------------------------------------------------------------
 *
 * CleanupMemory --
 *
 *	Releases the private copy of the TZ environment variable upon exit
 *	from Tcl.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	Frees allocated memory.
 *
 *----------------------------------------------------------------------
 */

static void
CleanupMemory(
    ClientData ignored)
{
    ckfree(lastTZ);
}

/*
 * Local Variables:
 * mode: c
 * c-basic-offset: 4
 * fill-column: 78
 * End:
 */
