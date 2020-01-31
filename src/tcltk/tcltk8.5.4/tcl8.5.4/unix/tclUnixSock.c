/*
 * tclUnixSock.c --
 *
 *	This file contains Unix-specific socket related code.
 *
 * Copyright (c) 1995 Sun Microsystems, Inc.
 *
 * See the file "license.terms" for information on usage and redistribution of
 * this file, and for a DISCLAIMER OF ALL WARRANTIES.
 *
 * RCS: @(#) $Id: tclUnixSock.c,v 1.20 2007/12/13 15:28:42 dgp Exp $
 */

#include "tclInt.h"

/*
 * The following variable holds the network name of this host.
 */

static TclInitProcessGlobalValueProc InitializeHostName;
static ProcessGlobalValue hostName =
	{0, 0, NULL, NULL, InitializeHostName, NULL, NULL};


/*
 *----------------------------------------------------------------------
 *
 * InitializeHostName --
 *
 * 	This routine sets the process global value of the name of the local
 * 	host on which the process is running.
 *
 * Results:
 *	None.
 *
 *----------------------------------------------------------------------
 */

static void
InitializeHostName(
    char **valuePtr,
    int *lengthPtr,
    Tcl_Encoding *encodingPtr)
{
    CONST char *native = NULL;

#ifndef NO_UNAME
    struct utsname u;
    struct hostent *hp;

    memset(&u, (int) 0, sizeof(struct utsname));
    if (uname(&u) > -1) {				/* INTL: Native. */
        hp = TclpGetHostByName(u.nodename);		/* INTL: Native. */
	if (hp == NULL) {
	    /*
	     * Sometimes the nodename is fully qualified, but gets truncated
	     * as it exceeds SYS_NMLN. See if we can just get the immediate
	     * nodename and get a proper answer that way.
	     */

	    char *dot = strchr(u.nodename, '.');

	    if (dot != NULL) {
		char *node = ckalloc((unsigned) (dot - u.nodename + 1));

		memcpy(node, u.nodename, (size_t) (dot - u.nodename));
		node[dot - u.nodename] = '\0';
		hp = TclpGetHostByName(node);
		ckfree(node);
	    }
	}
        if (hp != NULL) {
	    native = hp->h_name;
        } else {
	    native = u.nodename;
        }
    }
    if (native == NULL) {
	native = tclEmptyStringRep;
    }
#else
    /*
     * Uname doesn't exist; try gethostname instead.
     *
     * There is no portable macro for the maximum length of host names
     * returned by gethostbyname(). We should only trust SYS_NMLN if it is at
     * least 255 + 1 bytes to comply with DNS host name limits.
     *
     * Note: SYS_NMLN is a restriction on "uname" not on gethostbyname!
     *
     * For example HP-UX 10.20 has SYS_NMLN == 9, while gethostbyname() can
     * return a fully qualified name from DNS of up to 255 bytes.
     *
     * Fix suggested by Viktor Dukhovni (viktor@esm.com)
     */

#    if defined(SYS_NMLN) && SYS_NMLEN >= 256
    char buffer[SYS_NMLEN];
#    else
    char buffer[256];
#    endif

    if (gethostname(buffer, sizeof(buffer)) > -1) {	/* INTL: Native. */
	native = buffer;
    }
#endif

    *encodingPtr = Tcl_GetEncoding(NULL, NULL);
    *lengthPtr = strlen(native);
    *valuePtr = ckalloc((unsigned int) (*lengthPtr)+1);
    memcpy(*valuePtr, (void *) native, (size_t)(*lengthPtr)+1);
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_GetHostName --
 *
 *	Returns the name of the local host.
 *
 * Results:
 *	A string containing the network name for this machine, or an empty
 *	string if we can't figure out the name. The caller must not modify or
 *	free this string.
 *
 * Side effects:
 *	Caches the name to return for future calls.
 *
 *----------------------------------------------------------------------
 */

CONST char *
Tcl_GetHostName(void)
{
    return Tcl_GetString(TclGetProcessGlobalValue(&hostName));
}

/*
 *----------------------------------------------------------------------
 *
 * TclpHasSockets --
 *
 *	Detect if sockets are available on this platform.
 *
 * Results:
 *	Returns TCL_OK.
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */

int
TclpHasSockets(
    Tcl_Interp *interp)		/* Not used. */
{
    return TCL_OK;
}

/*
 *----------------------------------------------------------------------
 *
 * TclpFinalizeSockets --
 *
 *	Performs per-thread socket subsystem finalization.
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
TclpFinalizeSockets(void)
{
    return;
}

/*
 * Local Variables:
 * mode: c
 * c-basic-offset: 4
 * fill-column: 78
 * End:
 */
