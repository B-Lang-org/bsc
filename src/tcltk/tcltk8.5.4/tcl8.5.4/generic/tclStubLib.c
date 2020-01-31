/*
 * tclStubLib.c --
 *
 *	Stub object that will be statically linked into extensions that want
 *	to access Tcl.
 *
 * Copyright (c) 1998-1999 by Scriptics Corporation.
 * Copyright (c) 1998 Paul Duffin.
 *
 * See the file "license.terms" for information on usage and redistribution of
 * this file, and for a DISCLAIMER OF ALL WARRANTIES.
 *
 * RCS: @(#) $Id: tclStubLib.c,v 1.21.2.1 2008/04/01 19:21:06 dgp Exp $
 */

/*
 * We need to ensure that we use the stub macros so that this file contains no
 * references to any of the stub functions. This will make it possible to
 * build an extension that references Tcl_InitStubs but doesn't end up
 * including the rest of the stub functions.
 */

#ifndef USE_TCL_STUBS
#define USE_TCL_STUBS
#endif
#undef USE_TCL_STUB_PROCS

#include "tclInt.h"

/*
 * Tcl_InitStubs and stub table pointers are built as exported symbols.
 */

TclStubs *tclStubsPtr = NULL;
TclPlatStubs *tclPlatStubsPtr = NULL;
TclIntStubs *tclIntStubsPtr = NULL;
TclIntPlatStubs *tclIntPlatStubsPtr = NULL;
TclTomMathStubs* tclTomMathStubsPtr = NULL;

static TclStubs *
HasStubSupport(
    Tcl_Interp *interp)
{
    Interp *iPtr = (Interp *) interp;

    if (iPtr->stubTable && (iPtr->stubTable->magic == TCL_STUB_MAGIC)) {
	return iPtr->stubTable;
    }

    interp->result =
	    "This interpreter does not support stubs-enabled extensions.";
    interp->freeProc = TCL_STATIC;
    return NULL;
}

/*
 * Use our own isdigit to avoid linking to libc on windows
 */

static int isDigit(const int c)
{
    return (c >= '0' && c <= '9');
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_InitStubs --
 *
 *	Tries to initialise the stub table pointers and ensures that the
 *	correct version of Tcl is loaded.
 *
 * Results:
 *	The actual version of Tcl that satisfies the request, or NULL to
 *	indicate that an error occurred.
 *
 * Side effects:
 *	Sets the stub table pointers.
 *
 *----------------------------------------------------------------------
 */

#ifdef Tcl_InitStubs
#undef Tcl_InitStubs
#endif

CONST char *
Tcl_InitStubs(
    Tcl_Interp *interp,
    CONST char *version,
    int exact)
{
    CONST char *actualVersion = NULL;
    ClientData pkgData = NULL;

    /*
     * We can't optimize this check by caching tclStubsPtr because that
     * prevents apps from being able to load/unload Tcl dynamically multiple
     * times. [Bug 615304]
     */

    tclStubsPtr = HasStubSupport(interp);
    if (!tclStubsPtr) {
	return NULL;
    }

    actualVersion = Tcl_PkgRequireEx(interp, "Tcl", version, 0, &pkgData);
    if (actualVersion == NULL) {
	return NULL;
    }
    if (exact) {
	CONST char *p = version;
	int count = 0;

	while (*p) {
	    count += !isDigit(*p++);
	}
	if (count == 1) {
	    CONST char *q = actualVersion;

	    p = version;
	    while (*p && (*p == *q)) {
		p++; q++;
	    }
	    if (*p) {
		/* Construct error message */
		Tcl_PkgRequireEx(interp, "Tcl", version, 1, NULL);
		return NULL;
	    }
	} else {
	    actualVersion = Tcl_PkgRequireEx(interp, "Tcl", version, 1, NULL);
	    if (actualVersion == NULL) {
		return NULL;
	    }
	}
    }
    tclStubsPtr = (TclStubs*)pkgData;

    if (tclStubsPtr->hooks) {
	tclPlatStubsPtr = tclStubsPtr->hooks->tclPlatStubs;
	tclIntStubsPtr = tclStubsPtr->hooks->tclIntStubs;
	tclIntPlatStubsPtr = tclStubsPtr->hooks->tclIntPlatStubs;
    } else {
	tclPlatStubsPtr = NULL;
	tclIntStubsPtr = NULL;
	tclIntPlatStubsPtr = NULL;
    }

    return actualVersion;
}

/*
 *----------------------------------------------------------------------
 *
 * TclTomMathInitStubs --
 *
 *	Initializes the Stubs table for Tcl's subset of libtommath
 *
 * Results:
 *	Returns a standard Tcl result.
 *
 * This procedure should not be called directly, but rather through
 * the TclTomMath_InitStubs macro, to insure that the Stubs table
 * matches the header files used in compilation.
 *
 *----------------------------------------------------------------------
 */

#ifdef TclTomMathInitializeStubs
#undef TclTomMathInitializeStubs
#endif

CONST char*
TclTomMathInitializeStubs(
    Tcl_Interp* interp,		/* Tcl interpreter */
    CONST char* version,	/* Tcl version needed */
    int epoch,			/* Stubs table epoch from the header files */
    int revision		/* Stubs table revision number from the
				 * header files */
) {
    int exact = 0;
    const char* packageName = "tcl::tommath";
    const char* errMsg = NULL;
    ClientData pkgClientData = NULL;
    const char* actualVersion = 
	Tcl_PkgRequireEx(interp, packageName, version, exact, &pkgClientData);
    TclTomMathStubs* stubsPtr = (TclTomMathStubs*) pkgClientData;
    if (actualVersion == NULL) {
	return NULL;
    }
    if (pkgClientData == NULL) {
	errMsg = "missing stub table pointer";
    } else if ((stubsPtr->tclBN_epoch)() != epoch) {
	errMsg = "epoch number mismatch";
    } else if ((stubsPtr->tclBN_revision)() != revision) {
	errMsg = "requires a later revision";
    } else {
	tclTomMathStubsPtr = stubsPtr;
	return actualVersion;
    }
    Tcl_ResetResult(interp);
    Tcl_AppendResult(interp, "error loading ", packageName,
		     " (requested version ", version,
		     ", actual version ", actualVersion,
		     "): ", errMsg, NULL);
    return NULL;
}
