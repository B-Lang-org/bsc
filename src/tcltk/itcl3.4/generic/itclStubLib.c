/* 
 * itclStubLib.c --
 *
 *	Stub object that will be statically linked into extensions that wish
 *	to access Itcl.
 *
 * Copyright (c) 1998 Paul Duffin.
 *
 * See the file "license.terms" for information on usage and redistribution
 * of this file, and for a DISCLAIMER OF ALL WARRANTIES.
 *
 * RCS: $Id: itclStubLib.c,v 1.9 2003/12/24 03:38:02 davygrvy Exp $
 */

/*
 * We need to ensure that we use the stub macros so that this file contains
 * no references to any of the stub functions.  This will make it possible
 * to build an extension that references Tcl_InitStubs but doesn't end up
 * including the rest of the stub functions.
 */

#ifndef USE_TCL_STUBS
#define USE_TCL_STUBS
#endif
#undef USE_TCL_STUB_PROCS

/*
 * This ensures that the Itcl_InitStubs has a prototype in
 * itcl.h and is not the macro that turns it into Tcl_PkgRequire
 */

#ifndef USE_ITCL_STUBS
#define USE_ITCL_STUBS
#endif

#include "itclInt.h"

ItclStubs *itclStubsPtr;
ItclIntStubs *itclIntStubsPtr;

/*
 *----------------------------------------------------------------------
 *
 * Itcl_InitStubs --
 *
 *	Tries to initialize the stub table pointers and ensures that
 *	the correct version of Itcl is loaded.
 *
 * Results:
 *	The actual version of Itcl that satisfies the request, or
 *	NULL to indicate that an error occurred.
 *
 * Side effects:
 *	Sets the stub table pointers.
 *
 *----------------------------------------------------------------------
 */

#ifdef Itcl_InitStubs
#undef Itcl_InitStubs
#endif

CONST char *
Itcl_InitStubs (interp, version, exact)
    Tcl_Interp *interp;
    CONST char *version;
    int exact;
{
    CONST char *actualVersion;
    
    actualVersion = Tcl_PkgRequireEx(interp, "Itcl", (CONST84 char *)version, exact,
        (ClientData *) &itclStubsPtr);

    if (actualVersion == NULL) {
	itclStubsPtr = NULL;
	return NULL;
    }

    if (itclStubsPtr->hooks) {
	itclIntStubsPtr = itclStubsPtr->hooks->itclIntStubs;
    } else {
	itclIntStubsPtr = NULL;
    }
    
    return actualVersion;
}
