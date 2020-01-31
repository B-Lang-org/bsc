/*
 * ------------------------------------------------------------------------
 *      PACKAGE:  [incr Tcl]
 *  DESCRIPTION:  Object-Oriented Extensions to Tcl
 *
 *  This file contains procedures that belong in the Tcl/Tk core.
 *  Hopefully, they'll migrate there soon.
 *
 * ========================================================================
 *  AUTHOR:  Michael J. McLennan
 *           Bell Labs Innovations for Lucent Technologies
 *           mmclennan@lucent.com
 *           http://www.tcltk.com/itcl
 *
 *     RCS:  $Id: itcl_migrate.c,v 1.4 2007/08/07 20:05:30 msofer Exp $
 * ========================================================================
 *           Copyright (c) 1993-1998  Lucent Technologies, Inc.
 * ------------------------------------------------------------------------
 * See the file "license.terms" for information on usage and redistribution
 * of this file, and for a DISCLAIMER OF ALL WARRANTIES.
 */
#include "itclInt.h"


/*
 *----------------------------------------------------------------------
 *
 * _Tcl_GetCallFrame --
 *
 *	Checks the call stack and returns the call frame some number
 *	of levels up.  It is often useful to know the invocation
 *	context for a command.
 *
 * Results:
 *	Returns a token for the call frame 0 or more levels up in
 *	the call stack.
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */
Itcl_CallFrame*
_Tcl_GetCallFrame(interp, level)
    Tcl_Interp *interp;  /* interpreter being queried */
    int level;           /* number of levels up in the call stack (>= 0) */
{
    Interp *iPtr = (Interp*)interp;
    CallFrame *framePtr;

    if (level < 0) {
        Tcl_Panic("itcl: _Tcl_GetCallFrame called with bad number of levels");
    }

    framePtr = iPtr->varFramePtr;
    while (framePtr && level > 0) {
        framePtr = framePtr->callerVarPtr;
        level--;
    }
    return (Itcl_CallFrame *) framePtr;
}


/*
 *----------------------------------------------------------------------
 *
 * _Tcl_ActivateCallFrame --
 *
 *	Makes an existing call frame the current frame on the
 *	call stack.  Usually called in conjunction with
 *	_Tcl_GetCallFrame to simulate the effect of an "uplevel"
 *	command.
 *
 *	Note that this procedure is different from Tcl_PushCallFrame,
 *	which adds a new call frame to the call stack.  This procedure
 *	assumes that the call frame is already initialized, and it
 *	merely activates it on the call stack.
 *
 * Results:
 *	Returns a token for the call frame that was in effect before
 *	activating the new context.  That call frame can be restored
 *	by calling _Tcl_ActivateCallFrame again.
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */
Itcl_CallFrame*
_Tcl_ActivateCallFrame(interp, framePtr)
    Tcl_Interp *interp;        /* interpreter being queried */
    Itcl_CallFrame *framePtr;   /* call frame to be activated */
{
    Interp *iPtr = (Interp*)interp;
    CallFrame *oldFramePtr;

    oldFramePtr = iPtr->varFramePtr;
    iPtr->varFramePtr = (CallFrame *) framePtr;

    return (Itcl_CallFrame *) oldFramePtr;
}

/*
 *----------------------------------------------------------------------
 *
 * _TclNewVar --
 *
 *      Create a new heap-allocated variable that will eventually be
 *      entered into a hashtable.
 *
 * Results:
 *      The return value is a pointer to the new variable structure. It is
 *      marked as a scalar variable (and not a link or array variable). Its
 *      value initially is NULL. The variable is not part of any hash table
 *      yet. Since it will be in a hashtable and not in a call frame, its
 *      name field is set NULL. It is initially marked as undefined.
 *
 * Side effects:
 *      Storage gets allocated.
 *
 *----------------------------------------------------------------------
 */

Var *
_TclNewVar()
{
    Var *varPtr;

    varPtr = (Var *) ckalloc(itclVarLocalSize);
    ItclInitVarFlags(varPtr);
    ItclVarObjValue(varPtr) = NULL;
#if ITCL_TCL_PRE_8_5
    if (itclOldRuntime) {
	varPtr->name = NULL;
	varPtr->nsPtr = NULL;
	varPtr->hPtr = NULL;
	varPtr->refCount = 0;
	varPtr->tracePtr = NULL;
	varPtr->searchPtr = NULL;
    }
#endif
    return varPtr;
}

#if ITCL_TCL_PRE_8_5
Var *
ItclVarHashCreateVar(
    TclVarHashTable *tablePtr,
    const char *key,
    int *newPtr)
{
#if (USE_TCL_STUBS)
    if (itclOldRuntime) {
#endif
	Tcl_HashEntry *hPtr;
	
	if (newPtr) {
	    Var *varPtr = _TclNewVar();

	    hPtr = Tcl_CreateHashEntry(tablePtr, key, newPtr);
	    varPtr->hPtr = hPtr;
	    Tcl_SetHashValue(hPtr, varPtr);	
	} else {
	    hPtr = Tcl_FindHashEntry(tablePtr, key);
	}	
	
	if (hPtr) {
	    return (Var *) Tcl_GetHashValue(hPtr);
	} else {
	    return NULL;
	}
#if (USE_TCL_STUBS)
    } else {
	/*
	 * An 8.5 runtime: TclVarHashCreateVar is at position 234 in the
	 * internal stubs table: call it.
	 */
	
	Var * (*TclVarHashCreateVar)(Tcl_HashTable *, const char *, int *) =
	    (Var * (*)(Tcl_HashTable *, const char *, int *)) *((&tclIntStubsPtr->reserved0)+234);
	return (*TclVarHashCreateVar)(tablePtr, key, newPtr);
    }
#endif
}
#endif
