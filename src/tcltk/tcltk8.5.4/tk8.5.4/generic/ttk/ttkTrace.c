/* $Id: ttkTrace.c,v 1.1 2006/10/31 01:42:26 hobbs Exp $
 *
 * Copyright 2003, Joe English
 *
 * Simplified interface to Tcl_TraceVariable.
 *
 * PROBLEM: Can't distinguish "variable does not exist" (which is OK) 
 * from other errors (which are not).
 */

#include <tk.h>
#include "ttkTheme.h"
#include "ttkWidget.h"

struct TtkTraceHandle_
{
    Tcl_Interp		*interp;	/* Containing interpreter */
    Tcl_Obj 		*varnameObj;	/* Name of variable being traced */
    Ttk_TraceProc	callback;	/* Callback procedure */
    void		*clientData;	/* Data to pass to callback */
};

/*
 * Tcl_VarTraceProc for trace handles.
 */
static char *
VarTraceProc(
    ClientData clientData,	/* Widget record pointer */
    Tcl_Interp *interp, 	/* Interpreter containing variable. */
    CONST char *name1,		/* (unused) */
    CONST char *name2,		/* (unused) */
    int flags)			/* Information about what happened. */
{
    Ttk_TraceHandle *tracePtr = clientData;
    const char *name, *value;
    Tcl_Obj *valuePtr;

    if (flags & TCL_INTERP_DESTROYED) {
	return NULL;
    }

    name = Tcl_GetString(tracePtr->varnameObj);

    /*
     * If the variable is being unset, then re-establish the trace:
     */
    if (flags & TCL_TRACE_DESTROYED) {
	Tcl_TraceVar(interp, name,
		TCL_GLOBAL_ONLY|TCL_TRACE_WRITES|TCL_TRACE_UNSETS,
		VarTraceProc, clientData);
	tracePtr->callback(tracePtr->clientData, NULL);
	return NULL;
    }

    /*
     * Call the callback:
     */
    valuePtr = Tcl_GetVar2Ex(interp, name, NULL, TCL_GLOBAL_ONLY);
    value = valuePtr ?  Tcl_GetString(valuePtr) : NULL;
    tracePtr->callback(tracePtr->clientData, value);

    return NULL;
}

/* Ttk_TraceVariable(interp, varNameObj, callback, clientdata) --
 * 	Attach a write trace to the specified variable,
 * 	which will pass the variable's value to 'callback'
 * 	whenever the variable is set.
 *
 * 	When the variable is unset, passes NULL to the callback
 * 	and reattaches the trace.
 */
Ttk_TraceHandle *Ttk_TraceVariable(
    Tcl_Interp *interp,
    Tcl_Obj *varnameObj,
    Ttk_TraceProc callback,
    void *clientData)
{
    Ttk_TraceHandle *h = (Ttk_TraceHandle*)ckalloc(sizeof(*h));
    int status;

    h->interp = interp;
    h->varnameObj = Tcl_DuplicateObj(varnameObj);
    Tcl_IncrRefCount(h->varnameObj);
    h->clientData = clientData;
    h->callback = callback;

    status = Tcl_TraceVar(interp, Tcl_GetString(varnameObj),
	    TCL_GLOBAL_ONLY|TCL_TRACE_WRITES|TCL_TRACE_UNSETS,
	    VarTraceProc, (ClientData)h);

    if (status != TCL_OK) {
	Tcl_DecrRefCount(h->varnameObj);
	ckfree((ClientData)h);
	return NULL;
    }

    return h;
}

/*
 * Ttk_UntraceVariable --
 * 	Remove previously-registered trace and free the handle.
 */
void Ttk_UntraceVariable(Ttk_TraceHandle *h)
{
    if (h) {
	Tcl_UntraceVar(h->interp, Tcl_GetString(h->varnameObj),
		TCL_GLOBAL_ONLY|TCL_TRACE_WRITES|TCL_TRACE_UNSETS,
		VarTraceProc, (ClientData)h);
	Tcl_DecrRefCount(h->varnameObj);
	ckfree((ClientData)h);
    }
}

/*
 * Ttk_FireTrace --
 * 	Executes a trace handle as if the variable has been written.
 *
 * 	Note: may reenter the interpreter.
 */
int Ttk_FireTrace(Ttk_TraceHandle *tracePtr)
{
    Tcl_Interp *interp = tracePtr->interp;
    void *clientData = tracePtr->clientData;
    const char *name = Tcl_GetString(tracePtr->varnameObj);
    Ttk_TraceProc callback = tracePtr->callback;
    Tcl_Obj *valuePtr;
    const char *value;

    /* Read the variable.
     * Note that this can reenter the interpreter, and anything can happen --
     * including the current trace handle being freed!
     */
    valuePtr = Tcl_GetVar2Ex(interp, name, NULL, TCL_GLOBAL_ONLY);
    value = valuePtr ? Tcl_GetString(valuePtr) : NULL;

    /* Call callback.
     */
    callback(clientData, value);

    return TCL_OK;
}

/*EOF*/
