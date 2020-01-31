/*
 * tclLink.c --
 *
 *	This file implements linked variables (a C variable that is tied to a
 *	Tcl variable). The idea of linked variables was first suggested by
 *	Andreas Stolcke and this implementation is based heavily on a
 *	prototype implementation provided by him.
 *
 * Copyright (c) 1993 The Regents of the University of California.
 * Copyright (c) 1994-1997 Sun Microsystems, Inc.
 *
 * See the file "license.terms" for information on usage and redistribution of
 * this file, and for a DISCLAIMER OF ALL WARRANTIES.
 *
 * RCS: @(#) $Id: tclLink.c,v 1.24 2007/12/13 15:23:18 dgp Exp $
 */

#include "tclInt.h"

/*
 * For each linked variable there is a data structure of the following type,
 * which describes the link and is the clientData for the trace set on the Tcl
 * variable.
 */

typedef struct Link {
    Tcl_Interp *interp;		/* Interpreter containing Tcl variable. */
    Tcl_Obj *varName;		/* Name of variable (must be global). This is
				 * needed during trace callbacks, since the
				 * actual variable may be aliased at that time
				 * via upvar. */
    char *addr;			/* Location of C variable. */
    int type;			/* Type of link (TCL_LINK_INT, etc.). */
    union {
	char c;
	unsigned char uc;
	int i;
	unsigned int ui;
	short s;
	unsigned short us;
	long l;
	unsigned long ul;
	Tcl_WideInt w;
	Tcl_WideUInt uw;
	float f;
	double d;
    } lastValue;		/* Last known value of C variable; used to
				 * avoid string conversions. */
    int flags;			/* Miscellaneous one-bit values; see below for
				 * definitions. */
} Link;

/*
 * Definitions for flag bits:
 * LINK_READ_ONLY -		1 means errors should be generated if Tcl
 *				script attempts to write variable.
 * LINK_BEING_UPDATED -		1 means that a call to Tcl_UpdateLinkedVar is
 *				in progress for this variable, so trace
 *				callbacks on the variable should be ignored.
 */

#define LINK_READ_ONLY		1
#define LINK_BEING_UPDATED	2

/*
 * Forward references to functions defined later in this file:
 */

static char *		LinkTraceProc(ClientData clientData,Tcl_Interp *interp,
			    CONST char *name1, CONST char *name2, int flags);
static Tcl_Obj *	ObjValue(Link *linkPtr);

/*
 * Convenience macro for accessing the value of the C variable pointed to by a
 * link. Note that this macro produces something that may be regarded as an
 * lvalue or rvalue; it may be assigned to as well as read. Also note that
 * this macro assumes the name of the variable being accessed (linkPtr); this
 * is not strictly a good thing, but it keeps the code much shorter and
 * cleaner.
 */

#define LinkedVar(type) (*(type *) linkPtr->addr)

/*
 *----------------------------------------------------------------------
 *
 * Tcl_LinkVar --
 *
 *	Link a C variable to a Tcl variable so that changes to either one
 *	causes the other to change.
 *
 * Results:
 *	The return value is TCL_OK if everything went well or TCL_ERROR if an
 *	error occurred (the interp's result is also set after errors).
 *
 * Side effects:
 *	The value at *addr is linked to the Tcl variable "varName", using
 *	"type" to convert between string values for Tcl and binary values for
 *	*addr.
 *
 *----------------------------------------------------------------------
 */

int
Tcl_LinkVar(
    Tcl_Interp *interp,		/* Interpreter in which varName exists. */
    CONST char *varName,	/* Name of a global variable in interp. */
    char *addr,			/* Address of a C variable to be linked to
				 * varName. */
    int type)			/* Type of C variable: TCL_LINK_INT, etc. Also
				 * may have TCL_LINK_READ_ONLY OR'ed in. */
{
    Tcl_Obj *objPtr;
    Link *linkPtr;
    int code;

    linkPtr = (Link *) ckalloc(sizeof(Link));
    linkPtr->interp = interp;
    linkPtr->varName = Tcl_NewStringObj(varName, -1);
    Tcl_IncrRefCount(linkPtr->varName);
    linkPtr->addr = addr;
    linkPtr->type = type & ~TCL_LINK_READ_ONLY;
    if (type & TCL_LINK_READ_ONLY) {
	linkPtr->flags = LINK_READ_ONLY;
    } else {
	linkPtr->flags = 0;
    }
    objPtr = ObjValue(linkPtr);
    if (Tcl_ObjSetVar2(interp, linkPtr->varName, NULL, objPtr,
	    TCL_GLOBAL_ONLY|TCL_LEAVE_ERR_MSG) == NULL) {
	Tcl_DecrRefCount(linkPtr->varName);
	ckfree((char *) linkPtr);
	return TCL_ERROR;
    }
    code = Tcl_TraceVar(interp, varName, TCL_GLOBAL_ONLY|TCL_TRACE_READS
	    |TCL_TRACE_WRITES|TCL_TRACE_UNSETS, LinkTraceProc,
	    (ClientData) linkPtr);
    if (code != TCL_OK) {
	Tcl_DecrRefCount(linkPtr->varName);
	ckfree((char *) linkPtr);
    }
    return code;
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_UnlinkVar --
 *
 *	Destroy the link between a Tcl variable and a C variable.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	If "varName" was previously linked to a C variable, the link is broken
 *	to make the variable independent. If there was no previous link for
 *	"varName" then nothing happens.
 *
 *----------------------------------------------------------------------
 */

void
Tcl_UnlinkVar(
    Tcl_Interp *interp,		/* Interpreter containing variable to unlink */
    CONST char *varName)	/* Global variable in interp to unlink. */
{
    Link *linkPtr;

    linkPtr = (Link *) Tcl_VarTraceInfo(interp, varName, TCL_GLOBAL_ONLY,
	    LinkTraceProc, (ClientData) NULL);
    if (linkPtr == NULL) {
	return;
    }
    Tcl_UntraceVar(interp, varName,
	    TCL_GLOBAL_ONLY|TCL_TRACE_READS|TCL_TRACE_WRITES|TCL_TRACE_UNSETS,
	    LinkTraceProc, (ClientData) linkPtr);
    Tcl_DecrRefCount(linkPtr->varName);
    ckfree((char *) linkPtr);
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_UpdateLinkedVar --
 *
 *	This function is invoked after a linked variable has been changed by C
 *	code. It updates the Tcl variable so that traces on the variable will
 *	trigger.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	The Tcl variable "varName" is updated from its C value, causing traces
 *	on the variable to trigger.
 *
 *----------------------------------------------------------------------
 */

void
Tcl_UpdateLinkedVar(
    Tcl_Interp *interp,		/* Interpreter containing variable. */
    CONST char *varName)	/* Name of global variable that is linked. */
{
    Link *linkPtr;
    int savedFlag;

    linkPtr = (Link *) Tcl_VarTraceInfo(interp, varName, TCL_GLOBAL_ONLY,
	    LinkTraceProc, (ClientData) NULL);
    if (linkPtr == NULL) {
	return;
    }
    savedFlag = linkPtr->flags & LINK_BEING_UPDATED;
    linkPtr->flags |= LINK_BEING_UPDATED;
    Tcl_ObjSetVar2(interp, linkPtr->varName, NULL, ObjValue(linkPtr),
	    TCL_GLOBAL_ONLY);
    /*
     * Callback may have unlinked the variable. [Bug 1740631]
     */
    linkPtr = (Link *) Tcl_VarTraceInfo(interp, varName, TCL_GLOBAL_ONLY,
	    LinkTraceProc, (ClientData) NULL);
    if (linkPtr != NULL) {
	linkPtr->flags = (linkPtr->flags & ~LINK_BEING_UPDATED) | savedFlag;
    }
}

/*
 *----------------------------------------------------------------------
 *
 * LinkTraceProc --
 *
 *	This function is invoked when a linked Tcl variable is read, written,
 *	or unset from Tcl. It's responsible for keeping the C variable in sync
 *	with the Tcl variable.
 *
 * Results:
 *	If all goes well, NULL is returned; otherwise an error message is
 *	returned.
 *
 * Side effects:
 *	The C variable may be updated to make it consistent with the Tcl
 *	variable, or the Tcl variable may be overwritten to reject a
 *	modification.
 *
 *----------------------------------------------------------------------
 */

static char *
LinkTraceProc(
    ClientData clientData,	/* Contains information about the link. */
    Tcl_Interp *interp,		/* Interpreter containing Tcl variable. */
    CONST char *name1,		/* First part of variable name. */
    CONST char *name2,		/* Second part of variable name. */
    int flags)			/* Miscellaneous additional information. */
{
    Link *linkPtr = (Link *) clientData;
    int changed, valueLength;
    CONST char *value;
    char **pp;
    Tcl_Obj *valueObj;
    int valueInt;
    Tcl_WideInt valueWide;
    double valueDouble;

    /*
     * If the variable is being unset, then just re-create it (with a trace)
     * unless the whole interpreter is going away.
     */

    if (flags & TCL_TRACE_UNSETS) {
	if (Tcl_InterpDeleted(interp)) {
	    Tcl_DecrRefCount(linkPtr->varName);
	    ckfree((char *) linkPtr);
	} else if (flags & TCL_TRACE_DESTROYED) {
	    Tcl_ObjSetVar2(interp, linkPtr->varName, NULL, ObjValue(linkPtr),
		    TCL_GLOBAL_ONLY);
	    Tcl_TraceVar(interp, Tcl_GetString(linkPtr->varName),
		    TCL_GLOBAL_ONLY|TCL_TRACE_READS|TCL_TRACE_WRITES
		    |TCL_TRACE_UNSETS, LinkTraceProc, (ClientData) linkPtr);
	}
	return NULL;
    }

    /*
     * If we were invoked because of a call to Tcl_UpdateLinkedVar, then don't
     * do anything at all. In particular, we don't want to get upset that the
     * variable is being modified, even if it is supposed to be read-only.
     */

    if (linkPtr->flags & LINK_BEING_UPDATED) {
	return NULL;
    }

    /*
     * For read accesses, update the Tcl variable if the C variable has
     * changed since the last time we updated the Tcl variable.
     */

    if (flags & TCL_TRACE_READS) {
	switch (linkPtr->type) {
	case TCL_LINK_INT:
	case TCL_LINK_BOOLEAN:
	    changed = (LinkedVar(int) != linkPtr->lastValue.i);
	    break;
	case TCL_LINK_DOUBLE:
	    changed = (LinkedVar(double) != linkPtr->lastValue.d);
	    break;
	case TCL_LINK_WIDE_INT:
	    changed = (LinkedVar(Tcl_WideInt) != linkPtr->lastValue.w);
	    break;
	case TCL_LINK_WIDE_UINT:
	    changed = (LinkedVar(Tcl_WideUInt) != linkPtr->lastValue.uw);
	    break;
	case TCL_LINK_CHAR:
	    changed = (LinkedVar(char) != linkPtr->lastValue.c);
	    break;
	case TCL_LINK_UCHAR:
	    changed = (LinkedVar(unsigned char) != linkPtr->lastValue.uc);
	    break;
	case TCL_LINK_SHORT:
	    changed = (LinkedVar(short) != linkPtr->lastValue.s);
	    break;
	case TCL_LINK_USHORT:
	    changed = (LinkedVar(unsigned short) != linkPtr->lastValue.us);
	    break;
	case TCL_LINK_UINT:
	    changed = (LinkedVar(unsigned int) != linkPtr->lastValue.ui);
	    break;
	case TCL_LINK_LONG:
	    changed = (LinkedVar(long) != linkPtr->lastValue.l);
	    break;
	case TCL_LINK_ULONG:
	    changed = (LinkedVar(unsigned long) != linkPtr->lastValue.ul);
	    break;
	case TCL_LINK_FLOAT:
	    changed = (LinkedVar(float) != linkPtr->lastValue.f);
	    break;
	case TCL_LINK_STRING:
	    changed = 1;
	    break;
	default:
	    return "internal error: bad linked variable type";
	}
	if (changed) {
	    Tcl_ObjSetVar2(interp, linkPtr->varName, NULL, ObjValue(linkPtr),
		    TCL_GLOBAL_ONLY);
	}
	return NULL;
    }

    /*
     * For writes, first make sure that the variable is writable. Then convert
     * the Tcl value to C if possible. If the variable isn't writable or can't
     * be converted, then restore the varaible's old value and return an
     * error. Another tricky thing: we have to save and restore the interp's
     * result, since the variable access could occur when the result has been
     * partially set.
     */

    if (linkPtr->flags & LINK_READ_ONLY) {
	Tcl_ObjSetVar2(interp, linkPtr->varName, NULL, ObjValue(linkPtr),
		TCL_GLOBAL_ONLY);
	return "linked variable is read-only";
    }
    valueObj = Tcl_ObjGetVar2(interp, linkPtr->varName,NULL, TCL_GLOBAL_ONLY);
    if (valueObj == NULL) {
	/*
	 * This shouldn't ever happen.
	 */

	return "internal error: linked variable couldn't be read";
    }

    switch (linkPtr->type) {
    case TCL_LINK_INT:
	if (Tcl_GetIntFromObj(NULL, valueObj, &linkPtr->lastValue.i)
		!= TCL_OK) {
	    Tcl_ObjSetVar2(interp, linkPtr->varName, NULL, ObjValue(linkPtr),
		    TCL_GLOBAL_ONLY);
	    return "variable must have integer value";
	}
	LinkedVar(int) = linkPtr->lastValue.i;
	break;

    case TCL_LINK_WIDE_INT:
	if (Tcl_GetWideIntFromObj(NULL, valueObj, &linkPtr->lastValue.w)
		!= TCL_OK) {
	    Tcl_ObjSetVar2(interp, linkPtr->varName, NULL, ObjValue(linkPtr),
		    TCL_GLOBAL_ONLY);
	    return "variable must have integer value";
	}
	LinkedVar(Tcl_WideInt) = linkPtr->lastValue.w;
	break;

    case TCL_LINK_DOUBLE:
	if (Tcl_GetDoubleFromObj(NULL, valueObj, &linkPtr->lastValue.d)
		!= TCL_OK) {
#ifdef ACCEPT_NAN
	    if (valueObj->typePtr != &tclDoubleType) {
#endif
		Tcl_ObjSetVar2(interp, linkPtr->varName, NULL,
			ObjValue(linkPtr), TCL_GLOBAL_ONLY);
		return "variable must have real value";
#ifdef ACCEPT_NAN
	    }
	    linkPtr->lastValue.d = valueObj->internalRep.doubleValue;
#endif
	}
	LinkedVar(double) = linkPtr->lastValue.d;
	break;

    case TCL_LINK_BOOLEAN:
	if (Tcl_GetBooleanFromObj(NULL, valueObj, &linkPtr->lastValue.i)
		!= TCL_OK) {
	    Tcl_ObjSetVar2(interp, linkPtr->varName, NULL, ObjValue(linkPtr),
		    TCL_GLOBAL_ONLY);
	    return "variable must have boolean value";
	}
	LinkedVar(int) = linkPtr->lastValue.i;
	break;

    case TCL_LINK_CHAR:
	if (Tcl_GetIntFromObj(interp, valueObj, &valueInt) != TCL_OK
		|| valueInt < SCHAR_MIN || valueInt > SCHAR_MAX) {
	    Tcl_ObjSetVar2(interp, linkPtr->varName, NULL, ObjValue(linkPtr),
		    TCL_GLOBAL_ONLY);
	    return "variable must have char value";
	}
	linkPtr->lastValue.c = (char)valueInt;
	LinkedVar(char) = linkPtr->lastValue.c;
	break;

    case TCL_LINK_UCHAR:
	if (Tcl_GetIntFromObj(interp, valueObj, &valueInt) != TCL_OK
		|| valueInt < 0 || valueInt > UCHAR_MAX) {
	    Tcl_ObjSetVar2(interp, linkPtr->varName, NULL, ObjValue(linkPtr),
		    TCL_GLOBAL_ONLY);
	    return "variable must have unsigned char value";
	}
	linkPtr->lastValue.uc = (unsigned char) valueInt;
	LinkedVar(unsigned char) = linkPtr->lastValue.uc;
	break;

    case TCL_LINK_SHORT:
	if (Tcl_GetIntFromObj(interp, valueObj, &valueInt) != TCL_OK
		|| valueInt < SHRT_MIN || valueInt > SHRT_MAX) {
	    Tcl_ObjSetVar2(interp, linkPtr->varName, NULL, ObjValue(linkPtr),
		    TCL_GLOBAL_ONLY);
	    return "variable must have short value";
	}
	linkPtr->lastValue.s = (short)valueInt;
	LinkedVar(short) = linkPtr->lastValue.s;
	break;

    case TCL_LINK_USHORT:
	if (Tcl_GetIntFromObj(interp, valueObj, &valueInt) != TCL_OK
		|| valueInt < 0 || valueInt > USHRT_MAX) {
	    Tcl_ObjSetVar2(interp, linkPtr->varName, NULL, ObjValue(linkPtr),
		    TCL_GLOBAL_ONLY);
	    return "variable must have unsigned short value";
	}
	linkPtr->lastValue.us = (unsigned short)valueInt;
	LinkedVar(unsigned short) = linkPtr->lastValue.us;
	break;

    case TCL_LINK_UINT:
	if (Tcl_GetWideIntFromObj(interp, valueObj, &valueWide) != TCL_OK
		|| valueWide < 0 || valueWide > UINT_MAX) {
	    Tcl_ObjSetVar2(interp, linkPtr->varName, NULL, ObjValue(linkPtr),
		    TCL_GLOBAL_ONLY);
	    return "variable must have unsigned int value";
	}
	linkPtr->lastValue.ui = (unsigned int)valueWide;
	LinkedVar(unsigned int) = linkPtr->lastValue.ui;
	break;

    case TCL_LINK_LONG:
	if (Tcl_GetWideIntFromObj(interp, valueObj, &valueWide) != TCL_OK
		|| valueWide < LONG_MIN || valueWide > LONG_MAX) {
	    Tcl_ObjSetVar2(interp, linkPtr->varName, NULL, ObjValue(linkPtr),
		    TCL_GLOBAL_ONLY);
	    return "variable must have long value";
	}
	linkPtr->lastValue.l = (long)valueWide;
	LinkedVar(long) = linkPtr->lastValue.l;
	break;

    case TCL_LINK_ULONG:
	if (Tcl_GetWideIntFromObj(interp, valueObj, &valueWide) != TCL_OK
		|| valueWide < 0 || (Tcl_WideUInt) valueWide > ULONG_MAX) {
	    Tcl_ObjSetVar2(interp, linkPtr->varName, NULL, ObjValue(linkPtr),
		    TCL_GLOBAL_ONLY);
	    return "variable must have unsigned long value";
	}
	linkPtr->lastValue.ul = (unsigned long)valueWide;
	LinkedVar(unsigned long) = linkPtr->lastValue.ul;
	break;

    case TCL_LINK_WIDE_UINT:
	/*
	 * FIXME: represent as a bignum.
	 */
	if (Tcl_GetWideIntFromObj(interp, valueObj, &valueWide) != TCL_OK) {
	    Tcl_ObjSetVar2(interp, linkPtr->varName, NULL, ObjValue(linkPtr),
		    TCL_GLOBAL_ONLY);
	    return "variable must have unsigned wide int value";
	}
	linkPtr->lastValue.uw = (Tcl_WideUInt)valueWide;
	LinkedVar(Tcl_WideUInt) = linkPtr->lastValue.uw;
	break;

    case TCL_LINK_FLOAT:
	if (Tcl_GetDoubleFromObj(interp, valueObj, &valueDouble) != TCL_OK
		|| valueDouble < -FLT_MAX || valueDouble > FLT_MAX) {
	    Tcl_ObjSetVar2(interp, linkPtr->varName, NULL, ObjValue(linkPtr),
		    TCL_GLOBAL_ONLY);
	    return "variable must have float value";
	}
	linkPtr->lastValue.f = (float)valueDouble;
	LinkedVar(float) = linkPtr->lastValue.f;
	break;

    case TCL_LINK_STRING:
	value = Tcl_GetStringFromObj(valueObj, &valueLength);
	valueLength++;
	pp = (char **) linkPtr->addr;

	*pp = ckrealloc(*pp, valueLength);
	memcpy(*pp, value, (unsigned) valueLength);
	break;

    default:
	return "internal error: bad linked variable type";
    }
    return NULL;
}

/*
 *----------------------------------------------------------------------
 *
 * ObjValue --
 *
 *	Converts the value of a C variable to a Tcl_Obj* for use in a Tcl
 *	variable to which it is linked.
 *
 * Results:
 *	The return value is a pointer to a Tcl_Obj that represents the value
 *	of the C variable given by linkPtr.
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */

static Tcl_Obj *
ObjValue(
    Link *linkPtr)		/* Structure describing linked variable. */
{
    char *p;
    Tcl_Obj *resultObj;

    switch (linkPtr->type) {
    case TCL_LINK_INT:
	linkPtr->lastValue.i = LinkedVar(int);
	return Tcl_NewIntObj(linkPtr->lastValue.i);
    case TCL_LINK_WIDE_INT:
	linkPtr->lastValue.w = LinkedVar(Tcl_WideInt);
	return Tcl_NewWideIntObj(linkPtr->lastValue.w);
    case TCL_LINK_DOUBLE:
	linkPtr->lastValue.d = LinkedVar(double);
	return Tcl_NewDoubleObj(linkPtr->lastValue.d);
    case TCL_LINK_BOOLEAN:
	linkPtr->lastValue.i = LinkedVar(int);
	return Tcl_NewBooleanObj(linkPtr->lastValue.i != 0);
    case TCL_LINK_CHAR:
	linkPtr->lastValue.c = LinkedVar(char);
	return Tcl_NewIntObj(linkPtr->lastValue.c);
    case TCL_LINK_UCHAR:
	linkPtr->lastValue.uc = LinkedVar(unsigned char);
	return Tcl_NewIntObj(linkPtr->lastValue.uc);
    case TCL_LINK_SHORT:
	linkPtr->lastValue.s = LinkedVar(short);
	return Tcl_NewIntObj(linkPtr->lastValue.s);
    case TCL_LINK_USHORT:
	linkPtr->lastValue.us = LinkedVar(unsigned short);
	return Tcl_NewIntObj(linkPtr->lastValue.us);
    case TCL_LINK_UINT:
	linkPtr->lastValue.ui = LinkedVar(unsigned int);
	return Tcl_NewWideIntObj((Tcl_WideInt) linkPtr->lastValue.ui);
    case TCL_LINK_LONG:
	linkPtr->lastValue.l = LinkedVar(long);
	return Tcl_NewWideIntObj((Tcl_WideInt) linkPtr->lastValue.l);
    case TCL_LINK_ULONG:
	linkPtr->lastValue.ul = LinkedVar(unsigned long);
	return Tcl_NewWideIntObj((Tcl_WideInt) linkPtr->lastValue.ul);
    case TCL_LINK_FLOAT:
	linkPtr->lastValue.f = LinkedVar(float);
	return Tcl_NewDoubleObj(linkPtr->lastValue.f);
    case TCL_LINK_WIDE_UINT:
	linkPtr->lastValue.uw = LinkedVar(Tcl_WideUInt);
	/*
	 * FIXME: represent as a bignum.
	 */
	return Tcl_NewWideIntObj((Tcl_WideInt) linkPtr->lastValue.uw);
    case TCL_LINK_STRING:
	p = LinkedVar(char *);
	if (p == NULL) {
	    TclNewLiteralStringObj(resultObj, "NULL");
	    return resultObj;
	}
	return Tcl_NewStringObj(p, -1);

    /*
     * This code only gets executed if the link type is unknown (shouldn't
     * ever happen).
     */

    default:
	TclNewLiteralStringObj(resultObj, "??");
	return resultObj;
    }
}

/*
 * Local Variables:
 * mode: c
 * c-basic-offset: 4
 * fill-column: 78
 * End:
 */
