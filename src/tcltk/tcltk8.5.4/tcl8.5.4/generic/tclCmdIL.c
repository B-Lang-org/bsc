/*
 * tclCmdIL.c --
 *
 *	This file contains the top-level command routines for most of the Tcl
 *	built-in commands whose names begin with the letters I through L. It
 *	contains only commands in the generic core (i.e. those that don't
 *	depend much upon UNIX facilities).
 *
 * Copyright (c) 1987-1993 The Regents of the University of California.
 * Copyright (c) 1993-1997 Lucent Technologies.
 * Copyright (c) 1994-1997 Sun Microsystems, Inc.
 * Copyright (c) 1998-1999 by Scriptics Corporation.
 * Copyright (c) 2001 by Kevin B. Kenny. All rights reserved.
 * Copyright (c) 2005 Donal K. Fellows.
 *
 * See the file "license.terms" for information on usage and redistribution of
 * this file, and for a DISCLAIMER OF ALL WARRANTIES.
 *
 * RCS: @(#) $Id: tclCmdIL.c,v 1.137.2.4 2008/08/14 02:09:55 das Exp $
 */

#include "tclInt.h"
#include "tclRegexp.h"

/*
 * During execution of the "lsort" command, structures of the following type
 * are used to arrange the objects being sorted into a collection of linked
 * lists.
 */

typedef struct SortElement {
    union {
	char *strValuePtr;
	long   intValue;
	double doubleValue;
	Tcl_Obj *objValuePtr;
    } index;
    Tcl_Obj *objPtr;	        /* Object being sorted, or its index. */
    struct SortElement *nextPtr;/* Next element in the list, or NULL for end
				 * of list. */
} SortElement;

/*
 * These function pointer types are used with the "lsearch" and "lsort"
 * commands to facilitate the "-nocase" option.
 */

typedef int (*SortStrCmpFn_t) (const char *, const char *);
typedef int (*SortMemCmpFn_t) (const void *, const void *, size_t);

/*
 * The "lsort" command needs to pass certain information down to the function
 * that compares two list elements, and the comparison function needs to pass
 * success or failure information back up to the top-level "lsort" command.
 * The following structure is used to pass this information.
 */

typedef struct SortInfo {
    int isIncreasing;		/* Nonzero means sort in increasing order. */
    int sortMode;		/* The sort mode. One of SORTMODE_* values
				 * defined below. */
    Tcl_Obj *compareCmdPtr;	/* The Tcl comparison command when sortMode is
				 * SORTMODE_COMMAND. Pre-initialized to hold
				 * base of command. */
    int *indexv;		/* If the -index option was specified, this
				 * holds the indexes contained in the list
				 * supplied as an argument to that option.
				 * NULL if no indexes supplied, and points to
				 * singleIndex field when only one
				 * supplied. */
    int indexc;			/* Number of indexes in indexv array. */
    int singleIndex;		/* Static space for common index case. */
    int unique;
    int numElements;
    Tcl_Interp *interp;		/* The interpreter in which the sort is being
				 * done. */
    int resultCode;		/* Completion code for the lsort command. If
				 * an error occurs during the sort this is
				 * changed from TCL_OK to TCL_ERROR. */
} SortInfo;

/*
 * The "sortMode" field of the SortInfo structure can take on any of the
 * following values.
 */

#define SORTMODE_ASCII		0
#define SORTMODE_INTEGER	1
#define SORTMODE_REAL		2
#define SORTMODE_COMMAND	3
#define SORTMODE_DICTIONARY	4
#define SORTMODE_ASCII_NC	8

/*
 * Magic values for the index field of the SortInfo structure. Note that the
 * index "end-1" will be translated to SORTIDX_END-1, etc.
 */

#define SORTIDX_NONE	-1	/* Not indexed; use whole value. */
#define SORTIDX_END	-2	/* Indexed from end. */

/*
 * Forward declarations for procedures defined in this file:
 */

static int		DictionaryCompare(char *left, char *right);
static int		InfoArgsCmd(ClientData dummy, Tcl_Interp *interp,
			    int objc, Tcl_Obj *CONST objv[]);
static int		InfoBodyCmd(ClientData dummy, Tcl_Interp *interp,
			    int objc, Tcl_Obj *CONST objv[]);
static int		InfoCmdCountCmd(ClientData dummy, Tcl_Interp *interp,
			    int objc, Tcl_Obj *CONST objv[]);
static int		InfoCommandsCmd(ClientData dummy, Tcl_Interp *interp,
			    int objc, Tcl_Obj *CONST objv[]);
static int		InfoCompleteCmd(ClientData dummy, Tcl_Interp *interp,
			    int objc, Tcl_Obj *CONST objv[]);
static int		InfoDefaultCmd(ClientData dummy, Tcl_Interp *interp,
			    int objc, Tcl_Obj *CONST objv[]);
/* TIP #280 - New 'info' subcommand 'frame' */
static int		InfoFrameCmd(ClientData dummy, Tcl_Interp *interp,
			    int objc, Tcl_Obj *CONST objv[]);
static int		InfoFunctionsCmd(ClientData dummy, Tcl_Interp *interp,
			    int objc, Tcl_Obj *CONST objv[]);
static int		InfoHostnameCmd(ClientData dummy, Tcl_Interp *interp,
			    int objc, Tcl_Obj *CONST objv[]);
static int		InfoLevelCmd(ClientData dummy, Tcl_Interp *interp,
			    int objc, Tcl_Obj *CONST objv[]);
static int		InfoLibraryCmd(ClientData dummy, Tcl_Interp *interp,
			    int objc, Tcl_Obj *CONST objv[]);
static int		InfoLoadedCmd(ClientData dummy, Tcl_Interp *interp,
			    int objc, Tcl_Obj *CONST objv[]);
static int		InfoNameOfExecutableCmd(ClientData dummy,
			    Tcl_Interp *interp, int objc,
			    Tcl_Obj *CONST objv[]);
static int		InfoPatchLevelCmd(ClientData dummy, Tcl_Interp *interp,
			    int objc, Tcl_Obj *CONST objv[]);
static int		InfoProcsCmd(ClientData dummy, Tcl_Interp *interp,
			    int objc, Tcl_Obj *CONST objv[]);
static int		InfoScriptCmd(ClientData dummy, Tcl_Interp *interp,
			    int objc, Tcl_Obj *CONST objv[]);
static int		InfoSharedlibCmd(ClientData dummy, Tcl_Interp *interp,
			    int objc, Tcl_Obj *CONST objv[]);
static int		InfoTclVersionCmd(ClientData dummy, Tcl_Interp *interp,
			    int objc, Tcl_Obj *CONST objv[]);
static SortElement *    MergeLists(SortElement *leftPtr, SortElement *rightPtr,
			    SortInfo *infoPtr);
static int		SortCompare(SortElement *firstPtr, SortElement *second,
			    SortInfo *infoPtr);
static Tcl_Obj *	SelectObjFromSublist(Tcl_Obj *firstPtr,
			    SortInfo *infoPtr);

/*
 * Array of values describing how to implement each standard subcommand of the
 * "info" command.
 */

static const EnsembleImplMap defaultInfoMap[] = {
    {"args",		   InfoArgsCmd,		    NULL},
    {"body",		   InfoBodyCmd,		    NULL},
    {"cmdcount",	   InfoCmdCountCmd,	    NULL},
    {"commands",	   InfoCommandsCmd,	    NULL},
    {"complete",	   InfoCompleteCmd,	    NULL},
    {"default",		   InfoDefaultCmd,	    NULL},
    {"exists",		   TclInfoExistsCmd,	    TclCompileInfoExistsCmd},
    {"frame",		   InfoFrameCmd,	    NULL},
    {"functions",	   InfoFunctionsCmd,	    NULL},
    {"globals",		   TclInfoGlobalsCmd,	    NULL},
    {"hostname",	   InfoHostnameCmd,	    NULL},
    {"level",		   InfoLevelCmd,	    NULL},
    {"library",		   InfoLibraryCmd,	    NULL},
    {"loaded",		   InfoLoadedCmd,	    NULL},
    {"locals",		   TclInfoLocalsCmd,	    NULL},
    {"nameofexecutable",   InfoNameOfExecutableCmd, NULL},
    {"patchlevel",	   InfoPatchLevelCmd,	    NULL},
    {"procs",		   InfoProcsCmd,	    NULL},
    {"script",		   InfoScriptCmd,	    NULL},
    {"sharedlibextension", InfoSharedlibCmd,	    NULL},
    {"tclversion",	   InfoTclVersionCmd,	    NULL},
    {"vars",		   TclInfoVarsCmd,	    NULL},
    {NULL, NULL, NULL}
};

/*
 *----------------------------------------------------------------------
 *
 * Tcl_IfObjCmd --
 *
 *	This procedure is invoked to process the "if" Tcl command. See the
 *	user documentation for details on what it does.
 *
 *	With the bytecode compiler, this procedure is only called when a
 *	command name is computed at runtime, and is "if" or the name to which
 *	"if" was renamed: e.g., "set z if; $z 1 {puts foo}"
 *
 * Results:
 *	A standard Tcl result.
 *
 * Side effects:
 *	See the user documentation.
 *
 *----------------------------------------------------------------------
 */

int
Tcl_IfObjCmd(
    ClientData dummy,		/* Not used. */
    Tcl_Interp *interp,		/* Current interpreter. */
    int objc,			/* Number of arguments. */
    Tcl_Obj *CONST objv[])	/* Argument objects. */
{
    int thenScriptIndex = 0;	/* "then" script to be evaled after syntax
				 * check. */
    Interp *iPtr = (Interp *) interp;
    int i, result, value;
    char *clause;

    i = 1;
    while (1) {
	/*
	 * At this point in the loop, objv and objc refer to an expression to
	 * test, either for the main expression or an expression following an
	 * "elseif". The arguments after the expression must be "then"
	 * (optional) and a script to execute if the expression is true.
	 */

	if (i >= objc) {
	    clause = TclGetString(objv[i-1]);
	    Tcl_AppendResult(interp, "wrong # args: ",
		    "no expression after \"", clause, "\" argument", NULL);
	    return TCL_ERROR;
	}
	if (!thenScriptIndex) {
	    result = Tcl_ExprBooleanObj(interp, objv[i], &value);
	    if (result != TCL_OK) {
		return result;
	    }
	}
	i++;
	if (i >= objc) {
	missingScript:
	    clause = TclGetString(objv[i-1]);
	    Tcl_AppendResult(interp, "wrong # args: ",
		    "no script following \"", clause, "\" argument", NULL);
	    return TCL_ERROR;
	}
	clause = TclGetString(objv[i]);
	if ((i < objc) && (strcmp(clause, "then") == 0)) {
	    i++;
	}
	if (i >= objc) {
	    goto missingScript;
	}
	if (value) {
	    thenScriptIndex = i;
	    value = 0;
	}

	/*
	 * The expression evaluated to false. Skip the command, then see if
	 * there is an "else" or "elseif" clause.
	 */

	i++;
	if (i >= objc) {
	    if (thenScriptIndex) {
		/*
		 * TIP #280. Make invoking context available to branch.
		 */

		return TclEvalObjEx(interp, objv[thenScriptIndex], 0,
			iPtr->cmdFramePtr, thenScriptIndex);
	    }
	    return TCL_OK;
	}
	clause = TclGetString(objv[i]);
	if ((clause[0] == 'e') && (strcmp(clause, "elseif") == 0)) {
	    i++;
	    continue;
	}
	break;
    }

    /*
     * Couldn't find a "then" or "elseif" clause to execute. Check now for an
     * "else" clause. We know that there's at least one more argument when we
     * get here.
     */

    if (strcmp(clause, "else") == 0) {
	i++;
	if (i >= objc) {
	    Tcl_AppendResult(interp, "wrong # args: ",
		    "no script following \"else\" argument", NULL);
	    return TCL_ERROR;
	}
    }
    if (i < objc - 1) {
	Tcl_AppendResult(interp, "wrong # args: ",
		"extra words after \"else\" clause in \"if\" command", NULL);
	return TCL_ERROR;
    }
    if (thenScriptIndex) {
	/*
	 * TIP #280. Make invoking context available to branch/else.
	 */

	return TclEvalObjEx(interp, objv[thenScriptIndex], 0,
		iPtr->cmdFramePtr, thenScriptIndex);
    }
    return TclEvalObjEx(interp, objv[i], 0, iPtr->cmdFramePtr, i);
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_IncrObjCmd --
 *
 *	This procedure is invoked to process the "incr" Tcl command. See the
 *	user documentation for details on what it does.
 *
 *	With the bytecode compiler, this procedure is only called when a
 *	command name is computed at runtime, and is "incr" or the name to
 *	which "incr" was renamed: e.g., "set z incr; $z i -1"
 *
 * Results:
 *	A standard Tcl result.
 *
 * Side effects:
 *	See the user documentation.
 *
 *----------------------------------------------------------------------
 */

int
Tcl_IncrObjCmd(
    ClientData dummy,		/* Not used. */
    Tcl_Interp *interp,		/* Current interpreter. */
    int objc,			/* Number of arguments. */
    Tcl_Obj *CONST objv[])	/* Argument objects. */
{
    Tcl_Obj *newValuePtr, *incrPtr;

    if ((objc != 2) && (objc != 3)) {
	Tcl_WrongNumArgs(interp, 1, objv, "varName ?increment?");
	return TCL_ERROR;
    }

    if (objc == 3) {
	incrPtr = objv[2];
    } else {
	incrPtr = Tcl_NewIntObj(1);
    }
    Tcl_IncrRefCount(incrPtr);
    newValuePtr = TclIncrObjVar2(interp, objv[1], NULL,
	    incrPtr, TCL_LEAVE_ERR_MSG);
    Tcl_DecrRefCount(incrPtr);

    if (newValuePtr == NULL) {
	return TCL_ERROR;
    }

    /*
     * Set the interpreter's object result to refer to the variable's new
     * value object.
     */

    Tcl_SetObjResult(interp, newValuePtr);
    return TCL_OK;
}

/*
 *----------------------------------------------------------------------
 *
 * TclInitInfoCmd --
 *
 *	This function is called to create the "info" Tcl command. See the user
 *	documentation for details on what it does.
 *
 * Results:
 *	FIXME
 *
 * Side effects:
 *	none
 *
 *----------------------------------------------------------------------
 */

Tcl_Command
TclInitInfoCmd(
    Tcl_Interp *interp)		/* Current interpreter. */
{
    return TclMakeEnsemble(interp, "info", defaultInfoMap);
}

/*
 *----------------------------------------------------------------------
 *
 * InfoArgsCmd --
 *
 *	Called to implement the "info args" command that returns the argument
 *	list for a procedure. Handles the following syntax:
 *
 *	    info args procName
 *
 * Results:
 *	Returns TCL_OK if successful and TCL_ERROR if there is an error.
 *
 * Side effects:
 *	Returns a result in the interpreter's result object. If there is an
 *	error, the result is an error message.
 *
 *----------------------------------------------------------------------
 */

static int
InfoArgsCmd(
    ClientData dummy,		/* Not used. */
    Tcl_Interp *interp,		/* Current interpreter. */
    int objc,			/* Number of arguments. */
    Tcl_Obj *CONST objv[])	/* Argument objects. */
{
    register Interp *iPtr = (Interp *) interp;
    char *name;
    Proc *procPtr;
    CompiledLocal *localPtr;
    Tcl_Obj *listObjPtr;

    if (objc != 2) {
	Tcl_WrongNumArgs(interp, 1, objv, "procname");
	return TCL_ERROR;
    }

    name = TclGetString(objv[1]);
    procPtr = TclFindProc(iPtr, name);
    if (procPtr == NULL) {
	Tcl_AppendResult(interp, "\"", name, "\" isn't a procedure", NULL);
	return TCL_ERROR;
    }

    /*
     * Build a return list containing the arguments.
     */

    listObjPtr = Tcl_NewListObj(0, NULL);
    for (localPtr = procPtr->firstLocalPtr;  localPtr != NULL;
	    localPtr = localPtr->nextPtr) {
	if (TclIsVarArgument(localPtr)) {
	    Tcl_ListObjAppendElement(interp, listObjPtr,
		    Tcl_NewStringObj(localPtr->name, -1));
	}
    }
    Tcl_SetObjResult(interp, listObjPtr);
    return TCL_OK;
}

/*
 *----------------------------------------------------------------------
 *
 * InfoBodyCmd --
 *
 *	Called to implement the "info body" command that returns the body for
 *	a procedure. Handles the following syntax:
 *
 *	    info body procName
 *
 * Results:
 *	Returns TCL_OK if successful and TCL_ERROR if there is an error.
 *
 * Side effects:
 *	Returns a result in the interpreter's result object. If there is an
 *	error, the result is an error message.
 *
 *----------------------------------------------------------------------
 */

static int
InfoBodyCmd(
    ClientData dummy,		/* Not used. */
    Tcl_Interp *interp,		/* Current interpreter. */
    int objc,			/* Number of arguments. */
    Tcl_Obj *CONST objv[])	/* Argument objects. */
{
    register Interp *iPtr = (Interp *) interp;
    char *name;
    Proc *procPtr;
    Tcl_Obj *bodyPtr, *resultPtr;

    if (objc != 2) {
	Tcl_WrongNumArgs(interp, 1, objv, "procname");
	return TCL_ERROR;
    }

    name = TclGetString(objv[1]);
    procPtr = TclFindProc(iPtr, name);
    if (procPtr == NULL) {
	Tcl_AppendResult(interp, "\"", name, "\" isn't a procedure", NULL);
	return TCL_ERROR;
    }

    /*
     * Here we used to return procPtr->bodyPtr, except when the body was
     * bytecompiled - in that case, the return was a copy of the body's string
     * rep. In order to better isolate the implementation details of the
     * compiler/engine subsystem, we now always return a copy of the string
     * rep. It is important to return a copy so that later manipulations of
     * the object do not invalidate the internal rep.
     */

    bodyPtr = procPtr->bodyPtr;
    if (bodyPtr->bytes == NULL) {
	/*
	 * The string rep might not be valid if the procedure has never been
	 * run before. [Bug #545644]
	 */

	(void) TclGetString(bodyPtr);
    }
    resultPtr = Tcl_NewStringObj(bodyPtr->bytes, bodyPtr->length);

    Tcl_SetObjResult(interp, resultPtr);
    return TCL_OK;
}

/*
 *----------------------------------------------------------------------
 *
 * InfoCmdCountCmd --
 *
 *	Called to implement the "info cmdcount" command that returns the
 *	number of commands that have been executed. Handles the following
 *	syntax:
 *
 *	    info cmdcount
 *
 * Results:
 *	Returns TCL_OK if successful and TCL_ERROR if there is an error.
 *
 * Side effects:
 *	Returns a result in the interpreter's result object. If there is an
 *	error, the result is an error message.
 *
 *----------------------------------------------------------------------
 */

static int
InfoCmdCountCmd(
    ClientData dummy,		/* Not used. */
    Tcl_Interp *interp,		/* Current interpreter. */
    int objc,			/* Number of arguments. */
    Tcl_Obj *CONST objv[])	/* Argument objects. */
{
    Interp *iPtr = (Interp *) interp;

    if (objc != 1) {
	Tcl_WrongNumArgs(interp, 1, objv, NULL);
	return TCL_ERROR;
    }

    Tcl_SetObjResult(interp, Tcl_NewIntObj(iPtr->cmdCount));
    return TCL_OK;
}

/*
 *----------------------------------------------------------------------
 *
 * InfoCommandsCmd --
 *
 *	Called to implement the "info commands" command that returns the list
 *	of commands in the interpreter that match an optional pattern. The
 *	pattern, if any, consists of an optional sequence of namespace names
 *	separated by "::" qualifiers, which is followed by a glob-style
 *	pattern that restricts which commands are returned. Handles the
 *	following syntax:
 *
 *	    info commands ?pattern?
 *
 * Results:
 *	Returns TCL_OK if successful and TCL_ERROR if there is an error.
 *
 * Side effects:
 *	Returns a result in the interpreter's result object. If there is an
 *	error, the result is an error message.
 *
 *----------------------------------------------------------------------
 */

static int
InfoCommandsCmd(
    ClientData dummy,		/* Not used. */
    Tcl_Interp *interp,		/* Current interpreter. */
    int objc,			/* Number of arguments. */
    Tcl_Obj *CONST objv[])	/* Argument objects. */
{
    char *cmdName, *pattern;
    CONST char *simplePattern;
    register Tcl_HashEntry *entryPtr;
    Tcl_HashSearch search;
    Namespace *nsPtr;
    Namespace *globalNsPtr = (Namespace *) Tcl_GetGlobalNamespace(interp);
    Namespace *currNsPtr = (Namespace *) Tcl_GetCurrentNamespace(interp);
    Tcl_Obj *listPtr, *elemObjPtr;
    int specificNsInPattern = 0;/* Init. to avoid compiler warning. */
    Tcl_Command cmd;
    int i;

    /*
     * Get the pattern and find the "effective namespace" in which to list
     * commands.
     */

    if (objc == 1) {
	simplePattern = NULL;
	nsPtr = currNsPtr;
	specificNsInPattern = 0;
    } else if (objc == 2) {
	/*
	 * From the pattern, get the effective namespace and the simple
	 * pattern (no namespace qualifiers or ::'s) at the end. If an error
	 * was found while parsing the pattern, return it. Otherwise, if the
	 * namespace wasn't found, just leave nsPtr NULL: we will return an
	 * empty list since no commands there can be found.
	 */

	Namespace *dummy1NsPtr, *dummy2NsPtr;

	pattern = TclGetString(objv[1]);
	TclGetNamespaceForQualName(interp, pattern, (Namespace *) NULL, 0,
		&nsPtr, &dummy1NsPtr, &dummy2NsPtr, &simplePattern);

	if (nsPtr != NULL) {	/* We successfully found the pattern's ns. */
	    specificNsInPattern = (strcmp(simplePattern, pattern) != 0);
	}
    } else {
	Tcl_WrongNumArgs(interp, 1, objv, "?pattern?");
	return TCL_ERROR;
    }

    /*
     * Exit as quickly as possible if we couldn't find the namespace.
     */

    if (nsPtr == NULL) {
	return TCL_OK;
    }

    /*
     * Scan through the effective namespace's command table and create a list
     * with all commands that match the pattern. If a specific namespace was
     * requested in the pattern, qualify the command names with the namespace
     * name.
     */

    listPtr = Tcl_NewListObj(0, NULL);

    if (simplePattern != NULL && TclMatchIsTrivial(simplePattern)) {
	/*
	 * Special case for when the pattern doesn't include any of glob's
	 * special characters. This lets us avoid scans of any hash tables.
	 */

	entryPtr = Tcl_FindHashEntry(&nsPtr->cmdTable, simplePattern);
	if (entryPtr != NULL) {
	    if (specificNsInPattern) {
		cmd = (Tcl_Command) Tcl_GetHashValue(entryPtr);
		elemObjPtr = Tcl_NewObj();
		Tcl_GetCommandFullName(interp, cmd, elemObjPtr);
	    } else {
		cmdName = Tcl_GetHashKey(&nsPtr->cmdTable, entryPtr);
		elemObjPtr = Tcl_NewStringObj(cmdName, -1);
	    }
	    Tcl_ListObjAppendElement(interp, listPtr, elemObjPtr);
	    Tcl_SetObjResult(interp, listPtr);
	    return TCL_OK;
	}
	if ((nsPtr != globalNsPtr) && !specificNsInPattern) {
	    Tcl_HashTable *tablePtr = NULL;	/* Quell warning. */

	    for (i=0 ; i<nsPtr->commandPathLength ; i++) {
		Namespace *pathNsPtr = nsPtr->commandPathArray[i].nsPtr;

		if (pathNsPtr == NULL) {
		    continue;
		}
		tablePtr = &pathNsPtr->cmdTable;
		entryPtr = Tcl_FindHashEntry(tablePtr, simplePattern);
		if (entryPtr != NULL) {
		    break;
		}
	    }
	    if (entryPtr == NULL) {
		tablePtr = &globalNsPtr->cmdTable;
		entryPtr = Tcl_FindHashEntry(tablePtr, simplePattern);
	    }
	    if (entryPtr != NULL) {
		cmdName = Tcl_GetHashKey(tablePtr, entryPtr);
		Tcl_ListObjAppendElement(interp, listPtr,
			Tcl_NewStringObj(cmdName, -1));
		Tcl_SetObjResult(interp, listPtr);
		return TCL_OK;
	    }
	}
    } else if (nsPtr->commandPathLength == 0 || specificNsInPattern) {
	/*
	 * The pattern is non-trivial, but either there is no explicit path or
	 * there is an explicit namespace in the pattern. In both cases, the
	 * old matching scheme is perfect.
	 */

	entryPtr = Tcl_FirstHashEntry(&nsPtr->cmdTable, &search);
	while (entryPtr != NULL) {
	    cmdName = Tcl_GetHashKey(&nsPtr->cmdTable, entryPtr);
	    if ((simplePattern == NULL)
		    || Tcl_StringMatch(cmdName, simplePattern)) {
		if (specificNsInPattern) {
		    cmd = (Tcl_Command) Tcl_GetHashValue(entryPtr);
		    elemObjPtr = Tcl_NewObj();
		    Tcl_GetCommandFullName(interp, cmd, elemObjPtr);
		} else {
		    elemObjPtr = Tcl_NewStringObj(cmdName, -1);
		}
		Tcl_ListObjAppendElement(interp, listPtr, elemObjPtr);
	    }
	    entryPtr = Tcl_NextHashEntry(&search);
	}

	/*
	 * If the effective namespace isn't the global :: namespace, and a
	 * specific namespace wasn't requested in the pattern, then add in all
	 * global :: commands that match the simple pattern. Of course, we add
	 * in only those commands that aren't hidden by a command in the
	 * effective namespace.
	 */

	if ((nsPtr != globalNsPtr) && !specificNsInPattern) {
	    entryPtr = Tcl_FirstHashEntry(&globalNsPtr->cmdTable, &search);
	    while (entryPtr != NULL) {
		cmdName = Tcl_GetHashKey(&globalNsPtr->cmdTable, entryPtr);
		if ((simplePattern == NULL)
			|| Tcl_StringMatch(cmdName, simplePattern)) {
		    if (Tcl_FindHashEntry(&nsPtr->cmdTable,cmdName) == NULL) {
			Tcl_ListObjAppendElement(interp, listPtr,
				Tcl_NewStringObj(cmdName, -1));
		    }
		}
		entryPtr = Tcl_NextHashEntry(&search);
	    }
	}
    } else {
	/*
	 * The pattern is non-trivial (can match more than one command name),
	 * there is an explicit path, and there is no explicit namespace in
	 * the pattern. This means that we have to traverse the path to
	 * discover all the commands defined.
	 */

	Tcl_HashTable addedCommandsTable;
	int isNew;
	int foundGlobal = (nsPtr == globalNsPtr);

	/*
	 * We keep a hash of the objects already added to the result list.
	 */

	Tcl_InitObjHashTable(&addedCommandsTable);

	entryPtr = Tcl_FirstHashEntry(&nsPtr->cmdTable, &search);
	while (entryPtr != NULL) {
	    cmdName = Tcl_GetHashKey(&nsPtr->cmdTable, entryPtr);
	    if ((simplePattern == NULL)
		    || Tcl_StringMatch(cmdName, simplePattern)) {
		elemObjPtr = Tcl_NewStringObj(cmdName, -1);
		Tcl_ListObjAppendElement(interp, listPtr, elemObjPtr);
		(void) Tcl_CreateHashEntry(&addedCommandsTable,
			(char *)elemObjPtr, &isNew);
	    }
	    entryPtr = Tcl_NextHashEntry(&search);
	}

	/*
	 * Search the path next.
	 */

	for (i=0 ; i<nsPtr->commandPathLength ; i++) {
	    Namespace *pathNsPtr = nsPtr->commandPathArray[i].nsPtr;

	    if (pathNsPtr == NULL) {
		continue;
	    }
	    if (pathNsPtr == globalNsPtr) {
		foundGlobal = 1;
	    }
	    entryPtr = Tcl_FirstHashEntry(&pathNsPtr->cmdTable, &search);
	    while (entryPtr != NULL) {
		cmdName = Tcl_GetHashKey(&pathNsPtr->cmdTable, entryPtr);
		if ((simplePattern == NULL)
			|| Tcl_StringMatch(cmdName, simplePattern)) {
		    elemObjPtr = Tcl_NewStringObj(cmdName, -1);
		    (void) Tcl_CreateHashEntry(&addedCommandsTable,
			    (char *) elemObjPtr, &isNew);
		    if (isNew) {
			Tcl_ListObjAppendElement(interp, listPtr, elemObjPtr);
		    } else {
			TclDecrRefCount(elemObjPtr);
		    }
		}
		entryPtr = Tcl_NextHashEntry(&search);
	    }
	}

	/*
	 * If the effective namespace isn't the global :: namespace, and a
	 * specific namespace wasn't requested in the pattern, then add in all
	 * global :: commands that match the simple pattern. Of course, we add
	 * in only those commands that aren't hidden by a command in the
	 * effective namespace.
	 */

	if (!foundGlobal) {
	    entryPtr = Tcl_FirstHashEntry(&globalNsPtr->cmdTable, &search);
	    while (entryPtr != NULL) {
		cmdName = Tcl_GetHashKey(&globalNsPtr->cmdTable, entryPtr);
		if ((simplePattern == NULL)
			|| Tcl_StringMatch(cmdName, simplePattern)) {
		    elemObjPtr = Tcl_NewStringObj(cmdName, -1);
		    if (Tcl_FindHashEntry(&addedCommandsTable,
			    (char *) elemObjPtr) == NULL) {
			Tcl_ListObjAppendElement(interp, listPtr, elemObjPtr);
		    } else {
			TclDecrRefCount(elemObjPtr);
		    }
		}
		entryPtr = Tcl_NextHashEntry(&search);
	    }
	}

	Tcl_DeleteHashTable(&addedCommandsTable);
    }

    Tcl_SetObjResult(interp, listPtr);
    return TCL_OK;
}

/*
 *----------------------------------------------------------------------
 *
 * InfoCompleteCmd --
 *
 *	Called to implement the "info complete" command that determines
 *	whether a string is a complete Tcl command. Handles the following
 *	syntax:
 *
 *	    info complete command
 *
 * Results:
 *	Returns TCL_OK if successful and TCL_ERROR if there is an error.
 *
 * Side effects:
 *	Returns a result in the interpreter's result object. If there is an
 *	error, the result is an error message.
 *
 *----------------------------------------------------------------------
 */

static int
InfoCompleteCmd(
    ClientData dummy,		/* Not used. */
    Tcl_Interp *interp,		/* Current interpreter. */
    int objc,			/* Number of arguments. */
    Tcl_Obj *CONST objv[])	/* Argument objects. */
{
    if (objc != 2) {
	Tcl_WrongNumArgs(interp, 1, objv, "command");
	return TCL_ERROR;
    }

    Tcl_SetObjResult(interp, Tcl_NewBooleanObj(
	    TclObjCommandComplete(objv[1])));
    return TCL_OK;
}

/*
 *----------------------------------------------------------------------
 *
 * InfoDefaultCmd --
 *
 *	Called to implement the "info default" command that returns the
 *	default value for a procedure argument. Handles the following syntax:
 *
 *	    info default procName arg varName
 *
 * Results:
 *	Returns TCL_OK if successful and TCL_ERROR if there is an error.
 *
 * Side effects:
 *	Returns a result in the interpreter's result object. If there is an
 *	error, the result is an error message.
 *
 *----------------------------------------------------------------------
 */

static int
InfoDefaultCmd(
    ClientData dummy,		/* Not used. */
    Tcl_Interp *interp,		/* Current interpreter. */
    int objc,			/* Number of arguments. */
    Tcl_Obj *CONST objv[])	/* Argument objects. */
{
    Interp *iPtr = (Interp *) interp;
    char *procName, *argName, *varName;
    Proc *procPtr;
    CompiledLocal *localPtr;
    Tcl_Obj *valueObjPtr;

    if (objc != 4) {
	Tcl_WrongNumArgs(interp, 1, objv, "procname arg varname");
	return TCL_ERROR;
    }

    procName = TclGetString(objv[1]);
    argName = TclGetString(objv[2]);

    procPtr = TclFindProc(iPtr, procName);
    if (procPtr == NULL) {
	Tcl_AppendResult(interp, "\"", procName, "\" isn't a procedure",NULL);
	return TCL_ERROR;
    }

    for (localPtr = procPtr->firstLocalPtr;  localPtr != NULL;
	    localPtr = localPtr->nextPtr) {
	if (TclIsVarArgument(localPtr)
		&& (strcmp(argName, localPtr->name) == 0)) {
	    if (localPtr->defValuePtr != NULL) {
		valueObjPtr = Tcl_ObjSetVar2(interp, objv[3], NULL,
			localPtr->defValuePtr, 0);
		if (valueObjPtr == NULL) {
		    goto defStoreError;
		}
		Tcl_SetObjResult(interp, Tcl_NewIntObj(1));
	    } else {
		Tcl_Obj *nullObjPtr = Tcl_NewObj();
		valueObjPtr = Tcl_ObjSetVar2(interp, objv[3], NULL,
			nullObjPtr, 0);
		if (valueObjPtr == NULL) {
		    goto defStoreError;
		}
		Tcl_SetObjResult(interp, Tcl_NewIntObj(0));
	    }
	    return TCL_OK;
	}
    }

    Tcl_AppendResult(interp, "procedure \"", procName,
	    "\" doesn't have an argument \"", argName, "\"", NULL);
    return TCL_ERROR;

  defStoreError:
    varName = TclGetString(objv[3]);
    Tcl_AppendResult(interp, "couldn't store default value in variable \"",
	    varName, "\"", NULL);
    return TCL_ERROR;
}

/*
 *----------------------------------------------------------------------
 *
 * TclInfoExistsCmd --
 *
 *	Called to implement the "info exists" command that determines whether
 *	a variable exists. Handles the following syntax:
 *
 *	    info exists varName
 *
 * Results:
 *	Returns TCL_OK if successful and TCL_ERROR if there is an error.
 *
 * Side effects:
 *	Returns a result in the interpreter's result object. If there is an
 *	error, the result is an error message.
 *
 *----------------------------------------------------------------------
 */

int
TclInfoExistsCmd(
    ClientData dummy,		/* Not used. */
    Tcl_Interp *interp,		/* Current interpreter. */
    int objc,			/* Number of arguments. */
    Tcl_Obj *CONST objv[])	/* Argument objects. */
{
    char *varName;
    Var *varPtr;

    if (objc != 2) {
	Tcl_WrongNumArgs(interp, 1, objv, "varName");
	return TCL_ERROR;
    }

    varName = TclGetString(objv[1]);
    varPtr = TclVarTraceExists(interp, varName);

    Tcl_SetObjResult(interp,
	    Tcl_NewBooleanObj(varPtr && varPtr->value.objPtr));
    return TCL_OK;
}

/*
 *----------------------------------------------------------------------
 *
 * InfoFrameCmd --
 *	TIP #280
 *
 *	Called to implement the "info frame" command that returns the location
 *	of either the currently executing command, or its caller. Handles the
 *	following syntax:
 *
 *		info frame ?number?
 *
 * Results:
 *	Returns TCL_OK if successful and TCL_ERROR if there is an error.
 *
 * Side effects:
 *	Returns a result in the interpreter's result object. If there is an
 *	error, the result is an error message.
 *
 *----------------------------------------------------------------------
 */

static int
InfoFrameCmd(
    ClientData dummy,		/* Not used. */
    Tcl_Interp *interp,		/* Current interpreter. */
    int objc,			/* Number of arguments. */
    Tcl_Obj *CONST objv[])	/* Argument objects. */
{
    Interp *iPtr = (Interp *) interp;
    int level;
    CmdFrame *framePtr;

    if (objc == 1) {
	/*
	 * Just "info frame".
	 */

	int levels =
		(iPtr->cmdFramePtr == NULL ? 0 : iPtr->cmdFramePtr->level);

	Tcl_SetObjResult(interp, Tcl_NewIntObj (levels));
	return TCL_OK;
    } else if (objc != 2) {
	Tcl_WrongNumArgs(interp, 1, objv, "?number?");
	return TCL_ERROR;
    }

    /*
     * We've got "info frame level" and must parse the level first.
     */

    if (TclGetIntFromObj(interp, objv[1], &level) != TCL_OK) {
	return TCL_ERROR;
    }
    if (level <= 0) {
	/*
	 * Negative levels are adressing relative to the current frame's
	 * depth.
	 */

	if (iPtr->cmdFramePtr == NULL) {
	levelError:
	    Tcl_AppendStringsToObj(Tcl_GetObjResult(interp), "bad level \"",
		    TclGetString(objv[1]), "\"", NULL);
	    return TCL_ERROR;
	}

	/*
	 * Convert to absolute.
	 */

	level += iPtr->cmdFramePtr->level;
    }

    for (framePtr = iPtr->cmdFramePtr; framePtr != NULL;
	    framePtr = framePtr->nextPtr) {
	if (framePtr->level == level) {
	    break;
	}
    }
    if (framePtr == NULL) {
	goto levelError;
    }

    Tcl_SetObjResult(interp, TclInfoFrame(interp, framePtr));
    return TCL_OK;
}

/*
 *----------------------------------------------------------------------
 *
 * TclInfoFrame --
 *
 *	Core of InfoFrameCmd, returns TIP280 dict for a given frame.
 *
 * Results:
 *	Returns TIP280 dict.
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */

Tcl_Obj *
TclInfoFrame(
    Tcl_Interp *interp,		/* Current interpreter. */
    CmdFrame *framePtr)		/* Frame to get info for. */
{
    Interp *iPtr = (Interp *) interp;
    Tcl_Obj *lv[20];		/* Keep uptodate when more keys are added to
				 * the dict. */
    int lc = 0;
    /*
     * This array is indexed by the TCL_LOCATION_... values, except
     * for _LAST.
     */
    static CONST char *typeString[TCL_LOCATION_LAST] = {
	"eval", "eval", "eval", "precompiled", "source", "proc"
    };
    Tcl_Obj *tmpObj;
    Proc *procPtr =
	framePtr->framePtr ? framePtr->framePtr->procPtr : NULL;

   /*
     * Pull the information and construct the dictionary to return, as list.
     * Regarding use of the CmdFrame fields see tclInt.h, and its definition.
     */

#define ADD_PAIR(name, value) \
	TclNewLiteralStringObj(tmpObj, name); \
	lv[lc++] = tmpObj; \
	lv[lc++] = (value)

    switch (framePtr->type) {
    case TCL_LOCATION_EVAL:
	/*
	 * Evaluation, dynamic script. Type, line, cmd, the latter through
	 * str.
	 */

	ADD_PAIR("type", Tcl_NewStringObj(typeString[framePtr->type], -1));
	ADD_PAIR("line", Tcl_NewIntObj(framePtr->line[0]));
	ADD_PAIR("cmd", Tcl_NewStringObj(framePtr->cmd.str.cmd,
		framePtr->cmd.str.len));
	break;

    case TCL_LOCATION_EVAL_LIST:
	/*
	 * List optimized evaluation. Type, line, cmd, the latter through
	 * listPtr, possibly a frame.
	 */

	ADD_PAIR("type", Tcl_NewStringObj(typeString[framePtr->type], -1));
	ADD_PAIR("line", Tcl_NewIntObj(1));

	/*
	 * We put a duplicate of the command list obj into the result to
	 * ensure that the 'pure List'-property of the command itself is not
	 * destroyed. Otherwise the query here would disable the list
	 * optimization path in Tcl_EvalObjEx.
	 */

	ADD_PAIR("cmd", Tcl_DuplicateObj(framePtr->cmd.listPtr));
	break;

    case TCL_LOCATION_PREBC:
	/*
	 * Precompiled. Result contains the type as signal, nothing else.
	 */

	ADD_PAIR("type", Tcl_NewStringObj(typeString[framePtr->type], -1));
	break;

    case TCL_LOCATION_BC: {
	/*
	 * Execution of bytecode. Talk to the BC engine to fill out the frame.
	 */

	CmdFrame *fPtr;

	fPtr = (CmdFrame *) TclStackAlloc(interp, sizeof(CmdFrame));
	*fPtr = *framePtr;

	/*
	 * Note:
	 * Type BC => f.data.eval.path	  is not used.
	 *	      f.data.tebc.codePtr is used instead.
	 */

	TclGetSrcInfoForPc(fPtr);

	/*
	 * Now filled: cmd.str.(cmd,len), line
	 * Possibly modified: type, path!
	 */

	ADD_PAIR("type", Tcl_NewStringObj(typeString[fPtr->type], -1));
	if (fPtr->line) {
	    ADD_PAIR("line", Tcl_NewIntObj(fPtr->line[0]));
	}

	if (fPtr->type == TCL_LOCATION_SOURCE) {
	    ADD_PAIR("file", fPtr->data.eval.path);

	    /*
	     * Death of reference by TclGetSrcInfoForPc.
	     */

	    Tcl_DecrRefCount(fPtr->data.eval.path);
	}

	ADD_PAIR("cmd",
		Tcl_NewStringObj(fPtr->cmd.str.cmd, fPtr->cmd.str.len));
	TclStackFree(interp, fPtr);
	break;
    }

    case TCL_LOCATION_SOURCE:
	/*
	 * Evaluation of a script file.
	 */

	ADD_PAIR("type", Tcl_NewStringObj(typeString[framePtr->type], -1));
	ADD_PAIR("line", Tcl_NewIntObj(framePtr->line[0]));
	ADD_PAIR("file", framePtr->data.eval.path);

	/*
	 * Refcount framePtr->data.eval.path goes up when lv is converted into
	 * the result list object.
	 */

	ADD_PAIR("cmd", Tcl_NewStringObj(framePtr->cmd.str.cmd,
		framePtr->cmd.str.len));
	break;

    case TCL_LOCATION_PROC:
	Tcl_Panic("TCL_LOCATION_PROC found in standard frame");
	break;
    }

    /*
     * 'proc'. Common to all frame types. Conditional on having an associated
     * Procedure CallFrame.
     */

    if (procPtr != NULL) {
	Tcl_HashEntry *namePtr = procPtr->cmdPtr->hPtr;

	if (namePtr) {
	    /*
	     * This is a regular command.
	     */

	    char *procName = Tcl_GetHashKey(namePtr->tablePtr, namePtr);
	    char *nsName = procPtr->cmdPtr->nsPtr->fullName;

	    ADD_PAIR("proc", Tcl_NewStringObj(nsName, -1));

	    if (strcmp(nsName, "::") != 0) {
		Tcl_AppendToObj(lv[lc-1], "::", -1);
	    }
	    Tcl_AppendToObj(lv[lc-1], procName, -1);
	} else if (procPtr->cmdPtr->clientData) {
	    ExtraFrameInfo *efiPtr = procPtr->cmdPtr->clientData;
	    int i;

	    /*
	     * This is a non-standard command. Luckily, it's told us how to
	     * render extra information about its frame.
	     */

	    for (i=0 ; i<efiPtr->length ; i++) {
		lv[lc++] = Tcl_NewStringObj(efiPtr->fields[i].name, -1);
		if (efiPtr->fields[i].proc) {
		    lv[lc++] =
			efiPtr->fields[i].proc(efiPtr->fields[i].clientData);
		} else {
		    lv[lc++] = efiPtr->fields[i].clientData;
		}
	    }
	}
    }

    /*
     * 'level'. Common to all frame types. Conditional on having an associated
     * _visible_ CallFrame.
     */

    if ((framePtr->framePtr != NULL) && (iPtr->varFramePtr != NULL)) {
	CallFrame *current = framePtr->framePtr;
	CallFrame *top = iPtr->varFramePtr;
	CallFrame *idx;

	for (idx=top ; idx!=NULL ; idx=idx->callerVarPtr) {
	    if (idx == current) {
		int c = framePtr->framePtr->level;
		int t = iPtr->varFramePtr->level;

		ADD_PAIR("level", Tcl_NewIntObj(t - c));
		break;
	    }
	}
    }

    return Tcl_NewListObj(lc, lv);
}

/*
 *----------------------------------------------------------------------
 *
 * InfoFunctionsCmd --
 *
 *	Called to implement the "info functions" command that returns the list
 *	of math functions matching an optional pattern. Handles the following
 *	syntax:
 *
 *	    info functions ?pattern?
 *
 * Results:
 *	Returns TCL_OK if successful and TCL_ERROR if there is an error.
 *
 * Side effects:
 *	Returns a result in the interpreter's result object. If there is an
 *	error, the result is an error message.
 *
 *----------------------------------------------------------------------
 */

static int
InfoFunctionsCmd(
    ClientData dummy,		/* Not used. */
    Tcl_Interp *interp,		/* Current interpreter. */
    int objc,			/* Number of arguments. */
    Tcl_Obj *CONST objv[])	/* Argument objects. */
{
    char *pattern;

    if (objc == 1) {
	pattern = NULL;
    } else if (objc == 2) {
	pattern = TclGetString(objv[1]);
    } else {
	Tcl_WrongNumArgs(interp, 1, objv, "?pattern?");
	return TCL_ERROR;
    }

    Tcl_SetObjResult(interp, Tcl_ListMathFuncs(interp, pattern));
    return TCL_OK;
}

/*
 *----------------------------------------------------------------------
 *
 * InfoHostnameCmd --
 *
 *	Called to implement the "info hostname" command that returns the host
 *	name. Handles the following syntax:
 *
 *	    info hostname
 *
 * Results:
 *	Returns TCL_OK if successful and TCL_ERROR if there is an error.
 *
 * Side effects:
 *	Returns a result in the interpreter's result object. If there is an
 *	error, the result is an error message.
 *
 *----------------------------------------------------------------------
 */

static int
InfoHostnameCmd(
    ClientData dummy,		/* Not used. */
    Tcl_Interp *interp,		/* Current interpreter. */
    int objc,			/* Number of arguments. */
    Tcl_Obj *CONST objv[])	/* Argument objects. */
{
    CONST char *name;

    if (objc != 1) {
	Tcl_WrongNumArgs(interp, 1, objv, NULL);
	return TCL_ERROR;
    }

    name = Tcl_GetHostName();
    if (name) {
	Tcl_SetObjResult(interp, Tcl_NewStringObj(name, -1));
	return TCL_OK;
    }
    Tcl_SetResult(interp, "unable to determine name of host", TCL_STATIC);
    return TCL_ERROR;
}

/*
 *----------------------------------------------------------------------
 *
 * InfoLevelCmd --
 *
 *	Called to implement the "info level" command that returns information
 *	about the call stack. Handles the following syntax:
 *
 *	    info level ?number?
 *
 * Results:
 *	Returns TCL_OK if successful and TCL_ERROR if there is an error.
 *
 * Side effects:
 *	Returns a result in the interpreter's result object. If there is an
 *	error, the result is an error message.
 *
 *----------------------------------------------------------------------
 */

static int
InfoLevelCmd(
    ClientData dummy,		/* Not used. */
    Tcl_Interp *interp,		/* Current interpreter. */
    int objc,			/* Number of arguments. */
    Tcl_Obj *CONST objv[])	/* Argument objects. */
{
    Interp *iPtr = (Interp *) interp;

    if (objc == 1) {		/* Just "info level" */
	Tcl_SetObjResult(interp, Tcl_NewIntObj(iPtr->varFramePtr->level));
	return TCL_OK;
    }

    if (objc == 2) {
	int level;
	CallFrame *framePtr, *rootFramePtr = iPtr->rootFramePtr;

	if (TclGetIntFromObj(interp, objv[1], &level) != TCL_OK) {
	    return TCL_ERROR;
	}
	if (level <= 0) {
	    if (iPtr->varFramePtr == rootFramePtr) {
		goto levelError;
	    }
	    level += iPtr->varFramePtr->level;
	}
	for (framePtr=iPtr->varFramePtr ; framePtr!=rootFramePtr;
		framePtr=framePtr->callerVarPtr) {
	    if (framePtr->level == level) {
		break;
	    }
	}
	if (framePtr == rootFramePtr) {
	    goto levelError;
	}

	Tcl_SetObjResult(interp,
		Tcl_NewListObj(framePtr->objc, framePtr->objv));
	return TCL_OK;
    }

    Tcl_WrongNumArgs(interp, 1, objv, "?number?");
    return TCL_ERROR;

  levelError:
    Tcl_AppendResult(interp, "bad level \"", TclGetString(objv[1]), "\"",
	    NULL);
    return TCL_ERROR;
}

/*
 *----------------------------------------------------------------------
 *
 * InfoLibraryCmd --
 *
 *	Called to implement the "info library" command that returns the
 *	library directory for the Tcl installation. Handles the following
 *	syntax:
 *
 *	    info library
 *
 * Results:
 *	Returns TCL_OK if successful and TCL_ERROR if there is an error.
 *
 * Side effects:
 *	Returns a result in the interpreter's result object. If there is an
 *	error, the result is an error message.
 *
 *----------------------------------------------------------------------
 */

static int
InfoLibraryCmd(
    ClientData dummy,		/* Not used. */
    Tcl_Interp *interp,		/* Current interpreter. */
    int objc,			/* Number of arguments. */
    Tcl_Obj *CONST objv[])	/* Argument objects. */
{
    CONST char *libDirName;

    if (objc != 1) {
	Tcl_WrongNumArgs(interp, 1, objv, NULL);
	return TCL_ERROR;
    }

    libDirName = Tcl_GetVar(interp, "tcl_library", TCL_GLOBAL_ONLY);
    if (libDirName != NULL) {
	Tcl_SetObjResult(interp, Tcl_NewStringObj(libDirName, -1));
	return TCL_OK;
    }
    Tcl_SetResult(interp, "no library has been specified for Tcl",TCL_STATIC);
    return TCL_ERROR;
}

/*
 *----------------------------------------------------------------------
 *
 * InfoLoadedCmd --
 *
 *	Called to implement the "info loaded" command that returns the
 *	packages that have been loaded into an interpreter. Handles the
 *	following syntax:
 *
 *	    info loaded ?interp?
 *
 * Results:
 *	Returns TCL_OK if successful and TCL_ERROR if there is an error.
 *
 * Side effects:
 *	Returns a result in the interpreter's result object. If there is an
 *	error, the result is an error message.
 *
 *----------------------------------------------------------------------
 */

static int
InfoLoadedCmd(
    ClientData dummy,		/* Not used. */
    Tcl_Interp *interp,		/* Current interpreter. */
    int objc,			/* Number of arguments. */
    Tcl_Obj *CONST objv[])	/* Argument objects. */
{
    char *interpName;
    int result;

    if ((objc != 1) && (objc != 2)) {
	Tcl_WrongNumArgs(interp, 1, objv, "?interp?");
	return TCL_ERROR;
    }

    if (objc == 1) {		/* Get loaded pkgs in all interpreters. */
	interpName = NULL;
    } else {			/* Get pkgs just in specified interp. */
	interpName = TclGetString(objv[1]);
    }
    result = TclGetLoadedPackages(interp, interpName);
    return result;
}

/*
 *----------------------------------------------------------------------
 *
 * InfoNameOfExecutableCmd --
 *
 *	Called to implement the "info nameofexecutable" command that returns
 *	the name of the binary file running this application. Handles the
 *	following syntax:
 *
 *	    info nameofexecutable
 *
 * Results:
 *	Returns TCL_OK if successful and TCL_ERROR if there is an error.
 *
 * Side effects:
 *	Returns a result in the interpreter's result object. If there is an
 *	error, the result is an error message.
 *
 *----------------------------------------------------------------------
 */

static int
InfoNameOfExecutableCmd(
    ClientData dummy,		/* Not used. */
    Tcl_Interp *interp,		/* Current interpreter. */
    int objc,			/* Number of arguments. */
    Tcl_Obj *CONST objv[])	/* Argument objects. */
{
    if (objc != 1) {
	Tcl_WrongNumArgs(interp, 1, objv, NULL);
	return TCL_ERROR;
    }
    Tcl_SetObjResult(interp, TclGetObjNameOfExecutable());
    return TCL_OK;
}

/*
 *----------------------------------------------------------------------
 *
 * InfoPatchLevelCmd --
 *
 *	Called to implement the "info patchlevel" command that returns the
 *	default value for an argument to a procedure. Handles the following
 *	syntax:
 *
 *	    info patchlevel
 *
 * Results:
 *	Returns TCL_OK if successful and TCL_ERROR if there is an error.
 *
 * Side effects:
 *	Returns a result in the interpreter's result object. If there is an
 *	error, the result is an error message.
 *
 *----------------------------------------------------------------------
 */

static int
InfoPatchLevelCmd(
    ClientData dummy,		/* Not used. */
    Tcl_Interp *interp,		/* Current interpreter. */
    int objc,			/* Number of arguments. */
    Tcl_Obj *CONST objv[])	/* Argument objects. */
{
    CONST char *patchlevel;

    if (objc != 1) {
	Tcl_WrongNumArgs(interp, 1, objv, NULL);
	return TCL_ERROR;
    }

    patchlevel = Tcl_GetVar(interp, "tcl_patchLevel",
	    (TCL_GLOBAL_ONLY | TCL_LEAVE_ERR_MSG));
    if (patchlevel != NULL) {
	Tcl_SetObjResult(interp, Tcl_NewStringObj(patchlevel, -1));
	return TCL_OK;
    }
    return TCL_ERROR;
}

/*
 *----------------------------------------------------------------------
 *
 * InfoProcsCmd --
 *
 *	Called to implement the "info procs" command that returns the list of
 *	procedures in the interpreter that match an optional pattern. The
 *	pattern, if any, consists of an optional sequence of namespace names
 *	separated by "::" qualifiers, which is followed by a glob-style
 *	pattern that restricts which commands are returned. Handles the
 *	following syntax:
 *
 *	    info procs ?pattern?
 *
 * Results:
 *	Returns TCL_OK if successful and TCL_ERROR if there is an error.
 *
 * Side effects:
 *	Returns a result in the interpreter's result object. If there is an
 *	error, the result is an error message.
 *
 *----------------------------------------------------------------------
 */

static int
InfoProcsCmd(
    ClientData dummy,		/* Not used. */
    Tcl_Interp *interp,		/* Current interpreter. */
    int objc,			/* Number of arguments. */
    Tcl_Obj *CONST objv[])	/* Argument objects. */
{
    char *cmdName, *pattern;
    CONST char *simplePattern;
    Namespace *nsPtr;
#ifdef INFO_PROCS_SEARCH_GLOBAL_NS
    Namespace *globalNsPtr = (Namespace *) Tcl_GetGlobalNamespace(interp);
#endif
    Namespace *currNsPtr = (Namespace *) Tcl_GetCurrentNamespace(interp);
    Tcl_Obj *listPtr, *elemObjPtr;
    int specificNsInPattern = 0;/* Init. to avoid compiler warning. */
    register Tcl_HashEntry *entryPtr;
    Tcl_HashSearch search;
    Command *cmdPtr, *realCmdPtr;

    /*
     * Get the pattern and find the "effective namespace" in which to list
     * procs.
     */

    if (objc == 1) {
	simplePattern = NULL;
	nsPtr = currNsPtr;
	specificNsInPattern = 0;
    } else if (objc == 2) {
	/*
	 * From the pattern, get the effective namespace and the simple
	 * pattern (no namespace qualifiers or ::'s) at the end. If an error
	 * was found while parsing the pattern, return it. Otherwise, if the
	 * namespace wasn't found, just leave nsPtr NULL: we will return an
	 * empty list since no commands there can be found.
	 */

	Namespace *dummy1NsPtr, *dummy2NsPtr;

	pattern = TclGetString(objv[1]);
	TclGetNamespaceForQualName(interp, pattern, (Namespace *) NULL,
		/*flags*/ 0, &nsPtr, &dummy1NsPtr, &dummy2NsPtr,
		&simplePattern);

	if (nsPtr != NULL) {	/* We successfully found the pattern's ns. */
	    specificNsInPattern = (strcmp(simplePattern, pattern) != 0);
	}
    } else {
	Tcl_WrongNumArgs(interp, 1, objv, "?pattern?");
	return TCL_ERROR;
    }

    if (nsPtr == NULL) {
	return TCL_OK;
    }

    /*
     * Scan through the effective namespace's command table and create a list
     * with all procs that match the pattern. If a specific namespace was
     * requested in the pattern, qualify the command names with the namespace
     * name.
     */

    listPtr = Tcl_NewListObj(0, NULL);
#ifndef INFO_PROCS_SEARCH_GLOBAL_NS
    if (simplePattern != NULL && TclMatchIsTrivial(simplePattern)) {
	entryPtr = Tcl_FindHashEntry(&nsPtr->cmdTable, simplePattern);
	if (entryPtr != NULL) {
	    cmdPtr = (Command *) Tcl_GetHashValue(entryPtr);

	    if (!TclIsProc(cmdPtr)) {
		realCmdPtr = (Command *)
			TclGetOriginalCommand((Tcl_Command) cmdPtr);
		if (realCmdPtr != NULL && TclIsProc(realCmdPtr)) {
		    goto simpleProcOK;
		}
	    } else {
	    simpleProcOK:
		if (specificNsInPattern) {
		    elemObjPtr = Tcl_NewObj();
		    Tcl_GetCommandFullName(interp, (Tcl_Command) cmdPtr,
			    elemObjPtr);
		} else {
		    elemObjPtr = Tcl_NewStringObj(simplePattern, -1);
		}
		Tcl_ListObjAppendElement(interp, listPtr, elemObjPtr);
	    }
	}
    } else
#endif /* !INFO_PROCS_SEARCH_GLOBAL_NS */
    {
	entryPtr = Tcl_FirstHashEntry(&nsPtr->cmdTable, &search);
	while (entryPtr != NULL) {
	    cmdName = Tcl_GetHashKey(&nsPtr->cmdTable, entryPtr);
	    if ((simplePattern == NULL)
		    || Tcl_StringMatch(cmdName, simplePattern)) {
		cmdPtr = (Command *) Tcl_GetHashValue(entryPtr);

		if (!TclIsProc(cmdPtr)) {
		    realCmdPtr = (Command *)
			    TclGetOriginalCommand((Tcl_Command) cmdPtr);
		    if (realCmdPtr != NULL && TclIsProc(realCmdPtr)) {
			goto procOK;
		    }
		} else {
		procOK:
		    if (specificNsInPattern) {
			elemObjPtr = Tcl_NewObj();
			Tcl_GetCommandFullName(interp, (Tcl_Command) cmdPtr,
				elemObjPtr);
		    } else {
			elemObjPtr = Tcl_NewStringObj(cmdName, -1);
		    }
		    Tcl_ListObjAppendElement(interp, listPtr, elemObjPtr);
		}
	    }
	    entryPtr = Tcl_NextHashEntry(&search);
	}

	/*
	 * If the effective namespace isn't the global :: namespace, and a
	 * specific namespace wasn't requested in the pattern, then add in all
	 * global :: procs that match the simple pattern. Of course, we add in
	 * only those procs that aren't hidden by a proc in the effective
	 * namespace.
	 */

#ifdef INFO_PROCS_SEARCH_GLOBAL_NS
	/*
	 * If "info procs" worked like "info commands", returning the commands
	 * also seen in the global namespace, then you would include this
	 * code. As this could break backwards compatibilty with 8.0-8.2, we
	 * decided not to "fix" it in 8.3, leaving the behavior slightly
	 * different.
	 */

	if ((nsPtr != globalNsPtr) && !specificNsInPattern) {
	    entryPtr = Tcl_FirstHashEntry(&globalNsPtr->cmdTable, &search);
	    while (entryPtr != NULL) {
		cmdName = Tcl_GetHashKey(&globalNsPtr->cmdTable, entryPtr);
		if ((simplePattern == NULL)
			|| Tcl_StringMatch(cmdName, simplePattern)) {
		    if (Tcl_FindHashEntry(&nsPtr->cmdTable,cmdName) == NULL) {
			cmdPtr = (Command *) Tcl_GetHashValue(entryPtr);
			realCmdPtr = (Command *) TclGetOriginalCommand(
				(Tcl_Command) cmdPtr);

			if (TclIsProc(cmdPtr) || ((realCmdPtr != NULL)
				&& TclIsProc(realCmdPtr))) {
			    Tcl_ListObjAppendElement(interp, listPtr,
				    Tcl_NewStringObj(cmdName, -1));
			}
		    }
		}
		entryPtr = Tcl_NextHashEntry(&search);
	    }
	}
#endif
    }

    Tcl_SetObjResult(interp, listPtr);
    return TCL_OK;
}

/*
 *----------------------------------------------------------------------
 *
 * InfoScriptCmd --
 *
 *	Called to implement the "info script" command that returns the script
 *	file that is currently being evaluated. Handles the following syntax:
 *
 *	    info script ?newName?
 *
 *	If newName is specified, it will set that as the internal name.
 *
 * Results:
 *	Returns TCL_OK if successful and TCL_ERROR if there is an error.
 *
 * Side effects:
 *	Returns a result in the interpreter's result object. If there is an
 *	error, the result is an error message. It may change the internal
 *	script filename.
 *
 *----------------------------------------------------------------------
 */

static int
InfoScriptCmd(
    ClientData dummy,		/* Not used. */
    Tcl_Interp *interp,		/* Current interpreter. */
    int objc,			/* Number of arguments. */
    Tcl_Obj *CONST objv[])	/* Argument objects. */
{
    Interp *iPtr = (Interp *) interp;
    if ((objc != 1) && (objc != 2)) {
	Tcl_WrongNumArgs(interp, 1, objv, "?filename?");
	return TCL_ERROR;
    }

    if (objc == 2) {
	if (iPtr->scriptFile != NULL) {
	    Tcl_DecrRefCount(iPtr->scriptFile);
	}
	iPtr->scriptFile = objv[1];
	Tcl_IncrRefCount(iPtr->scriptFile);
    }
    if (iPtr->scriptFile != NULL) {
	Tcl_SetObjResult(interp, iPtr->scriptFile);
    }
    return TCL_OK;
}

/*
 *----------------------------------------------------------------------
 *
 * InfoSharedlibCmd --
 *
 *	Called to implement the "info sharedlibextension" command that returns
 *	the file extension used for shared libraries. Handles the following
 *	syntax:
 *
 *	    info sharedlibextension
 *
 * Results:
 *	Returns TCL_OK if successful and TCL_ERROR if there is an error.
 *
 * Side effects:
 *	Returns a result in the interpreter's result object. If there is an
 *	error, the result is an error message.
 *
 *----------------------------------------------------------------------
 */

static int
InfoSharedlibCmd(
    ClientData dummy,		/* Not used. */
    Tcl_Interp *interp,		/* Current interpreter. */
    int objc,			/* Number of arguments. */
    Tcl_Obj *CONST objv[])	/* Argument objects. */
{
    if (objc != 1) {
	Tcl_WrongNumArgs(interp, 1, objv, NULL);
	return TCL_ERROR;
    }

#ifdef TCL_SHLIB_EXT
    Tcl_SetObjResult(interp, Tcl_NewStringObj(TCL_SHLIB_EXT, -1));
#endif
    return TCL_OK;
}

/*
 *----------------------------------------------------------------------
 *
 * InfoTclVersionCmd --
 *
 *	Called to implement the "info tclversion" command that returns the
 *	version number for this Tcl library. Handles the following syntax:
 *
 *	    info tclversion
 *
 * Results:
 *	Returns TCL_OK if successful and TCL_ERROR if there is an error.
 *
 * Side effects:
 *	Returns a result in the interpreter's result object. If there is an
 *	error, the result is an error message.
 *
 *----------------------------------------------------------------------
 */

static int
InfoTclVersionCmd(
    ClientData dummy,		/* Not used. */
    Tcl_Interp *interp,		/* Current interpreter. */
    int objc,			/* Number of arguments. */
    Tcl_Obj *CONST objv[])	/* Argument objects. */
{
    Tcl_Obj *version;

    if (objc != 1) {
	Tcl_WrongNumArgs(interp, 1, objv, NULL);
	return TCL_ERROR;
    }

    version = Tcl_GetVar2Ex(interp, "tcl_version", NULL,
	    (TCL_GLOBAL_ONLY | TCL_LEAVE_ERR_MSG));
    if (version != NULL) {
	Tcl_SetObjResult(interp, version);
	return TCL_OK;
    }
    return TCL_ERROR;
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_JoinObjCmd --
 *
 *	This procedure is invoked to process the "join" Tcl command. See the
 *	user documentation for details on what it does.
 *
 * Results:
 *	A standard Tcl object result.
 *
 * Side effects:
 *	See the user documentation.
 *
 *----------------------------------------------------------------------
 */

int
Tcl_JoinObjCmd(
    ClientData dummy,		/* Not used. */
    Tcl_Interp *interp,		/* Current interpreter. */
    int objc,			/* Number of arguments. */
    Tcl_Obj *CONST objv[])	/* The argument objects. */
{
    int listLen, i;
    Tcl_Obj *resObjPtr, *joinObjPtr, **elemPtrs;

    if ((objc < 2) || (objc > 3)) {
	Tcl_WrongNumArgs(interp, 1, objv, "list ?joinString?");
	return TCL_ERROR;
    }

    /*
     * Make sure the list argument is a list object and get its length and a
     * pointer to its array of element pointers.
     */

    if (TclListObjGetElements(interp, objv[1], &listLen,
	    &elemPtrs) != TCL_OK) {
	return TCL_ERROR;
    }

    joinObjPtr = (objc == 2) ? Tcl_NewStringObj(" ", 1) : objv[2];
    Tcl_IncrRefCount(joinObjPtr);

    resObjPtr = Tcl_NewObj();
    for (i = 0;  i < listLen;  i++) {
	if (i > 0) {
	    Tcl_AppendObjToObj(resObjPtr, joinObjPtr);
	}
	Tcl_AppendObjToObj(resObjPtr, elemPtrs[i]);
    }
    Tcl_DecrRefCount(joinObjPtr);
    Tcl_SetObjResult(interp, resObjPtr);
    return TCL_OK;
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_LassignObjCmd --
 *
 *	This object-based procedure is invoked to process the "lassign" Tcl
 *	command. See the user documentation for details on what it does.
 *
 * Results:
 *	A standard Tcl object result.
 *
 * Side effects:
 *	See the user documentation.
 *
 *----------------------------------------------------------------------
 */

int
Tcl_LassignObjCmd(
    ClientData dummy,		/* Not used. */
    Tcl_Interp *interp,		/* Current interpreter. */
    int objc,			/* Number of arguments. */
    Tcl_Obj *CONST objv[])	/* Argument objects. */
{
    Tcl_Obj *listCopyPtr;
    Tcl_Obj **listObjv;		/* The contents of the list. */
    int listObjc;		/* The length of the list. */
    int code = TCL_OK;

    if (objc < 3) {
	Tcl_WrongNumArgs(interp, 1, objv, "list varName ?varName ...?");
	return TCL_ERROR;
    }

    listCopyPtr = TclListObjCopy(interp, objv[1]);
    if (listCopyPtr == NULL) {
	return TCL_ERROR;
    }

    TclListObjGetElements(NULL, listCopyPtr, &listObjc, &listObjv);

    objc -= 2;
    objv += 2;
    while (code == TCL_OK && objc > 0 && listObjc > 0) {
	if (NULL == Tcl_ObjSetVar2(interp, *objv++, NULL,
		*listObjv++, TCL_LEAVE_ERR_MSG)) {
	    code = TCL_ERROR;
	}
	objc--; listObjc--;
    }

    if (code == TCL_OK && objc > 0) {
	Tcl_Obj *emptyObj;
	TclNewObj(emptyObj);
	Tcl_IncrRefCount(emptyObj);
	while (code == TCL_OK && objc-- > 0) {
	    if (NULL == Tcl_ObjSetVar2(interp, *objv++, NULL,
		    emptyObj, TCL_LEAVE_ERR_MSG)) {
		code = TCL_ERROR;
	    }
	}
	Tcl_DecrRefCount(emptyObj);
    }

    if (code == TCL_OK && listObjc > 0) {
	Tcl_SetObjResult(interp, Tcl_NewListObj(listObjc, listObjv));
    }

    Tcl_DecrRefCount(listCopyPtr);
    return code;
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_LindexObjCmd --
 *
 *	This object-based procedure is invoked to process the "lindex" Tcl
 *	command. See the user documentation for details on what it does.
 *
 * Results:
 *	A standard Tcl object result.
 *
 * Side effects:
 *	See the user documentation.
 *
 *----------------------------------------------------------------------
 */

int
Tcl_LindexObjCmd(
    ClientData dummy,		/* Not used. */
    Tcl_Interp *interp,		/* Current interpreter. */
    int objc,			/* Number of arguments. */
    Tcl_Obj *CONST objv[])	/* Argument objects. */
{

    Tcl_Obj *elemPtr;		/* Pointer to the element being extracted. */

    if (objc < 2) {
	Tcl_WrongNumArgs(interp, 1, objv, "list ?index...?");
	return TCL_ERROR;
    }

    /*
     * If objc==3, then objv[2] may be either a single index or a list of
     * indices: go to TclLindexList to determine which. If objc>=4, or
     * objc==2, then objv[2 .. objc-2] are all single indices and processed as
     * such in TclLindexFlat.
     */

    if (objc == 3) {
	elemPtr = TclLindexList(interp, objv[1], objv[2]);
    } else {
	elemPtr = TclLindexFlat(interp, objv[1], objc-2, objv+2);
    }

    /*
     * Set the interpreter's object result to the last element extracted.
     */

    if (elemPtr == NULL) {
	return TCL_ERROR;
    } else {
	Tcl_SetObjResult(interp, elemPtr);
	Tcl_DecrRefCount(elemPtr);
	return TCL_OK;
    }
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_LinsertObjCmd --
 *
 *	This object-based procedure is invoked to process the "linsert" Tcl
 *	command. See the user documentation for details on what it does.
 *
 * Results:
 *	A new Tcl list object formed by inserting zero or more elements into a
 *	list.
 *
 * Side effects:
 *	See the user documentation.
 *
 *----------------------------------------------------------------------
 */

int
Tcl_LinsertObjCmd(
    ClientData dummy,		/* Not used. */
    Tcl_Interp *interp,		/* Current interpreter. */
    register int objc,		/* Number of arguments. */
    Tcl_Obj *CONST objv[])	/* Argument objects. */
{
    Tcl_Obj *listPtr;
    int index, len, result;

    if (objc < 4) {
	Tcl_WrongNumArgs(interp, 1, objv, "list index element ?element ...?");
	return TCL_ERROR;
    }

    result = TclListObjLength(interp, objv[1], &len);
    if (result != TCL_OK) {
	return result;
    }

    /*
     * Get the index. "end" is interpreted to be the index after the last
     * element, such that using it will cause any inserted elements to be
     * appended to the list.
     */

    result = TclGetIntForIndexM(interp, objv[2], /*end*/ len, &index);
    if (result != TCL_OK) {
	return result;
    }
    if (index > len) {
	index = len;
    }

    /*
     * If the list object is unshared we can modify it directly. Otherwise we
     * create a copy to modify: this is "copy on write".
     */

    listPtr = objv[1];
    if (Tcl_IsShared(listPtr)) {
	listPtr = TclListObjCopy(NULL, listPtr);
    }

    if ((objc == 4) && (index == len)) {
	/*
	 * Special case: insert one element at the end of the list.
	 */

	Tcl_ListObjAppendElement(NULL, listPtr, objv[3]);
    } else {
	Tcl_ListObjReplace(NULL, listPtr, index, 0, (objc-3), &(objv[3]));
    }

    /*
     * Set the interpreter's object result.
     */

    Tcl_SetObjResult(interp, listPtr);
    return TCL_OK;
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_ListObjCmd --
 *
 *	This procedure is invoked to process the "list" Tcl command. See the
 *	user documentation for details on what it does.
 *
 * Results:
 *	A standard Tcl object result.
 *
 * Side effects:
 *	See the user documentation.
 *
 *----------------------------------------------------------------------
 */

int
Tcl_ListObjCmd(
    ClientData dummy,		/* Not used. */
    Tcl_Interp *interp,		/* Current interpreter. */
    register int objc,		/* Number of arguments. */
    register Tcl_Obj *CONST objv[])
				/* The argument objects. */
{
    /*
     * If there are no list elements, the result is an empty object.
     * Otherwise set the interpreter's result object to be a list object.
     */

    if (objc > 1) {
	Tcl_SetObjResult(interp, Tcl_NewListObj((objc-1), &(objv[1])));
    }
    return TCL_OK;
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_LlengthObjCmd --
 *
 *	This object-based procedure is invoked to process the "llength" Tcl
 *	command. See the user documentation for details on what it does.
 *
 * Results:
 *	A standard Tcl object result.
 *
 * Side effects:
 *	See the user documentation.
 *
 *----------------------------------------------------------------------
 */

int
Tcl_LlengthObjCmd(
    ClientData dummy,		/* Not used. */
    Tcl_Interp *interp,		/* Current interpreter. */
    int objc,			/* Number of arguments. */
    register Tcl_Obj *CONST objv[])
				/* Argument objects. */
{
    int listLen, result;

    if (objc != 2) {
	Tcl_WrongNumArgs(interp, 1, objv, "list");
	return TCL_ERROR;
    }

    result = TclListObjLength(interp, objv[1], &listLen);
    if (result != TCL_OK) {
	return result;
    }

    /*
     * Set the interpreter's object result to an integer object holding the
     * length.
     */

    Tcl_SetObjResult(interp, Tcl_NewIntObj(listLen));
    return TCL_OK;
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_LrangeObjCmd --
 *
 *	This procedure is invoked to process the "lrange" Tcl command. See the
 *	user documentation for details on what it does.
 *
 * Results:
 *	A standard Tcl object result.
 *
 * Side effects:
 *	See the user documentation.
 *
 *----------------------------------------------------------------------
 */

int
Tcl_LrangeObjCmd(
    ClientData notUsed,		/* Not used. */
    Tcl_Interp *interp,		/* Current interpreter. */
    int objc,			/* Number of arguments. */
    register Tcl_Obj *CONST objv[])
				/* Argument objects. */
{
    Tcl_Obj *listPtr, **elemPtrs;
    int listLen, first, result;

    if (objc != 4) {
	Tcl_WrongNumArgs(interp, 1, objv, "list first last");
	return TCL_ERROR;
    }

    /*
     * Make sure the list argument is a list object and get its length and a
     * pointer to its array of element pointers.
     */

    listPtr = TclListObjCopy(interp, objv[1]);
    if (listPtr == NULL) {
	return TCL_ERROR;
    }
    TclListObjGetElements(NULL, listPtr, &listLen, &elemPtrs);

    result = TclGetIntForIndexM(interp, objv[2], /*endValue*/ listLen - 1,
	    &first);
    if (result == TCL_OK) {
	int last;

	if (first < 0) {
	    first = 0;
	}

	result = TclGetIntForIndexM(interp, objv[3], /*endValue*/ listLen - 1,
		&last);
	if (result == TCL_OK) {
	    if (last >= listLen) {
		last = (listLen - 1);
	    }

	    if (first <= last) {
		int numElems = (last - first + 1);

		Tcl_SetObjResult(interp,
			Tcl_NewListObj(numElems, &(elemPtrs[first])));
	    }
	}
    }

    Tcl_DecrRefCount(listPtr);
    return result;
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_LrepeatObjCmd --
 *
 *	This procedure is invoked to process the "lrepeat" Tcl command. See
 *	the user documentation for details on what it does.
 *
 * Results:
 *	A standard Tcl object result.
 *
 * Side effects:
 *	See the user documentation.
 *
 *----------------------------------------------------------------------
 */

int
Tcl_LrepeatObjCmd(
    ClientData dummy,		/* Not used. */
    Tcl_Interp *interp,		/* Current interpreter. */
    register int objc,		/* Number of arguments. */
    register Tcl_Obj *CONST objv[])
				/* The argument objects. */
{
    int elementCount, i, result;
    Tcl_Obj *listPtr, **dataArray;
    List *listRepPtr;

    /*
     * Check arguments for legality:
     *		lrepeat posInt value ?value ...?
     */

    if (objc < 3) {
	Tcl_WrongNumArgs(interp, 1, objv, "positiveCount value ?value ...?");
	return TCL_ERROR;
    }
    result = TclGetIntFromObj(interp, objv[1], &elementCount);
    if (result == TCL_ERROR) {
	return TCL_ERROR;
    }
    if (elementCount < 1) {
	Tcl_AppendResult(interp, "must have a count of at least 1", NULL);
	return TCL_ERROR;
    }

    /*
     * Skip forward to the interesting arguments now we've finished parsing.
     */

    objc -= 2;
    objv += 2;

    /*
     * Get an empty list object that is allocated large enough to hold each
     * init value elementCount times.
     */

    listPtr = Tcl_NewListObj(elementCount*objc, NULL);
    listRepPtr = (List *) listPtr->internalRep.twoPtrValue.ptr1;
    listRepPtr->elemCount = elementCount*objc;
    dataArray = &listRepPtr->elements;

    /*
     * Set the elements. Note that we handle the common degenerate case of a
     * single value being repeated separately to permit the compiler as much
     * room as possible to optimize a loop that might be run a very large
     * number of times.
     */

    if (objc == 1) {
	register Tcl_Obj *tmpPtr = objv[0];

	tmpPtr->refCount += elementCount;
	for (i=0 ; i<elementCount ; i++) {
	    dataArray[i] = tmpPtr;
	}
    } else {
	int j, k = 0;

	for (i=0 ; i<elementCount ; i++) {
	    for (j=0 ; j<objc ; j++) {
		Tcl_IncrRefCount(objv[j]);
		dataArray[k++] = objv[j];
	    }
	}
    }

    Tcl_SetObjResult(interp, listPtr);
    return TCL_OK;
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_LreplaceObjCmd --
 *
 *	This object-based procedure is invoked to process the "lreplace" Tcl
 *	command. See the user documentation for details on what it does.
 *
 * Results:
 *	A new Tcl list object formed by replacing zero or more elements of a
 *	list.
 *
 * Side effects:
 *	See the user documentation.
 *
 *----------------------------------------------------------------------
 */

int
Tcl_LreplaceObjCmd(
    ClientData dummy,		/* Not used. */
    Tcl_Interp *interp,		/* Current interpreter. */
    int objc,			/* Number of arguments. */
    Tcl_Obj *CONST objv[])	/* Argument objects. */
{
    register Tcl_Obj *listPtr;
    int first, last, listLen, numToDelete, result;

    if (objc < 4) {
	Tcl_WrongNumArgs(interp, 1, objv,
		"list first last ?element element ...?");
	return TCL_ERROR;
    }

    result = TclListObjLength(interp, objv[1], &listLen);
    if (result != TCL_OK) {
	return result;
    }

    /*
     * Get the first and last indexes. "end" is interpreted to be the index
     * for the last element, such that using it will cause that element to be
     * included for deletion.
     */

    result = TclGetIntForIndexM(interp, objv[2], /*end*/ listLen-1, &first);
    if (result != TCL_OK) {
	return result;
    }

    result = TclGetIntForIndexM(interp, objv[3], /*end*/ listLen-1, &last);
    if (result != TCL_OK) {
	return result;
    }

    if (first < 0) {
    	first = 0;
    }

    /*
     * Complain if the user asked for a start element that is greater than the
     * list length. This won't ever trigger for the "end-*" case as that will
     * be properly constrained by TclGetIntForIndex because we use listLen-1
     * (to allow for replacing the last elem).
     */

    if ((first >= listLen) && (listLen > 0)) {
	Tcl_AppendResult(interp, "list doesn't contain element ",
		TclGetString(objv[2]), NULL);
	return TCL_ERROR;
    }
    if (last >= listLen) {
    	last = (listLen - 1);
    }
    if (first <= last) {
	numToDelete = (last - first + 1);
    } else {
	numToDelete = 0;
    }

    /*
     * If the list object is unshared we can modify it directly, otherwise we
     * create a copy to modify: this is "copy on write".
     */

    listPtr = objv[1];
    if (Tcl_IsShared(listPtr)) {
	listPtr = TclListObjCopy(NULL, listPtr);
    }

    /*
     * Note that we call Tcl_ListObjReplace even when numToDelete == 0 and
     * objc == 4. In this case, the list value of listPtr is not changed (no
     * elements are removed or added), but by making the call we are assured
     * we end up with a list in canonical form. Resist any temptation to
     * optimize this case away.
     */

    Tcl_ListObjReplace(NULL, listPtr, first, numToDelete, objc-4, &(objv[4]));

    /*
     * Set the interpreter's object result.
     */

    Tcl_SetObjResult(interp, listPtr);
    return TCL_OK;
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_LreverseObjCmd --
 *
 *	This procedure is invoked to process the "lreverse" Tcl command. See
 *	the user documentation for details on what it does.
 *
 * Results:
 *	A standard Tcl result.
 *
 * Side effects:
 *	See the user documentation.
 *
 *----------------------------------------------------------------------
 */

int
Tcl_LreverseObjCmd(
    ClientData clientData,	/* Not used. */
    Tcl_Interp *interp,		/* Current interpreter. */
    int objc,			/* Number of arguments. */
    Tcl_Obj *CONST objv[])	/* Argument values. */
{
    Tcl_Obj **elemv;
    int elemc, i, j;

    if (objc != 2) {
	Tcl_WrongNumArgs(interp, 1, objv, "list");
	return TCL_ERROR;
    }
    if (TclListObjGetElements(interp, objv[1], &elemc, &elemv) != TCL_OK) {
	return TCL_ERROR;
    }

    /*
     * If the list is empty, just return it [Bug 1876793]
     */

    if (!elemc) {
	Tcl_SetObjResult(interp, objv[1]);
	return TCL_OK;
    }

    if (Tcl_IsShared(objv[1])) {
	Tcl_Obj *resultObj, **dataArray;
	List *listPtr;

    makeNewReversedList:
	resultObj = Tcl_NewListObj(elemc, NULL);
	listPtr = (List *) resultObj->internalRep.twoPtrValue.ptr1;
	listPtr->elemCount = elemc;
	dataArray = &listPtr->elements;

	for (i=0,j=elemc-1 ; i<elemc ; i++,j--) {
	    dataArray[j] = elemv[i];
	    Tcl_IncrRefCount(elemv[i]);
	}

	Tcl_SetObjResult(interp, resultObj);
    } else {
	/*
	 * It is theoretically possible for a list object to have a shared
	 * internal representation, but be an unshared object. Check for this
	 * and use the "shared" code if we have that problem. [Bug 1675044]
	 */

	if (((List *) objv[1]->internalRep.twoPtrValue.ptr1)->refCount > 1) {
	    goto makeNewReversedList;
	}

	/*
	 * Not shared, so swap "in place". This relies on Tcl_LOGE above
	 * returning a pointer to the live array of Tcl_Obj values.
	 */

	for (i=0,j=elemc-1 ; i<j ; i++,j--) {
	    Tcl_Obj *tmp = elemv[i];

	    elemv[i] = elemv[j];
	    elemv[j] = tmp;
	}
	TclInvalidateStringRep(objv[1]);
	Tcl_SetObjResult(interp, objv[1]);
    }
    return TCL_OK;
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_LsearchObjCmd --
 *
 *	This procedure is invoked to process the "lsearch" Tcl command. See
 *	the user documentation for details on what it does.
 *
 * Results:
 *	A standard Tcl result.
 *
 * Side effects:
 *	See the user documentation.
 *
 *----------------------------------------------------------------------
 */

int
Tcl_LsearchObjCmd(
    ClientData clientData,	/* Not used. */
    Tcl_Interp *interp,		/* Current interpreter. */
    int objc,			/* Number of arguments. */
    Tcl_Obj *CONST objv[])	/* Argument values. */
{
    char *bytes, *patternBytes;
    int i, match, mode, index, result, listc, length, elemLen;
    int dataType, isIncreasing, lower, upper, patInt, objInt, offset;
    int allMatches, inlineReturn, negatedMatch, returnSubindices, noCase;
    double patDouble, objDouble;
    SortInfo sortInfo;
    Tcl_Obj *patObj, **listv, *listPtr, *startPtr, *itemPtr;
    SortStrCmpFn_t strCmpFn = strcmp;
    Tcl_RegExp regexp = NULL;
    static CONST char *options[] = {
	"-all",	    "-ascii",   "-decreasing", "-dictionary",
	"-exact",   "-glob",    "-increasing", "-index",
	"-inline",  "-integer", "-nocase",     "-not",
	"-real",    "-regexp",  "-sorted",     "-start",
	"-subindices", NULL
    };
    enum options {
	LSEARCH_ALL, LSEARCH_ASCII, LSEARCH_DECREASING, LSEARCH_DICTIONARY,
	LSEARCH_EXACT, LSEARCH_GLOB, LSEARCH_INCREASING, LSEARCH_INDEX,
	LSEARCH_INLINE, LSEARCH_INTEGER, LSEARCH_NOCASE, LSEARCH_NOT,
	LSEARCH_REAL, LSEARCH_REGEXP, LSEARCH_SORTED, LSEARCH_START,
	LSEARCH_SUBINDICES
    };
    enum datatypes {
	ASCII, DICTIONARY, INTEGER, REAL
    };
    enum modes {
	EXACT, GLOB, REGEXP, SORTED
    };

    mode = GLOB;
    dataType = ASCII;
    isIncreasing = 1;
    allMatches = 0;
    inlineReturn = 0;
    returnSubindices = 0;
    negatedMatch = 0;
    listPtr = NULL;
    startPtr = NULL;
    offset = 0;
    noCase = 0;
    sortInfo.compareCmdPtr = NULL;
    sortInfo.isIncreasing = 1;
    sortInfo.sortMode = 0;
    sortInfo.interp = interp;
    sortInfo.resultCode = TCL_OK;
    sortInfo.indexv = NULL;
    sortInfo.indexc = 0;

    if (objc < 3) {
	Tcl_WrongNumArgs(interp, 1, objv, "?options? list pattern");
	return TCL_ERROR;
    }

    for (i = 1; i < objc-2; i++) {
	if (Tcl_GetIndexFromObj(interp, objv[i], options, "option", 0, &index)
		!= TCL_OK) {
	    if (startPtr != NULL) {
		Tcl_DecrRefCount(startPtr);
	    }
	    if (sortInfo.indexc > 1) {
		ckfree((char *) sortInfo.indexv);
	    }
	    return TCL_ERROR;
	}
	switch ((enum options) index) {
	case LSEARCH_ALL:		/* -all */
	    allMatches = 1;
	    break;
	case LSEARCH_ASCII:		/* -ascii */
	    dataType = ASCII;
	    break;
	case LSEARCH_DECREASING:	/* -decreasing */
	    isIncreasing = 0;
	    sortInfo.isIncreasing = 0;
	    break;
	case LSEARCH_DICTIONARY:	/* -dictionary */
	    dataType = DICTIONARY;
	    break;
	case LSEARCH_EXACT:		/* -increasing */
	    mode = EXACT;
	    break;
	case LSEARCH_GLOB:		/* -glob */
	    mode = GLOB;
	    break;
	case LSEARCH_INCREASING:	/* -increasing */
	    isIncreasing = 1;
	    sortInfo.isIncreasing = 1;
	    break;
	case LSEARCH_INLINE:		/* -inline */
	    inlineReturn = 1;
	    break;
	case LSEARCH_INTEGER:		/* -integer */
	    dataType = INTEGER;
	    break;
	case LSEARCH_NOCASE:		/* -nocase */
	    strCmpFn = strcasecmp;
	    noCase = 1;
	    break;
	case LSEARCH_NOT:		/* -not */
	    negatedMatch = 1;
	    break;
	case LSEARCH_REAL:		/* -real */
	    dataType = REAL;
	    break;
	case LSEARCH_REGEXP:		/* -regexp */
	    mode = REGEXP;
	    break;
	case LSEARCH_SORTED:		/* -sorted */
	    mode = SORTED;
	    break;
	case LSEARCH_SUBINDICES:	/* -subindices */
	    returnSubindices = 1;
	    break;
	case LSEARCH_START:		/* -start */
	    /*
	     * If there was a previous -start option, release its saved index
	     * because it will either be replaced or there will be an error.
	     */

	    if (startPtr != NULL) {
		Tcl_DecrRefCount(startPtr);
	    }
	    if (i > objc-4) {
		if (sortInfo.indexc > 1) {
		    ckfree((char *) sortInfo.indexv);
		}
		Tcl_AppendResult(interp, "missing starting index", NULL);
		return TCL_ERROR;
	    }
	    i++;
	    if (objv[i] == objv[objc - 2]) {
		/*
		 * Take copy to prevent shimmering problems. Note that it does
		 * not matter if the index obj is also a component of the list
		 * being searched. We only need to copy where the list and the
		 * index are one-and-the-same.
		 */

		startPtr = Tcl_DuplicateObj(objv[i]);
	    } else {
		startPtr = objv[i];
		Tcl_IncrRefCount(startPtr);
	    }
	    break;
	case LSEARCH_INDEX: {		/* -index */
	    Tcl_Obj **indices;
	    int j;

	    if (sortInfo.indexc > 1) {
		ckfree((char *) sortInfo.indexv);
	    }
	    if (i > objc-4) {
		if (startPtr != NULL) {
		    Tcl_DecrRefCount(startPtr);
		}
		Tcl_AppendResult(interp,
			"\"-index\" option must be followed by list index",
			NULL);
		return TCL_ERROR;
	    }

	    /*
	     * Store the extracted indices for processing by sublist
	     * extraction. Note that we don't do this using objects because
	     * that has shimmering problems.
	     */

	    i++;
	    if (TclListObjGetElements(interp, objv[i],
		    &sortInfo.indexc, &indices) != TCL_OK) {
		if (startPtr != NULL) {
		    Tcl_DecrRefCount(startPtr);
		}
		return TCL_ERROR;
	    }
	    switch (sortInfo.indexc) {
	    case 0:
		sortInfo.indexv = NULL;
		break;
	    case 1:
		sortInfo.indexv = &sortInfo.singleIndex;
		break;
	    default:
		sortInfo.indexv = (int *)
			ckalloc(sizeof(int) * sortInfo.indexc);
	    }

	    /*
	     * Fill the array by parsing each index. We don't know whether
	     * their scale is sensible yet, but we at least perform the
	     * syntactic check here.
	     */

	    for (j=0 ; j<sortInfo.indexc ; j++) {
		if (TclGetIntForIndexM(interp, indices[j], SORTIDX_END,
			&sortInfo.indexv[j]) != TCL_OK) {
		    if (sortInfo.indexc > 1) {
			ckfree((char *) sortInfo.indexv);
		    }
		    Tcl_AppendObjToErrorInfo(interp, Tcl_ObjPrintf(
			    "\n    (-index option item number %d)", j));
		    return TCL_ERROR;
		}
	    }
	    break;
	}
	}
    }

    /*
     * Subindices only make sense if asked for with -index option set.
     */

    if (returnSubindices && sortInfo.indexc==0) {
	if (startPtr != NULL) {
	    Tcl_DecrRefCount(startPtr);
	}
	Tcl_AppendResult(interp,
		"-subindices cannot be used without -index option", NULL);
	return TCL_ERROR;
    }

    if ((enum modes) mode == REGEXP) {
	/*
	 * We can shimmer regexp/list if listv[i] == pattern, so get the
	 * regexp rep before the list rep. First time round, omit the interp
	 * and hope that the compilation will succeed. If it fails, we'll
	 * recompile in "expensive" mode with a place to put error messages.
	 */

	regexp = Tcl_GetRegExpFromObj(NULL, objv[objc - 1],
		TCL_REG_ADVANCED | TCL_REG_NOSUB |
		(noCase ? TCL_REG_NOCASE : 0));
	if (regexp == NULL) {
	    /*
	     * Failed to compile the RE. Try again without the TCL_REG_NOSUB
	     * flag in case the RE had sub-expressions in it [Bug 1366683]. If
	     * this fails, an error message will be left in the interpreter.
	     */

	    regexp = Tcl_GetRegExpFromObj(interp, objv[objc - 1],
		    TCL_REG_ADVANCED | (noCase ? TCL_REG_NOCASE : 0));
	}

	if (regexp == NULL) {
	    if (startPtr != NULL) {
		Tcl_DecrRefCount(startPtr);
	    }
	    if (sortInfo.indexc > 1) {
		ckfree((char *) sortInfo.indexv);
	    }
	    return TCL_ERROR;
	}
    }

    /*
     * Make sure the list argument is a list object and get its length and a
     * pointer to its array of element pointers.
     */

    result = TclListObjGetElements(interp, objv[objc - 2], &listc, &listv);
    if (result != TCL_OK) {
	if (startPtr != NULL) {
	    Tcl_DecrRefCount(startPtr);
	}
	if (sortInfo.indexc > 1) {
	    ckfree((char *) sortInfo.indexv);
	}
	return result;
    }

    /*
     * Get the user-specified start offset.
     */

    if (startPtr) {
	result = TclGetIntForIndexM(interp, startPtr, listc-1, &offset);
	Tcl_DecrRefCount(startPtr);
	if (result != TCL_OK) {
	    if (sortInfo.indexc > 1) {
		ckfree((char *) sortInfo.indexv);
	    }
	    return result;
	}
	if (offset < 0) {
	    offset = 0;
	}

	/*
	 * If the search started past the end of the list, we just return a
	 * "did not match anything at all" result straight away. [Bug 1374778]
	 */

	if (offset > listc-1) {
	    if (sortInfo.indexc > 1) {
		ckfree((char *) sortInfo.indexv);
	    }
	    if (allMatches || inlineReturn) {
		Tcl_ResetResult(interp);
	    } else {
		Tcl_SetObjResult(interp, Tcl_NewIntObj(-1));
	    }
	    return TCL_OK;
	}
    }

    patObj = objv[objc - 1];
    patternBytes = NULL;
    if ((enum modes) mode == EXACT || (enum modes) mode == SORTED) {
	switch ((enum datatypes) dataType) {
	case ASCII:
	case DICTIONARY:
	    patternBytes = TclGetStringFromObj(patObj, &length);
	    break;
	case INTEGER:
	    result = TclGetIntFromObj(interp, patObj, &patInt);
	    if (result != TCL_OK) {
		if (sortInfo.indexc > 1) {
		    ckfree((char *) sortInfo.indexv);
		}
		return result;
	    }

	    /*
	     * List representation might have been shimmered; restore it. [Bug
	     * 1844789]
	     */

	    TclListObjGetElements(NULL, objv[objc - 2], &listc, &listv);
	    break;
	case REAL:
	    result = Tcl_GetDoubleFromObj(interp, patObj, &patDouble);
	    if (result != TCL_OK) {
		if (sortInfo.indexc > 1) {
		    ckfree((char *) sortInfo.indexv);
		}
		return result;
	    }

	    /*
	     * List representation might have been shimmered; restore it. [Bug
	     * 1844789]
	     */

	    TclListObjGetElements(NULL, objv[objc - 2], &listc, &listv);
	    break;
	}
    } else {
	patternBytes = TclGetStringFromObj(patObj, &length);
    }

    /*
     * Set default index value to -1, indicating failure; if we find the item
     * in the course of our search, index will be set to the correct value.
     */

    index = -1;
    match = 0;

    if ((enum modes) mode == SORTED && !allMatches && !negatedMatch) {
	/*
	 * If the data is sorted, we can do a more intelligent search. Note
	 * that there is no point in being smart when -all was specified; in
	 * that case, we have to look at all items anyway, and there is no
	 * sense in doing this when the match sense is inverted.
	 */

	lower = offset - 1;
	upper = listc;
	while (lower + 1 != upper && sortInfo.resultCode == TCL_OK) {
	    i = (lower + upper)/2;
	    if (sortInfo.indexc != 0) {
		itemPtr = SelectObjFromSublist(listv[i], &sortInfo);
		if (sortInfo.resultCode != TCL_OK) {
		    if (sortInfo.indexc > 1) {
			ckfree((char *) sortInfo.indexv);
		    }
		    return sortInfo.resultCode;
		}
	    } else {
		itemPtr = listv[i];
	    }
	    switch ((enum datatypes) dataType) {
	    case ASCII:
		bytes = TclGetString(itemPtr);
		match = strCmpFn(patternBytes, bytes);
		break;
	    case DICTIONARY:
		bytes = TclGetString(itemPtr);
		match = DictionaryCompare(patternBytes, bytes);
		break;
	    case INTEGER:
		result = TclGetIntFromObj(interp, itemPtr, &objInt);
		if (result != TCL_OK) {
		    if (sortInfo.indexc > 1) {
			ckfree((char *) sortInfo.indexv);
		    }
		    return result;
		}
		if (patInt == objInt) {
		    match = 0;
		} else if (patInt < objInt) {
		    match = -1;
		} else {
		    match = 1;
		}
		break;
	    case REAL:
		result = Tcl_GetDoubleFromObj(interp, itemPtr, &objDouble);
		if (result != TCL_OK) {
		    if (sortInfo.indexc > 1) {
			ckfree((char *) sortInfo.indexv);
		    }
		    return result;
		}
		if (patDouble == objDouble) {
		    match = 0;
		} else if (patDouble < objDouble) {
		    match = -1;
		} else {
		    match = 1;
		}
		break;
	    }
	    if (match == 0) {
		/*
		 * Normally, binary search is written to stop when it finds a
		 * match. If there are duplicates of an element in the list,
		 * our first match might not be the first occurance.
		 * Consider: 0 0 0 1 1 1 2 2 2
		 *
		 * To maintain consistancy with standard lsearch semantics, we
		 * must find the leftmost occurance of the pattern in the
		 * list. Thus we don't just stop searching here. This
		 * variation means that a search always makes log n
		 * comparisons (normal binary search might "get lucky" with an
		 * early comparison).
		 */

		index = i;
		upper = i;
	    } else if (match > 0) {
		if (isIncreasing) {
		    lower = i;
		} else {
		    upper = i;
		}
	    } else {
		if (isIncreasing) {
		    upper = i;
		} else {
		    lower = i;
		}
	    }
	}

    } else {
	/*
	 * We need to do a linear search, because (at least one) of:
	 *   - our matcher can only tell equal vs. not equal
	 *   - our matching sense is negated
	 *   - we're building a list of all matched items
	 */

	if (allMatches) {
	    listPtr = Tcl_NewListObj(0, NULL);
	}
	for (i = offset; i < listc; i++) {
	    match = 0;
	    if (sortInfo.indexc != 0) {	    
		itemPtr = SelectObjFromSublist(listv[i], &sortInfo);
		if (sortInfo.resultCode != TCL_OK) {
		    if (listPtr != NULL) {
			Tcl_DecrRefCount(listPtr);
		    }
		    if (sortInfo.indexc > 1) {
			ckfree((char *) sortInfo.indexv);
		    }
		    return sortInfo.resultCode;
		}
	    } else {
		itemPtr = listv[i];
	    }
		
	    switch ((enum modes) mode) {
	    case SORTED:
	    case EXACT:
		switch ((enum datatypes) dataType) {
		case ASCII:
		    bytes = TclGetStringFromObj(itemPtr, &elemLen);
		    if (length == elemLen) {
			/*
			 * This split allows for more optimal compilation of
			 * memcmp/strcasecmp.
			 */

			if (noCase) {
			    match = (strcasecmp(bytes, patternBytes) == 0);
			} else {
			    match = (memcmp(bytes, patternBytes,
				    (size_t) length) == 0);
			}
		    }
		    break;

		case DICTIONARY:
		    bytes = TclGetString(itemPtr);
		    match = (DictionaryCompare(bytes, patternBytes) == 0);
		    break;

		case INTEGER:
		    result = TclGetIntFromObj(interp, itemPtr, &objInt);
		    if (result != TCL_OK) {
			if (listPtr != NULL) {
			    Tcl_DecrRefCount(listPtr);
			}
			if (sortInfo.indexc > 1) {
			    ckfree((char *) sortInfo.indexv);
			}
			return result;
		    }
		    match = (objInt == patInt);
		    break;

		case REAL:
		    result = Tcl_GetDoubleFromObj(interp,itemPtr, &objDouble);
		    if (result != TCL_OK) {
			if (listPtr) {
			    Tcl_DecrRefCount(listPtr);
			}
			if (sortInfo.indexc > 1) {
			    ckfree((char *) sortInfo.indexv);
			}
			return result;
		    }
		    match = (objDouble == patDouble);
		    break;
		}
		break;

	    case GLOB:
		match = Tcl_StringCaseMatch(TclGetString(itemPtr),
			patternBytes, noCase);
		break;

	    case REGEXP:
		match = Tcl_RegExpExecObj(interp, regexp, itemPtr, 0, 0, 0);
		if (match < 0) {
		    Tcl_DecrRefCount(patObj);
		    if (listPtr != NULL) {
			Tcl_DecrRefCount(listPtr);
		    }
		    if (sortInfo.indexc > 1) {
			ckfree((char *) sortInfo.indexv);
		    }
		    return TCL_ERROR;
		}
		break;
	    }

	    /*
	     * Invert match condition for -not.
	     */

	    if (negatedMatch) {
		match = !match;
	    }
	    if (!match) {
		continue;
	    }
	    if (!allMatches) {
		index = i;
		break;
	    } else if (inlineReturn) {
		/*
		 * Note that these appends are not expected to fail.
		 */

		if (returnSubindices && (sortInfo.indexc != 0)) {
		    itemPtr = SelectObjFromSublist(listv[i], &sortInfo);
		} else {
		    itemPtr = listv[i];
		}
		Tcl_ListObjAppendElement(interp, listPtr, itemPtr);
	    } else if (returnSubindices) {
		int j;

		itemPtr = Tcl_NewIntObj(i);
		for (j=0 ; j<sortInfo.indexc ; j++) {
		    Tcl_ListObjAppendElement(interp, itemPtr,
			    Tcl_NewIntObj(sortInfo.indexv[j]));
		}
		Tcl_ListObjAppendElement(interp, listPtr, itemPtr);
	    } else {
		Tcl_ListObjAppendElement(interp, listPtr, Tcl_NewIntObj(i));
	    }
	}
    }

    /*
     * Return everything or a single value.
     */

    if (allMatches) {
	Tcl_SetObjResult(interp, listPtr);
    } else if (!inlineReturn) {
	if (returnSubindices) {
	    int j;

	    itemPtr = Tcl_NewIntObj(index);
	    for (j=0 ; j<sortInfo.indexc ; j++) {
		Tcl_ListObjAppendElement(interp, itemPtr,
			Tcl_NewIntObj(sortInfo.indexv[j]));
	    }
	    Tcl_SetObjResult(interp, itemPtr);
	} else {
	    Tcl_SetObjResult(interp, Tcl_NewIntObj(index));
	}
    } else if (index < 0) {
	/*
	 * Is this superfluous? The result should be a blank object by
	 * default...
	 */

	Tcl_SetObjResult(interp, Tcl_NewObj());
    } else {
	Tcl_SetObjResult(interp, listv[index]);
    }

    /*
     * Cleanup the index list array.
     */

    if (sortInfo.indexc > 1) {
	ckfree((char *) sortInfo.indexv);
    }
    return TCL_OK;
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_LsetObjCmd --
 *
 *	This procedure is invoked to process the "lset" Tcl command. See the
 *	user documentation for details on what it does.
 *
 * Results:
 *	A standard Tcl result.
 *
 * Side effects:
 *	See the user documentation.
 *
 *----------------------------------------------------------------------
 */

int
Tcl_LsetObjCmd(
    ClientData clientData,	/* Not used. */
    Tcl_Interp *interp,		/* Current interpreter. */
    int objc,			/* Number of arguments. */
    Tcl_Obj *CONST objv[])	/* Argument values. */
{
    Tcl_Obj *listPtr;		/* Pointer to the list being altered. */
    Tcl_Obj *finalValuePtr;	/* Value finally assigned to the variable. */

    /*
     * Check parameter count.
     */

    if (objc < 3) {
	Tcl_WrongNumArgs(interp, 1, objv, "listVar index ?index...? value");
	return TCL_ERROR;
    }

    /*
     * Look up the list variable's value.
     */

    listPtr = Tcl_ObjGetVar2(interp, objv[1], (Tcl_Obj *) NULL,
	    TCL_LEAVE_ERR_MSG);
    if (listPtr == NULL) {
	return TCL_ERROR;
    }

    /*
     * Substitute the value in the value. Return either the value or else an
     * unshared copy of it.
     */

    if (objc == 4) {
	finalValuePtr = TclLsetList(interp, listPtr, objv[2], objv[3]);
    } else {
	finalValuePtr = TclLsetFlat(interp, listPtr, objc-3, objv+2,
		objv[objc-1]);
    }

    /*
     * If substitution has failed, bail out.
     */

    if (finalValuePtr == NULL) {
	return TCL_ERROR;
    }

    /*
     * Finally, update the variable so that traces fire.
     */

    listPtr = Tcl_ObjSetVar2(interp, objv[1], NULL, finalValuePtr,
	    TCL_LEAVE_ERR_MSG);
    Tcl_DecrRefCount(finalValuePtr);
    if (listPtr == NULL) {
	return TCL_ERROR;
    }

    /*
     * Return the new value of the variable as the interpreter result.
     */

    Tcl_SetObjResult(interp, listPtr);
    return TCL_OK;
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_LsortObjCmd --
 *
 *	This procedure is invoked to process the "lsort" Tcl command. See the
 *	user documentation for details on what it does.
 *
 * Results:
 *	A standard Tcl result.
 *
 * Side effects:
 *	See the user documentation.
 *
 *----------------------------------------------------------------------
 */

int
Tcl_LsortObjCmd(
    ClientData clientData,	/* Not used. */
    Tcl_Interp *interp,		/* Current interpreter. */
    int objc,			/* Number of arguments. */
    Tcl_Obj *CONST objv[])	/* Argument values. */
{
    int i, j, index, unique, indices, length, nocase = 0, sortMode, indexc;
    Tcl_Obj *resultPtr, *cmdPtr, **listObjPtrs, *listObj, *indexPtr;
    SortElement *elementArray, *elementPtr;
    SortInfo sortInfo;		/* Information about this sort that needs to
				 * be passed to the comparison function. */
    static CONST char *switches[] = {
	"-ascii", "-command", "-decreasing", "-dictionary", "-increasing",
	"-index", "-indices", "-integer", "-nocase", "-real", "-unique", NULL
    };
    enum Lsort_Switches {
	LSORT_ASCII, LSORT_COMMAND, LSORT_DECREASING, LSORT_DICTIONARY,
	LSORT_INCREASING, LSORT_INDEX, LSORT_INDICES, LSORT_INTEGER,
	LSORT_NOCASE, LSORT_REAL, LSORT_UNIQUE
    };

    /*
     * The subList array below holds pointers to temporary lists built during
     * the merge sort. Element i of the array holds a list of length 2**i.
     */
#   define NUM_LISTS 30
    SortElement *subList[NUM_LISTS+1];

    if (objc < 2) {
	Tcl_WrongNumArgs(interp, 1, objv, "?options? list");
	return TCL_ERROR;
    }

    /*
     * Parse arguments to set up the mode for the sort.
     */

    sortInfo.isIncreasing = 1;
    sortInfo.sortMode = SORTMODE_ASCII;
    sortInfo.indexv = NULL;
    sortInfo.indexc = 0;
    sortInfo.unique = 0;
    sortInfo.interp = interp;
    sortInfo.resultCode = TCL_OK;    
    cmdPtr = NULL;
    unique = 0;
    indices = 0;
    for (i = 1; i < objc-1; i++) {
	if (Tcl_GetIndexFromObj(interp, objv[i], switches, "option", 0,
		&index) != TCL_OK) {
	    return TCL_ERROR;
	}
	switch ((enum Lsort_Switches) index) {
	case LSORT_ASCII:
	    sortInfo.sortMode = SORTMODE_ASCII;
	    break;
	case LSORT_COMMAND:
	    if (i == (objc-2)) {
		if (sortInfo.indexc > 1) {
		    ckfree((char *) sortInfo.indexv);
		}
		Tcl_AppendResult(interp,
			"\"-command\" option must be followed "
			"by comparison command", NULL);
		return TCL_ERROR;
	    }
	    sortInfo.sortMode = SORTMODE_COMMAND;
	    cmdPtr = objv[i+1];
	    i++;
	    break;
	case LSORT_DECREASING:
	    sortInfo.isIncreasing = 0;
	    break;
	case LSORT_DICTIONARY:
	    sortInfo.sortMode = SORTMODE_DICTIONARY;
	    break;
	case LSORT_INCREASING:
	    sortInfo.isIncreasing = 1;
	    break;
	case LSORT_INDEX: {
	    Tcl_Obj **indices;

	    if (sortInfo.indexc > 1) {
		ckfree((char *) sortInfo.indexv);
	    }
	    if (i == (objc-2)) {
		Tcl_AppendResult(interp, "\"-index\" option must be "
			"followed by list index", NULL);
		return TCL_ERROR;
	    }

	    /*
	     * Take copy to prevent shimmering problems.
	     */

	    if (TclListObjGetElements(interp, objv[i+1], &sortInfo.indexc,
		    &indices) != TCL_OK) {
		return TCL_ERROR;
	    }
	    switch (sortInfo.indexc) {
	    case 0:
		sortInfo.indexv = NULL;
		break;
	    case 1:
		sortInfo.indexv = &sortInfo.singleIndex;
		break;
	    default:
		sortInfo.indexv = (int *)
			ckalloc(sizeof(int) * sortInfo.indexc);
	    }

	    /*
	     * Fill the array by parsing each index. We don't know whether
	     * their scale is sensible yet, but we at least perform the
	     * syntactic check here.
	     */

	    for (j=0 ; j<sortInfo.indexc ; j++) {
		if (TclGetIntForIndexM(interp, indices[j], SORTIDX_END,
			&sortInfo.indexv[j]) != TCL_OK) {
		    if (sortInfo.indexc > 1) {
			ckfree((char *) sortInfo.indexv);
		    }
		    Tcl_AppendObjToErrorInfo(interp, Tcl_ObjPrintf(
			    "\n    (-index option item number %d)", j));
		    return TCL_ERROR;
		}
	    }
	    i++;
	    break;
	}
	case LSORT_INTEGER:
	    sortInfo.sortMode = SORTMODE_INTEGER;
	    break;
	case LSORT_NOCASE:
	    nocase = 1;
	    break;
	case LSORT_REAL:
	    sortInfo.sortMode = SORTMODE_REAL;
	    break;
	case LSORT_UNIQUE:
	    unique = 1;
	    sortInfo.unique = 1;
	    break;
	case LSORT_INDICES:
	    indices = 1;
	    break;
	}
    }
    if (nocase && (sortInfo.sortMode == SORTMODE_ASCII)) {
	sortInfo.sortMode = SORTMODE_ASCII_NC;
    }

    listObj = objv[objc-1];

    if (sortInfo.sortMode == SORTMODE_COMMAND) {
	Tcl_Obj *newCommandPtr, *newObjPtr;

	/*
	 * When sorting using a command, we are reentrant and therefore might
	 * have the representation of the list being sorted shimmered out from
	 * underneath our feet. Take a copy (cheap) to prevent this. [Bug
	 * 1675116]
	 */

	listObj = TclListObjCopy(interp, listObj);
	if (listObj == NULL) {
	    if (sortInfo.indexc > 1) {
		ckfree((char *) sortInfo.indexv);
	    }
	    return TCL_ERROR;
	}

	/*
	 * The existing command is a list. We want to flatten it, append two
	 * dummy arguments on the end, and replace these arguments later.
	 */

	newCommandPtr = Tcl_DuplicateObj(cmdPtr);
	TclNewObj(newObjPtr);
	Tcl_IncrRefCount(newCommandPtr);
	if (Tcl_ListObjAppendElement(interp, newCommandPtr, newObjPtr)
		!= TCL_OK) {
	    TclDecrRefCount(newCommandPtr);
	    TclDecrRefCount(listObj);
	    Tcl_IncrRefCount(newObjPtr);
	    TclDecrRefCount(newObjPtr);
	    if (sortInfo.indexc > 1) {
		ckfree((char *) sortInfo.indexv);
	    }
	    return TCL_ERROR;
	}
	Tcl_ListObjAppendElement(interp, newCommandPtr, Tcl_NewObj());
	sortInfo.compareCmdPtr = newCommandPtr;
    }

    sortInfo.resultCode = TclListObjGetElements(interp, listObj,
	    &length, &listObjPtrs);
    if (sortInfo.resultCode != TCL_OK || length <= 0) {
	goto done;
    }
    sortInfo.numElements = length;
    
    indexc = sortInfo.indexc;
    sortMode = sortInfo.sortMode;
    if ((sortMode == SORTMODE_ASCII_NC)
	    || (sortMode == SORTMODE_DICTIONARY)) {
	/*
	 * For this function's purpose all string-based modes are equivalent
	 */
	
	sortMode = SORTMODE_ASCII;
    }

    /*
     * Initialize the sublists. After the following loop, subList[i] will
     * contain a sorted sublist of length 2**i. Use one extra subList at the
     * end, always at NULL, to indicate the end of the lists.
     */
    
    for (j=0 ; j<=NUM_LISTS ; j++) {
	subList[j] = NULL;
    }

    /*
     * The following loop creates a SortElement for each list element and
     * begins sorting it into the sublists as it appears.
     */

    elementArray = (SortElement *) ckalloc( length * sizeof(SortElement));

    for (i=0; i < length; i++){
	if (indexc) {
	    /*
	     * If this is an indexed sort, retrieve the corresponding element
	     */
	    indexPtr = SelectObjFromSublist(listObjPtrs[i], &sortInfo);
	    if (sortInfo.resultCode != TCL_OK) {
		goto done1;
	    }
	} else {
	    indexPtr = listObjPtrs[i];
	}

	/*
	 * Determine the "value" of this object for sorting purposes
	 */
	
	if (sortMode == SORTMODE_ASCII) {
	    elementArray[i].index.strValuePtr = TclGetString(indexPtr);
	} else if (sortMode == SORTMODE_INTEGER) {
	    long a;
	    if (TclGetLongFromObj(sortInfo.interp, indexPtr, &a) != TCL_OK) {
		sortInfo.resultCode = TCL_ERROR;
		goto done1;
	    }
	    elementArray[i].index.intValue = a;
	} else if (sortInfo.sortMode == SORTMODE_REAL) {
	    double a;
	    if (Tcl_GetDoubleFromObj(sortInfo.interp, indexPtr, &a) != TCL_OK) {
		sortInfo.resultCode = TCL_ERROR;
		goto done1;
	    }
	    elementArray[i].index.doubleValue = a;
	} else {
	    elementArray[i].index.objValuePtr = indexPtr;
	}

	/*
	 * Determine the representation of this element in the result: either
	 * the objPtr itself, or its index in the original list.
	 */
	
	elementArray[i].objPtr = (indices ? INT2PTR(i) : listObjPtrs[i]);

	/*
	 * Merge this element in the pre-existing sublists (and merge together
	 * sublists when we have two of the same size).
	 */
	
	elementArray[i].nextPtr = NULL;
	elementPtr = &elementArray[i];
	for (j=0 ; subList[j] ; j++) {
	    elementPtr = MergeLists(subList[j], elementPtr, &sortInfo);
	    subList[j] = NULL;
	}
	if (j >= NUM_LISTS) {
	    j = NUM_LISTS-1;
	}
	subList[j] = elementPtr;
    }

    /*
     * Merge all sublists
     */
    
    elementPtr = subList[0];
    for (j=1 ; j<NUM_LISTS ; j++) {
	elementPtr = MergeLists(subList[j], elementPtr, &sortInfo);
    }


    /*
     * Now store the sorted elements in the result list.
     */
    
    if (sortInfo.resultCode == TCL_OK) {
	List *listRepPtr;
	Tcl_Obj **newArray, *objPtr;
	int i;
	
	resultPtr = Tcl_NewListObj(sortInfo.numElements, NULL);
	listRepPtr = (List *) resultPtr->internalRep.twoPtrValue.ptr1;
	newArray = &listRepPtr->elements;
	if (indices) {
	    for (i = 0; elementPtr != NULL ; elementPtr = elementPtr->nextPtr){
		objPtr = Tcl_NewIntObj(PTR2INT(elementPtr->objPtr));
		newArray[i++] = objPtr;
		Tcl_IncrRefCount(objPtr);
	    }
	} else {
	    for (i = 0; elementPtr != NULL ; elementPtr = elementPtr->nextPtr){
		objPtr = elementPtr->objPtr;
		newArray[i++] = objPtr;
		Tcl_IncrRefCount(objPtr);
	    }
	}
	listRepPtr->elemCount = i;
	Tcl_SetObjResult(interp, resultPtr);
    }

  done1:
    ckfree((char *)elementArray);

  done:
    if (sortInfo.sortMode == SORTMODE_COMMAND) {
	TclDecrRefCount(sortInfo.compareCmdPtr);
	TclDecrRefCount(listObj);
	sortInfo.compareCmdPtr = NULL;
    }
    if (sortInfo.indexc > 1) {
	ckfree((char *) sortInfo.indexv);
    }
    return sortInfo.resultCode;
}

/*
 *----------------------------------------------------------------------
 *
 * MergeLists -
 *
 *	This procedure combines two sorted lists of SortElement structures
 *	into a single sorted list.
 *
 * Results:
 *	The unified list of SortElement structures.
 *
 * Side effects:
 *      If infoPtr->unique is set then infoPtr->numElements may be updated.
 *	Possibly others, if a user-defined comparison command does something
 *      weird. 
 *
 * Note:
 *      If infoPtr->unique is set, the merge assumes that there are no
 *	"repeated" elements in each of the left and right lists. In that case,
 *	if any element of the left list is equivalent to one in the right list
 *	it is omitted from the merged list.
 *      This simplified mechanism works because of the special way
 *	our MergeSort creates the sublists to be merged and will fail to
 *	eliminate all repeats in the general case where they are already
 *	present in either the left or right list. A general code would need to
 *	skip adjacent initial repeats in the left and right lists before
 *	comparing their initial elements, at each step. 
 *----------------------------------------------------------------------
 */

static SortElement *
MergeLists(
    SortElement *leftPtr,	/* First list to be merged; may be NULL. */
    SortElement *rightPtr,	/* Second list to be merged; may be NULL. */
    SortInfo *infoPtr)		/* Information needed by the comparison
				 * operator. */
{
    SortElement *headPtr, *tailPtr;
    int cmp;

    if (leftPtr == NULL) {
	return rightPtr;
    }
    if (rightPtr == NULL) {
	return leftPtr;
    }
    cmp = SortCompare(leftPtr, rightPtr, infoPtr);
    if (cmp > 0 || (cmp == 0 && infoPtr->unique)) {
	if (cmp == 0) {
	    infoPtr->numElements--;
	    leftPtr = leftPtr->nextPtr;
	}
	tailPtr = rightPtr;
	rightPtr = rightPtr->nextPtr;
    } else {
	tailPtr = leftPtr;
	leftPtr = leftPtr->nextPtr;
    }
    headPtr = tailPtr;
    if (!infoPtr->unique) {
	while ((leftPtr != NULL) && (rightPtr != NULL)) {
	    cmp = SortCompare(leftPtr, rightPtr, infoPtr);
	    if (cmp > 0) {
		tailPtr->nextPtr = rightPtr;
		tailPtr = rightPtr;
		rightPtr = rightPtr->nextPtr;
	    } else {
		tailPtr->nextPtr = leftPtr;
		tailPtr = leftPtr;
		leftPtr = leftPtr->nextPtr;
	    }
	}
    } else {
	while ((leftPtr != NULL) && (rightPtr != NULL)) {
	    cmp = SortCompare(leftPtr, rightPtr, infoPtr);
	    if (cmp >= 0) {
		if (cmp == 0) {
		    infoPtr->numElements--;
		    leftPtr = leftPtr->nextPtr;
		}
		tailPtr->nextPtr = rightPtr;
		tailPtr = rightPtr;
		rightPtr = rightPtr->nextPtr;
	    } else {
		tailPtr->nextPtr = leftPtr;
		tailPtr = leftPtr;
		leftPtr = leftPtr->nextPtr;
	    }
	}
    }
    if (leftPtr != NULL) {
	tailPtr->nextPtr = leftPtr;
    } else {
	tailPtr->nextPtr = rightPtr;
    }
    return headPtr;
}

/*
 *----------------------------------------------------------------------
 *
 * SortCompare --
 *
 *	This procedure is invoked by MergeLists to determine the proper
 *	ordering between two elements.
 *
 * Results:
 *	A negative results means the the first element comes before the
 *	second, and a positive results means that the second element should
 *	come first. A result of zero means the two elements are equal and it
 *	doesn't matter which comes first.
 *
 * Side effects:
 *	None, unless a user-defined comparison command does something weird.
 *
 *----------------------------------------------------------------------
 */

static int
SortCompare(
    SortElement *elemPtr1, SortElement *elemPtr2,
				/* Values to be compared. */
    SortInfo *infoPtr)		/* Information passed from the top-level
				 * "lsort" command. */
{
    int order = 0;

    if (infoPtr->sortMode == SORTMODE_ASCII) {
	order = strcmp(elemPtr1->index.strValuePtr,
		elemPtr2->index.strValuePtr);
    } else if (infoPtr->sortMode == SORTMODE_ASCII_NC) {
	order = strcasecmp(elemPtr1->index.strValuePtr,
		elemPtr2->index.strValuePtr);
    } else if (infoPtr->sortMode == SORTMODE_DICTIONARY) {
	order = DictionaryCompare(elemPtr1->index.strValuePtr,
		elemPtr2->index.strValuePtr);
    } else if (infoPtr->sortMode == SORTMODE_INTEGER) {
	long a, b;

	a = elemPtr1->index.intValue;
	b = elemPtr2->index.intValue;
	order = ((a >= b) - (a <= b));
    } else if (infoPtr->sortMode == SORTMODE_REAL) {
	double a, b;

	a = elemPtr1->index.doubleValue;
	b = elemPtr2->index.doubleValue;
	order = ((a >= b) - (a <= b));
    } else {
	Tcl_Obj **objv, *paramObjv[2];
	int objc;
	Tcl_Obj *objPtr1, *objPtr2;

	if (infoPtr->resultCode != TCL_OK) {
	    /*
	     * Once an error has occurred, skip any future comparisons so as
	     * to preserve the error message in sortInterp->result.
	     */
	    
	    return 0;
	}


	objPtr1 = elemPtr1->index.objValuePtr;
	objPtr2 = elemPtr2->index.objValuePtr;
	
	paramObjv[0] = objPtr1;
	paramObjv[1] = objPtr2;

	/*
	 * We made space in the command list for the two things to compare.
	 * Replace them and evaluate the result.
	 */

	TclListObjLength(infoPtr->interp, infoPtr->compareCmdPtr, &objc);
	Tcl_ListObjReplace(infoPtr->interp, infoPtr->compareCmdPtr, objc - 2,
		2, 2, paramObjv);
	TclListObjGetElements(infoPtr->interp, infoPtr->compareCmdPtr,
		&objc, &objv);

	infoPtr->resultCode = Tcl_EvalObjv(infoPtr->interp, objc, objv, 0);

	if (infoPtr->resultCode != TCL_OK) {
	    Tcl_AddErrorInfo(infoPtr->interp,
		    "\n    (-compare command)");
	    return 0;
	}

	/*
	 * Parse the result of the command.
	 */

	if (TclGetIntFromObj(infoPtr->interp,
		Tcl_GetObjResult(infoPtr->interp), &order) != TCL_OK) {
	    Tcl_ResetResult(infoPtr->interp);
	    Tcl_AppendResult(infoPtr->interp,
		    "-compare command returned non-integer result", NULL);
	    infoPtr->resultCode = TCL_ERROR;
	    return 0;
	}
    }
    if (!infoPtr->isIncreasing) {
	order = -order;
    }
    return order;
}

/*
 *----------------------------------------------------------------------
 *
 * DictionaryCompare
 *
 *	This function compares two strings as if they were being used in an
 *	index or card catalog. The case of alphabetic characters is ignored,
 *	except to break ties. Thus "B" comes before "b" but after "a". Also,
 *	integers embedded in the strings compare in numerical order. In other
 *	words, "x10y" comes after "x9y", not * before it as it would when
 *	using strcmp().
 *
 * Results:
 *	A negative result means that the first element comes before the
 *	second, and a positive result means that the second element should
 *	come first. A result of zero means the two elements are equal and it
 *	doesn't matter which comes first.
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */

static int
DictionaryCompare(
    char *left, char *right)	/* The strings to compare. */
{
    Tcl_UniChar uniLeft, uniRight, uniLeftLower, uniRightLower;
    int diff, zeros;
    int secondaryDiff = 0;

    while (1) {
	if (isdigit(UCHAR(*right))		/* INTL: digit */
		&& isdigit(UCHAR(*left))) {	/* INTL: digit */
	    /*
	     * There are decimal numbers embedded in the two strings. Compare
	     * them as numbers, rather than strings. If one number has more
	     * leading zeros than the other, the number with more leading
	     * zeros sorts later, but only as a secondary choice.
	     */

	    zeros = 0;
	    while ((*right == '0') && (isdigit(UCHAR(right[1])))) {
		right++;
		zeros--;
	    }
	    while ((*left == '0') && (isdigit(UCHAR(left[1])))) {
		left++;
		zeros++;
	    }
	    if (secondaryDiff == 0) {
		secondaryDiff = zeros;
	    }

	    /*
	     * The code below compares the numbers in the two strings without
	     * ever converting them to integers. It does this by first
	     * comparing the lengths of the numbers and then comparing the
	     * digit values.
	     */

	    diff = 0;
	    while (1) {
		if (diff == 0) {
		    diff = UCHAR(*left) - UCHAR(*right);
		}
		right++;
		left++;
		if (!isdigit(UCHAR(*right))) {		/* INTL: digit */
		    if (isdigit(UCHAR(*left))) {	/* INTL: digit */
			return 1;
		    } else {
			/*
			 * The two numbers have the same length. See if their
			 * values are different.
			 */

			if (diff != 0) {
			    return diff;
			}
			break;
		    }
		} else if (!isdigit(UCHAR(*left))) {	/* INTL: digit */
		    return -1;
		}
	    }
	    continue;
	}

	/*
	 * Convert character to Unicode for comparison purposes. If either
	 * string is at the terminating null, do a byte-wise comparison and
	 * bail out immediately.
	 */

	if ((*left != '\0') && (*right != '\0')) {
	    left += Tcl_UtfToUniChar(left, &uniLeft);
	    right += Tcl_UtfToUniChar(right, &uniRight);

	    /*
	     * Convert both chars to lower for the comparison, because
	     * dictionary sorts are case insensitve. Covert to lower, not
	     * upper, so chars between Z and a will sort before A (where most
	     * other interesting punctuations occur).
	     */

	    uniLeftLower = Tcl_UniCharToLower(uniLeft);
	    uniRightLower = Tcl_UniCharToLower(uniRight);
	} else {
	    diff = UCHAR(*left) - UCHAR(*right);
	    break;
	}

	diff = uniLeftLower - uniRightLower;
	if (diff) {
	    return diff;
	}
	if (secondaryDiff == 0) {
	    if (Tcl_UniCharIsUpper(uniLeft) && Tcl_UniCharIsLower(uniRight)) {
		secondaryDiff = -1;
	    } else if (Tcl_UniCharIsUpper(uniRight)
		    && Tcl_UniCharIsLower(uniLeft)) {
		secondaryDiff = 1;
	    }
	}
    }
    if (diff == 0) {
	diff = secondaryDiff;
    }
    return diff;
}

/*
 *----------------------------------------------------------------------
 *
 * SelectObjFromSublist --
 *
 *	This procedure is invoked from lsearch and SortCompare. It is used for
 *	implementing the -index option, for the lsort and lsearch commands.
 *
 * Results:
 *	Returns NULL if a failure occurs, and sets the result in the infoPtr.
 *	Otherwise returns the Tcl_Obj* to the item.
 *
 * Side effects:
 *	None.
 *
 * Note:
 *	No reference counting is done, as the result is only used internally
 *	and never passed directly to user code.
 *
 *----------------------------------------------------------------------
 */

static Tcl_Obj *
SelectObjFromSublist(
    Tcl_Obj *objPtr,		/* Obj to select sublist from. */
    SortInfo *infoPtr)		/* Information passed from the top-level
				 * "lsearch" or "lsort" command. */
{
    int i;

    /*
     * Quick check for case when no "-index" option is there.
     */

    if (infoPtr->indexc == 0) {
	return objPtr;
    }

    /*
     * Iterate over the indices, traversing through the nested sublists as we
     * go.
     */

    for (i=0 ; i<infoPtr->indexc ; i++) {
	int listLen, index;
	Tcl_Obj *currentObj;

	if (TclListObjLength(infoPtr->interp, objPtr, &listLen) != TCL_OK) {
	    infoPtr->resultCode = TCL_ERROR;
	    return NULL;
	}
	index = infoPtr->indexv[i];

	/*
	 * Adjust for end-based indexing.
	 */

	if (index < SORTIDX_NONE) {
	    index += listLen + 1;
	}

	if (Tcl_ListObjIndex(infoPtr->interp, objPtr, index,
		&currentObj) != TCL_OK) {
	    infoPtr->resultCode = TCL_ERROR;
	    return NULL;
	}
	if (currentObj == NULL) {
	    char buffer[TCL_INTEGER_SPACE];

	    TclFormatInt(buffer, index);
	    Tcl_AppendResult(infoPtr->interp, "element ", buffer,
		    " missing from sublist \"", TclGetString(objPtr), "\"",
		    NULL);
	    infoPtr->resultCode = TCL_ERROR;
	    return NULL;
	}
	objPtr = currentObj;
    }
    return objPtr;
}

/*
 * Local Variables:
 * mode: c
 * c-basic-offset: 4
 * fill-column: 78
 * End:
 */
