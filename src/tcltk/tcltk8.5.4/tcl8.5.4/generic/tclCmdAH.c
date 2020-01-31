/*
 * tclCmdAH.c --
 *
 *	This file contains the top-level command routines for most of the Tcl
 *	built-in commands whose names begin with the letters A to H.
 *
 * Copyright (c) 1987-1993 The Regents of the University of California.
 * Copyright (c) 1994-1997 Sun Microsystems, Inc.
 *
 * See the file "license.terms" for information on usage and redistribution of
 * this file, and for a DISCLAIMER OF ALL WARRANTIES.
 *
 * RCS: @(#) $Id: tclCmdAH.c,v 1.93.2.1 2008/07/21 19:38:17 andreas_kupries Exp $
 */

#include "tclInt.h"
#include <locale.h>

/*
 * Prototypes for local procedures defined in this file:
 */

static int		CheckAccess(Tcl_Interp *interp, Tcl_Obj *pathPtr,
			    int mode);
static int		EncodingDirsObjCmd(ClientData dummy,
			    Tcl_Interp *interp, int objc,
			    Tcl_Obj *CONST objv[]);
static int		GetStatBuf(Tcl_Interp *interp, Tcl_Obj *pathPtr,
			    Tcl_FSStatProc *statProc, Tcl_StatBuf *statPtr);
static char *		GetTypeFromMode(int mode);
static int		StoreStatData(Tcl_Interp *interp, Tcl_Obj *varName,
			    Tcl_StatBuf *statPtr);

/*
 *----------------------------------------------------------------------
 *
 * Tcl_BreakObjCmd --
 *
 *	This procedure is invoked to process the "break" Tcl command. See the
 *	user documentation for details on what it does.
 *
 *	With the bytecode compiler, this procedure is only called when a
 *	command name is computed at runtime, and is "break" or the name to
 *	which "break" was renamed: e.g., "set z break; $z"
 *
 * Results:
 *	A standard Tcl result.
 *
 * Side effects:
 *	See the user documentation.
 *
 *----------------------------------------------------------------------
 */

	/* ARGSUSED */
int
Tcl_BreakObjCmd(
    ClientData dummy,		/* Not used. */
    Tcl_Interp *interp,		/* Current interpreter. */
    int objc,			/* Number of arguments. */
    Tcl_Obj *CONST objv[])	/* Argument objects. */
{
    if (objc != 1) {
	Tcl_WrongNumArgs(interp, 1, objv, NULL);
	return TCL_ERROR;
    }
    return TCL_BREAK;
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_CaseObjCmd --
 *
 *	This procedure is invoked to process the "case" Tcl command. See the
 *	user documentation for details on what it does. THIS COMMAND IS
 *	OBSOLETE AND DEPRECATED. SLATED FOR REMOVAL IN TCL 9.0.
 *
 * Results:
 *	A standard Tcl object result.
 *
 * Side effects:
 *	See the user documentation.
 *
 *----------------------------------------------------------------------
 */

	/* ARGSUSED */
int
Tcl_CaseObjCmd(
    ClientData dummy,		/* Not used. */
    Tcl_Interp *interp,		/* Current interpreter. */
    int objc,			/* Number of arguments. */
    Tcl_Obj *CONST objv[])	/* Argument objects. */
{
    register int i;
    int body, result, caseObjc;
    char *stringPtr, *arg;
    Tcl_Obj *CONST *caseObjv;
    Tcl_Obj *armPtr;

    if (objc < 3) {
	Tcl_WrongNumArgs(interp, 1, objv,
		"string ?in? patList body ... ?default body?");
	return TCL_ERROR;
    }

    stringPtr = TclGetString(objv[1]);
    body = -1;

    arg = TclGetString(objv[2]);
    if (strcmp(arg, "in") == 0) {
	i = 3;
    } else {
	i = 2;
    }
    caseObjc = objc - i;
    caseObjv = objv + i;

    /*
     * If all of the pattern/command pairs are lumped into a single argument,
     * split them out again.
     */

    if (caseObjc == 1) {
	Tcl_Obj **newObjv;

	TclListObjGetElements(interp, caseObjv[0], &caseObjc, &newObjv);
	caseObjv = newObjv;
    }

    for (i = 0;  i < caseObjc;  i += 2) {
	int patObjc, j;
	CONST char **patObjv;
	char *pat;
	unsigned char *p;

	if (i == (caseObjc - 1)) {
	    Tcl_ResetResult(interp);
	    Tcl_AppendResult(interp, "extra case pattern with no body", NULL);
	    return TCL_ERROR;
	}

	/*
	 * Check for special case of single pattern (no list) with no
	 * backslash sequences.
	 */

	pat = TclGetString(caseObjv[i]);
	for (p = (unsigned char *) pat; *p != '\0'; p++) {
	    if (isspace(*p) || (*p == '\\')) {	/* INTL: ISO space, UCHAR */
		break;
	    }
	}
	if (*p == '\0') {
	    if ((*pat == 'd') && (strcmp(pat, "default") == 0)) {
		body = i + 1;
	    }
	    if (Tcl_StringMatch(stringPtr, pat)) {
		body = i + 1;
		goto match;
	    }
	    continue;
	}

	/*
	 * Break up pattern lists, then check each of the patterns in the
	 * list.
	 */

	result = Tcl_SplitList(interp, pat, &patObjc, &patObjv);
	if (result != TCL_OK) {
	    return result;
	}
	for (j = 0; j < patObjc; j++) {
	    if (Tcl_StringMatch(stringPtr, patObjv[j])) {
		body = i + 1;
		break;
	    }
	}
	ckfree((char *) patObjv);
	if (j < patObjc) {
	    break;
	}
    }

  match:
    if (body != -1) {
	armPtr = caseObjv[body - 1];
	result = Tcl_EvalObjEx(interp, caseObjv[body], 0);
	if (result == TCL_ERROR) {
	    Tcl_AppendObjToErrorInfo(interp, Tcl_ObjPrintf(
		    "\n    (\"%.50s\" arm line %d)",
		    TclGetString(armPtr), interp->errorLine));
	}
	return result;
    }

    /*
     * Nothing matched: return nothing.
     */

    return TCL_OK;
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_CatchObjCmd --
 *
 *	This object-based procedure is invoked to process the "catch" Tcl
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

	/* ARGSUSED */
int
Tcl_CatchObjCmd(
    ClientData dummy,		/* Not used. */
    Tcl_Interp *interp,		/* Current interpreter. */
    int objc,			/* Number of arguments. */
    Tcl_Obj *CONST objv[])	/* Argument objects. */
{
    Tcl_Obj *varNamePtr = NULL;
    Tcl_Obj *optionVarNamePtr = NULL;
    int result;
    Interp *iPtr = (Interp *) interp;

    if ((objc < 2) || (objc > 4)) {
	Tcl_WrongNumArgs(interp, 1, objv,
		"script ?resultVarName? ?optionVarName?");
	return TCL_ERROR;
    }

    if (objc >= 3) {
	varNamePtr = objv[2];
    }
    if (objc == 4) {
	optionVarNamePtr = objv[3];
    }

    /*
     * TIP #280. Make invoking context available to caught script.
     */

    result = TclEvalObjEx(interp, objv[1], 0, iPtr->cmdFramePtr, 1);

    /*
     * We disable catch in interpreters where the limit has been exceeded.
     */

    if (Tcl_LimitExceeded(interp)) {
	Tcl_AppendObjToErrorInfo(interp, Tcl_ObjPrintf(
		"\n    (\"catch\" body line %d)", interp->errorLine));
	return TCL_ERROR;
    }

    if (objc >= 3) {
	if (NULL == Tcl_ObjSetVar2(interp, varNamePtr, NULL,
		Tcl_GetObjResult(interp), 0)) {
	    Tcl_ResetResult(interp);
	    Tcl_AppendResult(interp,
		    "couldn't save command result in variable", NULL);
	    return TCL_ERROR;
	}
    }
    if (objc == 4) {
	Tcl_Obj *options = Tcl_GetReturnOptions(interp, result);
	if (NULL == Tcl_ObjSetVar2(interp, optionVarNamePtr, NULL,
		options, 0)) {
	    Tcl_ResetResult(interp);
	    Tcl_AppendResult(interp,
		    "couldn't save return options in variable", NULL);
	    return TCL_ERROR;
	}
    }

    Tcl_ResetResult(interp);
    Tcl_SetObjResult(interp, Tcl_NewIntObj(result));
    return TCL_OK;
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_CdObjCmd --
 *
 *	This procedure is invoked to process the "cd" Tcl command. See the
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

	/* ARGSUSED */
int
Tcl_CdObjCmd(
    ClientData dummy,		/* Not used. */
    Tcl_Interp *interp,		/* Current interpreter. */
    int objc,			/* Number of arguments. */
    Tcl_Obj *CONST objv[])	/* Argument objects. */
{
    Tcl_Obj *dir;
    int result;

    if (objc > 2) {
	Tcl_WrongNumArgs(interp, 1, objv, "?dirName?");
	return TCL_ERROR;
    }

    if (objc == 2) {
	dir = objv[1];
    } else {
	TclNewLiteralStringObj(dir, "~");
	Tcl_IncrRefCount(dir);
    }
    if (Tcl_FSConvertToPathType(interp, dir) != TCL_OK) {
	result = TCL_ERROR;
    } else {
	result = Tcl_FSChdir(dir);
	if (result != TCL_OK) {
	    Tcl_AppendResult(interp, "couldn't change working directory to \"",
		    TclGetString(dir), "\": ", Tcl_PosixError(interp), NULL);
	    result = TCL_ERROR;
	}
    }
    if (objc != 2) {
	Tcl_DecrRefCount(dir);
    }
    return result;
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_ConcatObjCmd --
 *
 *	This object-based procedure is invoked to process the "concat" Tcl
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

	/* ARGSUSED */
int
Tcl_ConcatObjCmd(
    ClientData dummy,		/* Not used. */
    Tcl_Interp *interp,		/* Current interpreter. */
    int objc,			/* Number of arguments. */
    Tcl_Obj *CONST objv[])	/* Argument objects. */
{
    if (objc >= 2) {
	Tcl_SetObjResult(interp, Tcl_ConcatObj(objc-1, objv+1));
    }
    return TCL_OK;
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_ContinueObjCmd --
 *
 *	This procedure is invoked to process the "continue" Tcl command. See
 *	the user documentation for details on what it does.
 *
 *	With the bytecode compiler, this procedure is only called when a
 *	command name is computed at runtime, and is "continue" or the name to
 *	which "continue" was renamed: e.g., "set z continue; $z"
 *
 * Results:
 *	A standard Tcl result.
 *
 * Side effects:
 *	See the user documentation.
 *
 *----------------------------------------------------------------------
 */

	/* ARGSUSED */
int
Tcl_ContinueObjCmd(
    ClientData dummy,		/* Not used. */
    Tcl_Interp *interp,		/* Current interpreter. */
    int objc,			/* Number of arguments. */
    Tcl_Obj *CONST objv[])	/* Argument objects. */
{
    if (objc != 1) {
	Tcl_WrongNumArgs(interp, 1, objv, NULL);
	return TCL_ERROR;
    }
    return TCL_CONTINUE;
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_EncodingObjCmd --
 *
 *	This command manipulates encodings.
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
Tcl_EncodingObjCmd(
    ClientData dummy,		/* Not used. */
    Tcl_Interp *interp,		/* Current interpreter. */
    int objc,			/* Number of arguments. */
    Tcl_Obj *CONST objv[])	/* Argument objects. */
{
    int index;

    static CONST char *optionStrings[] = {
	"convertfrom", "convertto", "dirs", "names", "system",
	NULL
    };
    enum options {
	ENC_CONVERTFROM, ENC_CONVERTTO, ENC_DIRS, ENC_NAMES, ENC_SYSTEM
    };

    if (objc < 2) {
	Tcl_WrongNumArgs(interp, 1, objv, "option ?arg ...?");
	return TCL_ERROR;
    }
    if (Tcl_GetIndexFromObj(interp, objv[1], optionStrings, "option", 0,
	    &index) != TCL_OK) {
	return TCL_ERROR;
    }

    switch ((enum options) index) {
    case ENC_CONVERTTO:
    case ENC_CONVERTFROM: {
	Tcl_Obj *data;
	Tcl_DString ds;
	Tcl_Encoding encoding;
	int length;
	char *stringPtr;

	if (objc == 3) {
	    encoding = Tcl_GetEncoding(interp, NULL);
	    data = objv[2];
	} else if (objc == 4) {
	    if (Tcl_GetEncodingFromObj(interp, objv[2], &encoding) != TCL_OK) {
		return TCL_ERROR;
	    }
	    data = objv[3];
	} else {
	    Tcl_WrongNumArgs(interp, 2, objv, "?encoding? data");
	    return TCL_ERROR;
	}

	if ((enum options) index == ENC_CONVERTFROM) {
	    /*
	     * Treat the string as binary data.
	     */

	    stringPtr = (char *) Tcl_GetByteArrayFromObj(data, &length);
	    Tcl_ExternalToUtfDString(encoding, stringPtr, length, &ds);

	    /*
	     * Note that we cannot use Tcl_DStringResult here because it will
	     * truncate the string at the first null byte.
	     */

	    Tcl_SetObjResult(interp, Tcl_NewStringObj(
		    Tcl_DStringValue(&ds), Tcl_DStringLength(&ds)));
	    Tcl_DStringFree(&ds);
	} else {
	    /*
	     * Store the result as binary data.
	     */

	    stringPtr = TclGetStringFromObj(data, &length);
	    Tcl_UtfToExternalDString(encoding, stringPtr, length, &ds);
	    Tcl_SetObjResult(interp, Tcl_NewByteArrayObj(
		    (unsigned char *) Tcl_DStringValue(&ds),
		    Tcl_DStringLength(&ds)));
	    Tcl_DStringFree(&ds);
	}

	Tcl_FreeEncoding(encoding);
	break;
    }
    case ENC_DIRS:
	return EncodingDirsObjCmd(dummy, interp, objc-1, objv+1);
    case ENC_NAMES:
	if (objc > 2) {
	    Tcl_WrongNumArgs(interp, 2, objv, NULL);
	    return TCL_ERROR;
	}
	Tcl_GetEncodingNames(interp);
	break;
    case ENC_SYSTEM:
	if (objc > 3) {
	    Tcl_WrongNumArgs(interp, 2, objv, "?encoding?");
	    return TCL_ERROR;
	}
	if (objc == 2) {
	    Tcl_SetObjResult(interp, Tcl_NewStringObj(
		    Tcl_GetEncodingName(NULL), -1));
	} else {
	    return Tcl_SetSystemEncoding(interp, TclGetString(objv[2]));
	}
	break;
    }
    return TCL_OK;
}

/*
 *----------------------------------------------------------------------
 *
 * EncodingDirsObjCmd --
 *
 *	This command manipulates the encoding search path.
 *
 * Results:
 *	A standard Tcl result.
 *
 * Side effects:
 *	Can set the encoding search path.
 *
 *----------------------------------------------------------------------
 */

int
EncodingDirsObjCmd(
    ClientData dummy,		/* Not used. */
    Tcl_Interp *interp,		/* Current interpreter. */
    int objc,			/* Number of arguments. */
    Tcl_Obj *CONST objv[])	/* Argument objects. */
{
    if (objc > 2) {
	Tcl_WrongNumArgs(interp, 1, objv, "?dirList?");
	return TCL_ERROR;
    }
    if (objc == 1) {
	Tcl_SetObjResult(interp, Tcl_GetEncodingSearchPath());
	return TCL_OK;
    }
    if (Tcl_SetEncodingSearchPath(objv[1]) == TCL_ERROR) {
	Tcl_AppendResult(interp, "expected directory list but got \"",
		TclGetString(objv[1]), "\"", NULL);
	return TCL_ERROR;
    }
    Tcl_SetObjResult(interp, objv[1]);
    return TCL_OK;
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_ErrorObjCmd --
 *
 *	This procedure is invoked to process the "error" Tcl command. See the
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

	/* ARGSUSED */
int
Tcl_ErrorObjCmd(
    ClientData dummy,		/* Not used. */
    Tcl_Interp *interp,		/* Current interpreter. */
    int objc,			/* Number of arguments. */
    Tcl_Obj *CONST objv[])	/* Argument objects. */
{
    Tcl_Obj *options, *optName;

    if ((objc < 2) || (objc > 4)) {
	Tcl_WrongNumArgs(interp, 1, objv, "message ?errorInfo? ?errorCode?");
	return TCL_ERROR;
    }

    TclNewLiteralStringObj(options, "-code error -level 0");

    if (objc >= 3) {		/* Process the optional info argument */
	TclNewLiteralStringObj(optName, "-errorinfo");
	Tcl_ListObjAppendElement(NULL, options, optName);
	Tcl_ListObjAppendElement(NULL, options, objv[2]);
    }

    if (objc >= 4) {		/* Process the optional code argument */
	TclNewLiteralStringObj(optName, "-errorcode");
	Tcl_ListObjAppendElement(NULL, options, optName);
	Tcl_ListObjAppendElement(NULL, options, objv[3]);
    }

    Tcl_SetObjResult(interp, objv[1]);
    return Tcl_SetReturnOptions(interp, options);
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_EvalObjCmd --
 *
 *	This object-based procedure is invoked to process the "eval" Tcl
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

	/* ARGSUSED */
int
Tcl_EvalObjCmd(
    ClientData dummy,		/* Not used. */
    Tcl_Interp *interp,		/* Current interpreter. */
    int objc,			/* Number of arguments. */
    Tcl_Obj *CONST objv[])	/* Argument objects. */
{
    int result;
    register Tcl_Obj *objPtr;
    Interp *iPtr = (Interp *) interp;

    if (objc < 2) {
	Tcl_WrongNumArgs(interp, 1, objv, "arg ?arg ...?");
	return TCL_ERROR;
    }

    if (objc == 2) {
	/*
	 * TIP #280. Make argument location available to eval'd script.
	 */

	CmdFrame* invoker = iPtr->cmdFramePtr;
	int word          = 1;
	TclArgumentGet (interp, objv[1], &invoker, &word);

	result = TclEvalObjEx(interp, objv[1], TCL_EVAL_DIRECT,
		invoker, word);
    } else {
	/*
	 * More than one argument: concatenate them together with spaces
	 * between, then evaluate the result. Tcl_EvalObjEx will delete the
	 * object when it decrements its refcount after eval'ing it.
	 */

	objPtr = Tcl_ConcatObj(objc-1, objv+1);

	/*
	 * TIP #280. Make invoking context available to eval'd script.
	 */

	result = TclEvalObjEx(interp, objPtr, TCL_EVAL_DIRECT, NULL, 0);
    }
    if (result == TCL_ERROR) {
	Tcl_AppendObjToErrorInfo(interp, Tcl_ObjPrintf(
		"\n    (\"eval\" body line %d)", interp->errorLine));
    }
    return result;
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_ExitObjCmd --
 *
 *	This procedure is invoked to process the "exit" Tcl command. See the
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

	/* ARGSUSED */
int
Tcl_ExitObjCmd(
    ClientData dummy,		/* Not used. */
    Tcl_Interp *interp,		/* Current interpreter. */
    int objc,			/* Number of arguments. */
    Tcl_Obj *CONST objv[])	/* Argument objects. */
{
    int value;

    if ((objc != 1) && (objc != 2)) {
	Tcl_WrongNumArgs(interp, 1, objv, "?returnCode?");
	return TCL_ERROR;
    }

    if (objc == 1) {
	value = 0;
    } else if (Tcl_GetIntFromObj(interp, objv[1], &value) != TCL_OK) {
	return TCL_ERROR;
    }
    Tcl_Exit(value);
    /*NOTREACHED*/
    return TCL_OK;		/* Better not ever reach this! */
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_ExprObjCmd --
 *
 *	This object-based procedure is invoked to process the "expr" Tcl
 *	command. See the user documentation for details on what it does.
 *
 *	With the bytecode compiler, this procedure is called in two
 *	circumstances: 1) to execute expr commands that are too complicated or
 *	too unsafe to try compiling directly into an inline sequence of
 *	instructions, and 2) to execute commands where the command name is
 *	computed at runtime and is "expr" or the name to which "expr" was
 *	renamed (e.g., "set z expr; $z 2+3")
 *
 * Results:
 *	A standard Tcl object result.
 *
 * Side effects:
 *	See the user documentation.
 *
 *----------------------------------------------------------------------
 */

	/* ARGSUSED */
int
Tcl_ExprObjCmd(
    ClientData dummy,		/* Not used. */
    Tcl_Interp *interp,		/* Current interpreter. */
    int objc,			/* Number of arguments. */
    Tcl_Obj *CONST objv[])	/* Argument objects. */
{
    Tcl_Obj *resultPtr;
    int result;

    if (objc < 2) {
	Tcl_WrongNumArgs(interp, 1, objv, "arg ?arg ...?");
	return TCL_ERROR;
    }

    if (objc == 2) {
	result = Tcl_ExprObj(interp, objv[1], &resultPtr);
    } else {
	Tcl_Obj *objPtr = Tcl_ConcatObj(objc-1, objv+1);
	Tcl_IncrRefCount(objPtr);
	result = Tcl_ExprObj(interp, objPtr, &resultPtr);
	Tcl_DecrRefCount(objPtr);
    }

    if (result == TCL_OK) {
	Tcl_SetObjResult(interp, resultPtr);
	Tcl_DecrRefCount(resultPtr);	/* Done with the result object */
    }

    return result;
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_FileObjCmd --
 *
 *	This procedure is invoked to process the "file" Tcl command. See the
 *	user documentation for details on what it does. PLEASE NOTE THAT THIS
 *	FAILS WITH FILENAMES AND PATHS WITH EMBEDDED NULLS. With the
 *	object-based Tcl_FS APIs, the above NOTE may no longer be true. In any
 *	case this assertion should be tested.
 *
 * Results:
 *	A standard Tcl result.
 *
 * Side effects:
 *	See the user documentation.
 *
 *----------------------------------------------------------------------
 */

	/* ARGSUSED */
int
Tcl_FileObjCmd(
    ClientData dummy,		/* Not used. */
    Tcl_Interp *interp,		/* Current interpreter. */
    int objc,			/* Number of arguments. */
    Tcl_Obj *CONST objv[])	/* Argument objects. */
{
    int index, value;
    Tcl_StatBuf buf;
    struct utimbuf tval;

    /*
     * This list of constants should match the fileOption string array below.
     */

    static CONST char *fileOptions[] = {
	"atime",	"attributes",	"channels",	"copy",
	"delete",
	"dirname",	"executable",	"exists",	"extension",
	"isdirectory",	"isfile",	"join",		"link",
	"lstat",	"mtime",	"mkdir",	"nativename",
	"normalize",    "owned",
	"pathtype",	"readable",	"readlink",	"rename",
	"rootname",	"separator",    "size",		"split",
	"stat",		"system",
	"tail",		"type",		"volumes",	"writable",
	NULL
    };
    enum options {
	FCMD_ATIME,	FCMD_ATTRIBUTES, FCMD_CHANNELS,	FCMD_COPY,
	FCMD_DELETE,
	FCMD_DIRNAME,	FCMD_EXECUTABLE, FCMD_EXISTS,	FCMD_EXTENSION,
	FCMD_ISDIRECTORY, FCMD_ISFILE,	FCMD_JOIN,	FCMD_LINK,
	FCMD_LSTAT,	FCMD_MTIME,	FCMD_MKDIR,	FCMD_NATIVENAME,
	FCMD_NORMALIZE,	FCMD_OWNED,
	FCMD_PATHTYPE,	FCMD_READABLE,	FCMD_READLINK,	FCMD_RENAME,
	FCMD_ROOTNAME,	FCMD_SEPARATOR,	FCMD_SIZE,	FCMD_SPLIT,
	FCMD_STAT,	FCMD_SYSTEM,
	FCMD_TAIL,	FCMD_TYPE,	FCMD_VOLUMES,	FCMD_WRITABLE
    };

    if (objc < 2) {
	Tcl_WrongNumArgs(interp, 1, objv, "option ?arg ...?");
	return TCL_ERROR;
    }
    if (Tcl_GetIndexFromObj(interp, objv[1], fileOptions, "option", 0,
	    &index) != TCL_OK) {
	return TCL_ERROR;
    }

    switch ((enum options) index) {

    case FCMD_ATIME:
    case FCMD_MTIME:
	if ((objc < 3) || (objc > 4)) {
	    Tcl_WrongNumArgs(interp, 2, objv, "name ?time?");
	    return TCL_ERROR;
	}
	if (GetStatBuf(interp, objv[2], Tcl_FSStat, &buf) != TCL_OK) {
	    return TCL_ERROR;
	}
	if (objc == 4) {
	    /*
	     * Need separate variable for reading longs from an object on
	     * 64-bit platforms. [Bug #698146]
	     */

	    long newTime;

	    if (TclGetLongFromObj(interp, objv[3], &newTime) != TCL_OK) {
		return TCL_ERROR;
	    }

	    if (index == FCMD_ATIME) {
		tval.actime = newTime;
		tval.modtime = buf.st_mtime;
	    } else {	/* index == FCMD_MTIME */
		tval.actime = buf.st_atime;
		tval.modtime = newTime;
	    }

	    if (Tcl_FSUtime(objv[2], &tval) != 0) {
		Tcl_AppendResult(interp, "could not set ",
			(index == FCMD_ATIME ? "access" : "modification"),
			" time for file \"", TclGetString(objv[2]), "\": ",
			Tcl_PosixError(interp), NULL);
		return TCL_ERROR;
	    }

	    /*
	     * Do another stat to ensure that the we return the new recognized
	     * atime - hopefully the same as the one we sent in. However, fs's
	     * like FAT don't even know what atime is.
	     */

	    if (GetStatBuf(interp, objv[2], Tcl_FSStat, &buf) != TCL_OK) {
		return TCL_ERROR;
	    }
	}

	Tcl_SetObjResult(interp, Tcl_NewLongObj((long)
		(index == FCMD_ATIME ? buf.st_atime : buf.st_mtime)));
	return TCL_OK;
    case FCMD_ATTRIBUTES:
	return TclFileAttrsCmd(interp, objc, objv);
    case FCMD_CHANNELS:
	if ((objc < 2) || (objc > 3)) {
	    Tcl_WrongNumArgs(interp, 2, objv, "?pattern?");
	    return TCL_ERROR;
	}
	return Tcl_GetChannelNamesEx(interp,
		((objc == 2) ? NULL : TclGetString(objv[2])));
    case FCMD_COPY:
	return TclFileCopyCmd(interp, objc, objv);
    case FCMD_DELETE:
	return TclFileDeleteCmd(interp, objc, objv);
    case FCMD_DIRNAME: {
	Tcl_Obj *dirPtr;

	if (objc != 3) {
	    goto only3Args;
	}
	dirPtr = TclPathPart(interp, objv[2], TCL_PATH_DIRNAME);
	if (dirPtr == NULL) {
	    return TCL_ERROR;
	} else {
	    Tcl_SetObjResult(interp, dirPtr);
	    Tcl_DecrRefCount(dirPtr);
	    return TCL_OK;
	}
    }
    case FCMD_EXECUTABLE:
	if (objc != 3) {
	    goto only3Args;
	}
	return CheckAccess(interp, objv[2], X_OK);
    case FCMD_EXISTS:
	if (objc != 3) {
	    goto only3Args;
	}
	return CheckAccess(interp, objv[2], F_OK);
    case FCMD_EXTENSION: {
	Tcl_Obj *ext;

	if (objc != 3) {
	    goto only3Args;
	}
	ext = TclPathPart(interp, objv[2], TCL_PATH_EXTENSION);
	if (ext != NULL) {
	    Tcl_SetObjResult(interp, ext);
	    Tcl_DecrRefCount(ext);
	    return TCL_OK;
	} else {
	    return TCL_ERROR;
	}
    }
    case FCMD_ISDIRECTORY:
	if (objc != 3) {
	    goto only3Args;
	}
	value = 0;
	if (GetStatBuf(NULL, objv[2], Tcl_FSStat, &buf) == TCL_OK) {
	    value = S_ISDIR(buf.st_mode);
	}
	Tcl_SetObjResult(interp, Tcl_NewBooleanObj(value));
	return TCL_OK;
    case FCMD_ISFILE:
	if (objc != 3) {
	    goto only3Args;
	}
	value = 0;
	if (GetStatBuf(NULL, objv[2], Tcl_FSStat, &buf) == TCL_OK) {
	    value = S_ISREG(buf.st_mode);
	}
	Tcl_SetObjResult(interp, Tcl_NewBooleanObj(value));
	return TCL_OK;
    case FCMD_OWNED:
	if (objc != 3) {
	    goto only3Args;
	}
	value = 0;
	if (GetStatBuf(NULL, objv[2], Tcl_FSStat, &buf) == TCL_OK) {
	    /*
	     * For Windows, there are no user ids associated with a file, so
	     * we always return 1.
	     */

#if defined(__WIN32__)
	    value = 1;
#else
	    value = (geteuid() == buf.st_uid);
#endif
	}
	Tcl_SetObjResult(interp, Tcl_NewBooleanObj(value));
	return TCL_OK;
    case FCMD_JOIN: {
	Tcl_Obj *resObj;

	if (objc < 3) {
	    Tcl_WrongNumArgs(interp, 2, objv, "name ?name ...?");
	    return TCL_ERROR;
	}
	resObj = Tcl_FSJoinToPath(NULL, objc - 2, objv + 2);
	Tcl_SetObjResult(interp, resObj);
	return TCL_OK;
    }
    case FCMD_LINK: {
	Tcl_Obj *contents;
	int index;

	if (objc < 3 || objc > 5) {
	    Tcl_WrongNumArgs(interp, 2, objv, "?-linktype? linkname ?target?");
	    return TCL_ERROR;
	}

	/*
	 * Index of the 'source' argument.
	 */

	if (objc == 5) {
	    index = 3;
	} else {
	    index = 2;
	}

	if (objc > 3) {
	    int linkAction;
	    if (objc == 5) {
		/*
		 * We have a '-linktype' argument.
		 */

		static CONST char *linkTypes[] = {
		    "-symbolic", "-hard", NULL
		};
		if (Tcl_GetIndexFromObj(interp, objv[2], linkTypes, "switch",
			0, &linkAction) != TCL_OK) {
		    return TCL_ERROR;
		}
		if (linkAction == 0) {
		    linkAction = TCL_CREATE_SYMBOLIC_LINK;
		} else {
		    linkAction = TCL_CREATE_HARD_LINK;
		}
	    } else {
		linkAction = TCL_CREATE_SYMBOLIC_LINK|TCL_CREATE_HARD_LINK;
	    }
	    if (Tcl_FSConvertToPathType(interp, objv[index]) != TCL_OK) {
		return TCL_ERROR;
	    }

	    /*
	     * Create link from source to target.
	     */

	    contents = Tcl_FSLink(objv[index], objv[index+1], linkAction);
	    if (contents == NULL) {
		/*
		 * We handle three common error cases specially, and for all
		 * other errors, we use the standard posix error message.
		 */

		if (errno == EEXIST) {
		    Tcl_AppendResult(interp, "could not create new link \"",
			    TclGetString(objv[index]),
			    "\": that path already exists", NULL);
		} else if (errno == ENOENT) {
		    /*
		     * There are two cases here: either the target doesn't
		     * exist, or the directory of the src doesn't exist.
		     */

		    int access;
		    Tcl_Obj *dirPtr = TclPathPart(interp, objv[index],
			    TCL_PATH_DIRNAME);

		    if (dirPtr == NULL) {
			return TCL_ERROR;
		    }
		    access = Tcl_FSAccess(dirPtr, F_OK);
		    Tcl_DecrRefCount(dirPtr);
		    if (access != 0) {
			Tcl_AppendResult(interp,
				"could not create new link \"",
				TclGetString(objv[index]),
				"\": no such file or directory", NULL);
		    } else {
			Tcl_AppendResult(interp,
				"could not create new link \"",
				TclGetString(objv[index]), "\": target \"",
				TclGetString(objv[index+1]),
				"\" doesn't exist", NULL);
		    }
		} else {
		    Tcl_AppendResult(interp,
			    "could not create new link \"",
			    TclGetString(objv[index]), "\" pointing to \"",
			    TclGetString(objv[index+1]), "\": ",
			    Tcl_PosixError(interp), NULL);
		}
		return TCL_ERROR;
	    }
	} else {
	    if (Tcl_FSConvertToPathType(interp, objv[index]) != TCL_OK) {
		return TCL_ERROR;
	    }

	    /*
	     * Read link
	     */

	    contents = Tcl_FSLink(objv[index], NULL, 0);
	    if (contents == NULL) {
		Tcl_AppendResult(interp, "could not read link \"",
			TclGetString(objv[index]), "\": ",
			Tcl_PosixError(interp), NULL);
		return TCL_ERROR;
	    }
	}
	Tcl_SetObjResult(interp, contents);
	if (objc == 3) {
	    /*
	     * If we are reading a link, we need to free this result refCount.
	     * If we are creating a link, this will just be objv[index+1], and
	     * so we don't own it.
	     */

	    Tcl_DecrRefCount(contents);
	}
	return TCL_OK;
    }
    case FCMD_LSTAT:
	if (objc != 4) {
	    Tcl_WrongNumArgs(interp, 2, objv, "name varName");
	    return TCL_ERROR;
	}
	if (GetStatBuf(interp, objv[2], Tcl_FSLstat, &buf) != TCL_OK) {
	    return TCL_ERROR;
	}
	return StoreStatData(interp, objv[3], &buf);
    case FCMD_STAT:
	if (objc != 4) {
	    Tcl_WrongNumArgs(interp, 2, objv, "name varName");
	    return TCL_ERROR;
	}
	if (GetStatBuf(interp, objv[2], Tcl_FSStat, &buf) != TCL_OK) {
	    return TCL_ERROR;
	}
	return StoreStatData(interp, objv[3], &buf);
    case FCMD_SIZE:
	if (objc != 3) {
	    goto only3Args;
	}
	if (GetStatBuf(interp, objv[2], Tcl_FSStat, &buf) != TCL_OK) {
	    return TCL_ERROR;
	}
	Tcl_SetObjResult(interp,
		Tcl_NewWideIntObj((Tcl_WideInt) buf.st_size));
	return TCL_OK;
    case FCMD_TYPE:
	if (objc != 3) {
	    goto only3Args;
	}
	if (GetStatBuf(interp, objv[2], Tcl_FSLstat, &buf) != TCL_OK) {
	    return TCL_ERROR;
	}
	Tcl_SetObjResult(interp, Tcl_NewStringObj(
		GetTypeFromMode((unsigned short) buf.st_mode), -1));
	return TCL_OK;
    case FCMD_MKDIR:
	if (objc < 3) {
	    Tcl_WrongNumArgs(interp, 2, objv, "name ?name ...?");
	    return TCL_ERROR;
	}
	return TclFileMakeDirsCmd(interp, objc, objv);
    case FCMD_NATIVENAME: {
	CONST char *fileName;
	Tcl_DString ds;

	if (objc != 3) {
	    goto only3Args;
	}
	fileName = TclGetString(objv[2]);
	fileName = Tcl_TranslateFileName(interp, fileName, &ds);
	if (fileName == NULL) {
	    return TCL_ERROR;
	}
	Tcl_SetObjResult(interp, Tcl_NewStringObj(fileName,
		Tcl_DStringLength(&ds)));
	Tcl_DStringFree(&ds);
	return TCL_OK;
    }
    case FCMD_NORMALIZE: {
	Tcl_Obj *fileName;

	if (objc != 3) {
	    Tcl_WrongNumArgs(interp, 2, objv, "filename");
	    return TCL_ERROR;
	}

	fileName = Tcl_FSGetNormalizedPath(interp, objv[2]);
	if (fileName == NULL) {
	    return TCL_ERROR;
	}
	Tcl_SetObjResult(interp, fileName);
	return TCL_OK;
    }
    case FCMD_PATHTYPE: {
	Tcl_Obj *typeName;

	if (objc != 3) {
	    goto only3Args;
	}

	switch (Tcl_FSGetPathType(objv[2])) {
	case TCL_PATH_ABSOLUTE:
	    TclNewLiteralStringObj(typeName, "absolute");
	    break;
	case TCL_PATH_RELATIVE:
	    TclNewLiteralStringObj(typeName, "relative");
	    break;
	case TCL_PATH_VOLUME_RELATIVE:
	    TclNewLiteralStringObj(typeName, "volumerelative");
	    break;
	default:
	    return TCL_OK;
	}
	Tcl_SetObjResult(interp, typeName);
	return TCL_OK;
    }
    case FCMD_READABLE:
	if (objc != 3) {
	    goto only3Args;
	}
	return CheckAccess(interp, objv[2], R_OK);
    case FCMD_READLINK: {
	Tcl_Obj *contents;

	if (objc != 3) {
	    goto only3Args;
	}

	if (Tcl_FSConvertToPathType(interp, objv[2]) != TCL_OK) {
	    return TCL_ERROR;
	}

	contents = Tcl_FSLink(objv[2], NULL, 0);

	if (contents == NULL) {
	    Tcl_AppendResult(interp, "could not readlink \"",
		    TclGetString(objv[2]), "\": ", Tcl_PosixError(interp),
		    NULL);
	    return TCL_ERROR;
	}
	Tcl_SetObjResult(interp, contents);
	Tcl_DecrRefCount(contents);
	return TCL_OK;
    }
    case FCMD_RENAME:
	return TclFileRenameCmd(interp, objc, objv);
    case FCMD_ROOTNAME: {
	Tcl_Obj *root;

	if (objc != 3) {
	    goto only3Args;
	}
	root = TclPathPart(interp, objv[2], TCL_PATH_ROOT);
	if (root != NULL) {
	    Tcl_SetObjResult(interp, root);
	    Tcl_DecrRefCount(root);
	    return TCL_OK;
	} else {
	    return TCL_ERROR;
	}
    }
    case FCMD_SEPARATOR:
	if ((objc < 2) || (objc > 3)) {
	    Tcl_WrongNumArgs(interp, 2, objv, "?name?");
	    return TCL_ERROR;
	}
	if (objc == 2) {
	    char *separator = NULL; /* lint */

	    switch (tclPlatform) {
	    case TCL_PLATFORM_UNIX:
		separator = "/";
		break;
	    case TCL_PLATFORM_WINDOWS:
		separator = "\\";
		break;
	    }
	    Tcl_SetObjResult(interp, Tcl_NewStringObj(separator, 1));
	} else {
	    Tcl_Obj *separatorObj = Tcl_FSPathSeparator(objv[2]);

	    if (separatorObj == NULL) {
		Tcl_SetResult(interp, "Unrecognised path", TCL_STATIC);
		return TCL_ERROR;
	    }
	    Tcl_SetObjResult(interp, separatorObj);
	}
	return TCL_OK;
    case FCMD_SPLIT: {
	Tcl_Obj *res;

	if (objc != 3) {
	    goto only3Args;
	}
	res = Tcl_FSSplitPath(objv[2], NULL);
	if (res == NULL) {
	    /* How can the interp be NULL here?! DKF */
	    if (interp != NULL) {
		Tcl_AppendResult(interp, "could not read \"",
			TclGetString(objv[2]),
			"\": no such file or directory", NULL);
	    }
	    return TCL_ERROR;
	}
	Tcl_SetObjResult(interp, res);
	return TCL_OK;
    }
    case FCMD_SYSTEM: {
	Tcl_Obj *fsInfo;

	if (objc != 3) {
	    goto only3Args;
	}
	fsInfo = Tcl_FSFileSystemInfo(objv[2]);
	if (fsInfo == NULL) {
	    Tcl_SetResult(interp, "Unrecognised path", TCL_STATIC);
	    return TCL_ERROR;
	}
	Tcl_SetObjResult(interp, fsInfo);
	return TCL_OK;
    }
    case FCMD_TAIL: {
	Tcl_Obj *dirPtr;

	if (objc != 3) {
	    goto only3Args;
	}
	dirPtr = TclPathPart(interp, objv[2], TCL_PATH_TAIL);
	if (dirPtr == NULL) {
	    return TCL_ERROR;
	}
	Tcl_SetObjResult(interp, dirPtr);
	Tcl_DecrRefCount(dirPtr);
	return TCL_OK;
    }
    case FCMD_VOLUMES:
	if (objc != 2) {
	    Tcl_WrongNumArgs(interp, 2, objv, NULL);
	    return TCL_ERROR;
	}
	Tcl_SetObjResult(interp, Tcl_FSListVolumes());
	return TCL_OK;
    case FCMD_WRITABLE:
	if (objc != 3) {
	    goto only3Args;
	}
	return CheckAccess(interp, objv[2], W_OK);
    }

  only3Args:
    Tcl_WrongNumArgs(interp, 2, objv, "name");
    return TCL_ERROR;
}

/*
 *---------------------------------------------------------------------------
 *
 * CheckAccess --
 *
 *	Utility procedure used by Tcl_FileObjCmd() to query file attributes
 *	available through the access() system call.
 *
 * Results:
 *	Always returns TCL_OK. Sets interp's result to boolean true or false
 *	depending on whether the file has the specified attribute.
 *
 * Side effects:
 *	None.
 *
 *---------------------------------------------------------------------------
 */

static int
CheckAccess(
    Tcl_Interp *interp,		/* Interp for status return. Must not be
				 * NULL. */
    Tcl_Obj *pathPtr,		/* Name of file to check. */
    int mode)			/* Attribute to check; passed as argument to
				 * access(). */
{
    int value;

    if (Tcl_FSConvertToPathType(interp, pathPtr) != TCL_OK) {
	value = 0;
    } else {
	value = (Tcl_FSAccess(pathPtr, mode) == 0);
    }
    Tcl_SetObjResult(interp, Tcl_NewBooleanObj(value));

    return TCL_OK;
}

/*
 *---------------------------------------------------------------------------
 *
 * GetStatBuf --
 *
 *	Utility procedure used by Tcl_FileObjCmd() to query file attributes
 *	available through the stat() or lstat() system call.
 *
 * Results:
 *	The return value is TCL_OK if the specified file exists and can be
 *	stat'ed, TCL_ERROR otherwise. If TCL_ERROR is returned, an error
 *	message is left in interp's result. If TCL_OK is returned, *statPtr is
 *	filled with information about the specified file.
 *
 * Side effects:
 *	None.
 *
 *---------------------------------------------------------------------------
 */

static int
GetStatBuf(
    Tcl_Interp *interp,		/* Interp for error return. May be NULL. */
    Tcl_Obj *pathPtr,		/* Path name to examine. */
    Tcl_FSStatProc *statProc,	/* Either stat() or lstat() depending on
				 * desired behavior. */
    Tcl_StatBuf *statPtr)	/* Filled with info about file obtained by
				 * calling (*statProc)(). */
{
    int status;

    if (Tcl_FSConvertToPathType(interp, pathPtr) != TCL_OK) {
	return TCL_ERROR;
    }

    status = (*statProc)(pathPtr, statPtr);

    if (status < 0) {
	if (interp != NULL) {
	    Tcl_AppendResult(interp, "could not read \"",
		    TclGetString(pathPtr), "\": ",
		    Tcl_PosixError(interp), NULL);
	}
	return TCL_ERROR;
    }
    return TCL_OK;
}

/*
 *----------------------------------------------------------------------
 *
 * StoreStatData --
 *
 *	This is a utility procedure that breaks out the fields of a "stat"
 *	structure and stores them in textual form into the elements of an
 *	associative array.
 *
 * Results:
 *	Returns a standard Tcl return value. If an error occurs then a message
 *	is left in interp's result.
 *
 * Side effects:
 *	Elements of the associative array given by "varName" are modified.
 *
 *----------------------------------------------------------------------
 */

static int
StoreStatData(
    Tcl_Interp *interp,		/* Interpreter for error reports. */
    Tcl_Obj *varName,		/* Name of associative array variable in which
				 * to store stat results. */
    Tcl_StatBuf *statPtr)	/* Pointer to buffer containing stat data to
				 * store in varName. */
{
    Tcl_Obj *field, *value;
    register unsigned short mode;

    /*
     * Assume Tcl_ObjSetVar2() does not keep a copy of the field name!
     *
     * Might be a better idea to call Tcl_SetVar2Ex() instead, except we want
     * to have an object (i.e. possibly cached) array variable name but a
     * string element name, so no API exists. Messy.
     */

#define STORE_ARY(fieldName, object) \
    TclNewLiteralStringObj(field, fieldName); \
    Tcl_IncrRefCount(field); \
    value = (object); \
    if (Tcl_ObjSetVar2(interp,varName,field,value,TCL_LEAVE_ERR_MSG)==NULL) { \
	TclDecrRefCount(field); \
	return TCL_ERROR; \
    } \
    TclDecrRefCount(field);

    /*
     * Watch out porters; the inode is meant to be an *unsigned* value, so the
     * cast might fail when there isn't a real arithmentic 'long long' type...
     */

    STORE_ARY("dev",	Tcl_NewLongObj((long)statPtr->st_dev));
    STORE_ARY("ino",	Tcl_NewWideIntObj((Tcl_WideInt)statPtr->st_ino));
    STORE_ARY("nlink",	Tcl_NewLongObj((long)statPtr->st_nlink));
    STORE_ARY("uid",	Tcl_NewLongObj((long)statPtr->st_uid));
    STORE_ARY("gid",	Tcl_NewLongObj((long)statPtr->st_gid));
    STORE_ARY("size",	Tcl_NewWideIntObj((Tcl_WideInt)statPtr->st_size));
#ifdef HAVE_ST_BLOCKS
    STORE_ARY("blocks",	Tcl_NewWideIntObj((Tcl_WideInt)statPtr->st_blocks));
#endif
    STORE_ARY("atime",	Tcl_NewLongObj((long)statPtr->st_atime));
    STORE_ARY("mtime",	Tcl_NewLongObj((long)statPtr->st_mtime));
    STORE_ARY("ctime",	Tcl_NewLongObj((long)statPtr->st_ctime));
    mode = (unsigned short) statPtr->st_mode;
    STORE_ARY("mode",	Tcl_NewIntObj(mode));
    STORE_ARY("type",	Tcl_NewStringObj(GetTypeFromMode(mode), -1));
#undef STORE_ARY

    return TCL_OK;
}

/*
 *----------------------------------------------------------------------
 *
 * GetTypeFromMode --
 *
 *	Given a mode word, returns a string identifying the type of a file.
 *
 * Results:
 *	A static text string giving the file type from mode.
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */

static char *
GetTypeFromMode(
    int mode)
{
    if (S_ISREG(mode)) {
	return "file";
    } else if (S_ISDIR(mode)) {
	return "directory";
    } else if (S_ISCHR(mode)) {
	return "characterSpecial";
    } else if (S_ISBLK(mode)) {
	return "blockSpecial";
    } else if (S_ISFIFO(mode)) {
	return "fifo";
#ifdef S_ISLNK
    } else if (S_ISLNK(mode)) {
	return "link";
#endif
#ifdef S_ISSOCK
    } else if (S_ISSOCK(mode)) {
	return "socket";
#endif
    }
    return "unknown";
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_ForObjCmd --
 *
 *	This procedure is invoked to process the "for" Tcl command. See the
 *	user documentation for details on what it does.
 *
 *	With the bytecode compiler, this procedure is only called when a
 *	command name is computed at runtime, and is "for" or the name to which
 *	"for" was renamed: e.g.,
 *	"set z for; $z {set i 0} {$i<100} {incr i} {puts $i}"
 *
 * Results:
 *	A standard Tcl result.
 *
 * Side effects:
 *	See the user documentation.
 *
 *----------------------------------------------------------------------
 */

	/* ARGSUSED */
int
Tcl_ForObjCmd(
    ClientData dummy,		/* Not used. */
    Tcl_Interp *interp,		/* Current interpreter. */
    int objc,			/* Number of arguments. */
    Tcl_Obj *CONST objv[])	/* Argument objects. */
{
    int result, value;
    Interp *iPtr = (Interp *) interp;

    if (objc != 5) {
	Tcl_WrongNumArgs(interp, 1, objv, "start test next command");
	return TCL_ERROR;
    }

    /*
     * TIP #280. Make invoking context available to initial script.
     */

    result = TclEvalObjEx(interp, objv[1], 0, iPtr->cmdFramePtr, 1);
    if (result != TCL_OK) {
	if (result == TCL_ERROR) {
	    Tcl_AddErrorInfo(interp, "\n    (\"for\" initial command)");
	}
	return result;
    }
    while (1) {
	/*
	 * We need to reset the result before passing it off to
	 * Tcl_ExprBooleanObj. Otherwise, any error message will be appended
	 * to the result of the last evaluation.
	 */

	Tcl_ResetResult(interp);
	result = Tcl_ExprBooleanObj(interp, objv[2], &value);
	if (result != TCL_OK) {
	    return result;
	}
	if (!value) {
	    break;
	}

	/*
	 * TIP #280. Make invoking context available to loop body.
	 */

	result = TclEvalObjEx(interp, objv[4], 0, iPtr->cmdFramePtr, 4);
	if ((result != TCL_OK) && (result != TCL_CONTINUE)) {
	    if (result == TCL_ERROR) {
		Tcl_AppendObjToErrorInfo(interp, Tcl_ObjPrintf(
			"\n    (\"for\" body line %d)", interp->errorLine));
	    }
	    break;
	}

	/*
	 * TIP #280. Make invoking context available to next script.
	 */

	result = TclEvalObjEx(interp, objv[3], 0, iPtr->cmdFramePtr, 3);
	if (result == TCL_BREAK) {
	    break;
	} else if (result != TCL_OK) {
	    if (result == TCL_ERROR) {
		Tcl_AddErrorInfo(interp, "\n    (\"for\" loop-end command)");
	    }
	    return result;
	}
    }
    if (result == TCL_BREAK) {
	result = TCL_OK;
    }
    if (result == TCL_OK) {
	Tcl_ResetResult(interp);
    }
    return result;
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_ForeachObjCmd --
 *
 *	This object-based procedure is invoked to process the "foreach" Tcl
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

	/* ARGSUSED */
int
Tcl_ForeachObjCmd(
    ClientData dummy,		/* Not used. */
    Tcl_Interp *interp,		/* Current interpreter. */
    int objc,			/* Number of arguments. */
    Tcl_Obj *CONST objv[])	/* Argument objects. */
{
    int result = TCL_OK;
    int i;			/* i selects a value list */
    int j, maxj;		/* Number of loop iterations */
    int v;			/* v selects a loop variable */
    int numLists = (objc-2)/2;	/* Count of value lists */
    Tcl_Obj *bodyPtr;
    Interp *iPtr = (Interp *) interp;

    int *index;			/* Array of value list indices */
    int *varcList;		/* # loop variables per list */
    Tcl_Obj ***varvList;	/* Array of var name lists */
    Tcl_Obj **vCopyList;	/* Copies of var name list arguments */
    int *argcList;		/* Array of value list sizes */
    Tcl_Obj ***argvList;	/* Array of value lists */
    Tcl_Obj **aCopyList;	/* Copies of value list arguments */

    if (objc < 4 || (objc%2 != 0)) {
	Tcl_WrongNumArgs(interp, 1, objv,
		"varList list ?varList list ...? command");
	return TCL_ERROR;
    }

    /*
     * Manage numList parallel value lists.
     * argvList[i] is a value list counted by argcList[i]l;
     * varvList[i] is the list of variables associated with the value list;
     * varcList[i] is the number of variables associated with the value list;
     * index[i] is the current pointer into the value list argvList[i].
     */

    index = (int *) TclStackAlloc(interp, 3 * numLists * sizeof(int));
    varcList = index + numLists;
    argcList = varcList + numLists;
    memset(index, 0, 3 * numLists * sizeof(int));

    varvList = (Tcl_Obj ***)
	    TclStackAlloc(interp, 2 * numLists * sizeof(Tcl_Obj **));
    argvList = varvList + numLists;
    memset(varvList, 0, 2 * numLists * sizeof(Tcl_Obj **));

    vCopyList = (Tcl_Obj **)
	    TclStackAlloc(interp, 2 * numLists * sizeof(Tcl_Obj *));
    aCopyList = vCopyList + numLists;
    memset(vCopyList, 0, 2 * numLists * sizeof(Tcl_Obj *));

    /*
     * Break up the value lists and variable lists into elements.
     */

    maxj = 0;
    for (i=0 ; i<numLists ; i++) {
	
	vCopyList[i] = TclListObjCopy(interp, objv[1+i*2]);
	if (vCopyList[i] == NULL) {
	    result = TCL_ERROR;
	    goto done;
	}
	TclListObjGetElements(NULL, vCopyList[i], &varcList[i], &varvList[i]);
	if (varcList[i] < 1) {
	    Tcl_AppendResult(interp, "foreach varlist is empty", NULL);
	    result = TCL_ERROR;
	    goto done;
	}

	aCopyList[i] = TclListObjCopy(interp, objv[2+i*2]);
	if (aCopyList[i] == NULL) {
	    result = TCL_ERROR;
	    goto done;
	}
	TclListObjGetElements(NULL, aCopyList[i], &argcList[i], &argvList[i]);

	j = argcList[i] / varcList[i];
	if ((argcList[i] % varcList[i]) != 0) {
	    j++;
	}
	if (j > maxj) {
	    maxj = j;
	}
    }

    /*
     * Iterate maxj times through the lists in parallel. If some value lists
     * run out of values, set loop vars to ""
     */

    bodyPtr = objv[objc-1];
    for (j=0 ; j<maxj ; j++) {
	for (i=0 ; i<numLists ; i++) {
	    for (v=0 ; v<varcList[i] ; v++) {
		int k = index[i]++;
		Tcl_Obj *valuePtr, *varValuePtr;

		if (k < argcList[i]) {
		    valuePtr = argvList[i][k];
		} else {
		    valuePtr = Tcl_NewObj(); /* Empty string */
		}
		varValuePtr = Tcl_ObjSetVar2(interp, varvList[i][v], NULL,
			valuePtr, TCL_LEAVE_ERR_MSG);
		if (varValuePtr == NULL) {
		    Tcl_AppendObjToErrorInfo(interp, Tcl_ObjPrintf(
			    "\n    (setting foreach loop variable \"%s\")",
			    TclGetString(varvList[i][v])));
		    result = TCL_ERROR;
		    goto done;
		}
	    }
	}

	/*
	 * TIP #280. Make invoking context available to loop body.
	 */

	result = TclEvalObjEx(interp, bodyPtr, 0, iPtr->cmdFramePtr, objc-1);
	if (result != TCL_OK) {
	    if (result == TCL_CONTINUE) {
		result = TCL_OK;
	    } else if (result == TCL_BREAK) {
		result = TCL_OK;
		break;
	    } else if (result == TCL_ERROR) {
		Tcl_AppendObjToErrorInfo(interp, Tcl_ObjPrintf(
			"\n    (\"foreach\" body line %d)",
			interp->errorLine));
		break;
	    } else {
		break;
	    }
	}
    }
    if (result == TCL_OK) {
	Tcl_ResetResult(interp);
    }

  done:
    for (i=0 ; i<numLists ; i++) {
	if (vCopyList[i]) {
	    Tcl_DecrRefCount(vCopyList[i]);
	}
	if (aCopyList[i]) {
	    Tcl_DecrRefCount(aCopyList[i]);
	}
    }
    TclStackFree(interp, vCopyList);	/* Tcl_Obj * arrays */
    TclStackFree(interp, varvList);	/* Tcl_Obj ** arrays */
    TclStackFree(interp, index);	/* int arrays */
    return result;
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_FormatObjCmd --
 *
 *	This procedure is invoked to process the "format" Tcl command. See
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

	/* ARGSUSED */
int
Tcl_FormatObjCmd(
    ClientData dummy,		/* Not used. */
    Tcl_Interp *interp,		/* Current interpreter. */
    int objc,			/* Number of arguments. */
    Tcl_Obj *CONST objv[])	/* Argument objects. */
{
    Tcl_Obj *resultPtr;		/* Where result is stored finally. */

    if (objc < 2) {
	Tcl_WrongNumArgs(interp, 1, objv, "formatString ?arg arg ...?");
	return TCL_ERROR;
    }

    resultPtr = Tcl_Format(interp, TclGetString(objv[1]), objc-2, objv+2);
    if (resultPtr == NULL) {
	return TCL_ERROR;
    }
    Tcl_SetObjResult(interp, resultPtr);
    return TCL_OK;
}

/*
 * Local Variables:
 * mode: c
 * c-basic-offset: 4
 * fill-column: 78
 * End:
 */
