/*
 * tclMain.c --
 *
 *	Main program for Tcl shells and other Tcl-based applications.
 *
 * Copyright (c) 1988-1994 The Regents of the University of California.
 * Copyright (c) 1994-1997 Sun Microsystems, Inc.
 * Copyright (c) 2000 Ajuba Solutions.
 *
 * See the file "license.terms" for information on usage and redistribution of
 * this file, and for a DISCLAIMER OF ALL WARRANTIES.
 *
 * RCS: @(#) $Id: tclMain.c,v 1.44 2007/12/13 15:23:19 dgp Exp $
 */

#include "tclInt.h"

#undef TCL_STORAGE_CLASS
#define TCL_STORAGE_CLASS DLLEXPORT

/*
 * The default prompt used when the user has not overridden it.
 */

#define DEFAULT_PRIMARY_PROMPT	"% "

/*
 * Declarations for various library functions and variables (don't want to
 * include tclPort.h here, because people might copy this file out of the Tcl
 * source directory to make their own modified versions).
 */

extern CRTIMPORT int	isatty(int fd);

static Tcl_Obj *tclStartupScriptPath = NULL;
static Tcl_Obj *tclStartupScriptEncoding = NULL;
static Tcl_MainLoopProc *mainLoopProc = NULL;

/*
 * Structure definition for information used to keep the state of an
 * interactive command processor that reads lines from standard input and
 * writes prompts and results to standard output.
 */

typedef enum {
    PROMPT_NONE,		/* Print no prompt */
    PROMPT_START,		/* Print prompt for command start */
    PROMPT_CONTINUE		/* Print prompt for command continuation */
} PromptType;

typedef struct InteractiveState {
    Tcl_Channel input;		/* The standard input channel from which lines
				 * are read. */
    int tty;			/* Non-zero means standard input is a
				 * terminal-like device. Zero means it's a
				 * file. */
    Tcl_Obj *commandPtr;	/* Used to assemble lines of input into Tcl
				 * commands. */
    PromptType prompt;		/* Next prompt to print */
    Tcl_Interp *interp;		/* Interpreter that evaluates interactive
				 * commands. */
} InteractiveState;

/*
 * Forward declarations for functions defined later in this file.
 */

static void		Prompt(Tcl_Interp *interp, PromptType *promptPtr);
static void		StdinProc(ClientData clientData, int mask);

/*
 *----------------------------------------------------------------------
 *
 * Tcl_SetStartupScript --
 *
 *	Sets the path and encoding of the startup script to be evaluated by
 *	Tcl_Main, used to override the command line processing.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *
 *----------------------------------------------------------------------
 */

void
Tcl_SetStartupScript(
    Tcl_Obj *path,		/* Filesystem path of startup script file */
    CONST char *encoding)	/* Encoding of the data in that file */
{
    Tcl_Obj *newEncoding = NULL;
    if (encoding != NULL) {
	newEncoding = Tcl_NewStringObj(encoding, -1);
    }

    if (tclStartupScriptPath != NULL) {
	Tcl_DecrRefCount(tclStartupScriptPath);
    }
    tclStartupScriptPath = path;
    if (tclStartupScriptPath != NULL) {
	Tcl_IncrRefCount(tclStartupScriptPath);
    }

    if (tclStartupScriptEncoding != NULL) {
	Tcl_DecrRefCount(tclStartupScriptEncoding);
    }
    tclStartupScriptEncoding = newEncoding;
    if (tclStartupScriptEncoding != NULL) {
	Tcl_IncrRefCount(tclStartupScriptEncoding);
    }
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_GetStartupScript --
 *
 *	Gets the path and encoding of the startup script to be evaluated by
 *	Tcl_Main.
 *
 * Results:
 *	The path of the startup script; NULL if none has been set.
 *
 * Side effects:
 * 	If encodingPtr is not NULL, stores a (CONST char *) in it pointing to
 * 	the encoding name registered for the startup script. Tcl retains
 * 	ownership of the string, and may free it. Caller should make a copy
 * 	for long-term use.
 *
 *----------------------------------------------------------------------
 */

Tcl_Obj *
Tcl_GetStartupScript(
    CONST char **encodingPtr)	/* When not NULL, points to storage for the
				 * (CONST char *) that points to the
				 * registered encoding name for the startup
				 * script */
{
    if (encodingPtr != NULL) {
	if (tclStartupScriptEncoding == NULL) {
	    *encodingPtr = NULL;
	} else {
	    *encodingPtr = Tcl_GetString(tclStartupScriptEncoding);
	}
    }
    return tclStartupScriptPath;
}

/*
 *----------------------------------------------------------------------
 *
 * TclSetStartupScriptPath --
 *
 *	Primes the startup script VFS path, used to override the command line
 *	processing.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	This function initializes the VFS path of the Tcl script to run at
 *	startup.
 *
 *----------------------------------------------------------------------
 */

void
TclSetStartupScriptPath(
    Tcl_Obj *path)
{
    Tcl_SetStartupScript(path, NULL);
}

/*
 *----------------------------------------------------------------------
 *
 * TclGetStartupScriptPath --
 *
 *	Gets the startup script VFS path, used to override the command line
 *	processing.
 *
 * Results:
 *	The startup script VFS path, NULL if none has been set.
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */

Tcl_Obj *
TclGetStartupScriptPath(void)
{
    return Tcl_GetStartupScript(NULL);
}

/*
 *----------------------------------------------------------------------
 *
 * TclSetStartupScriptFileName --
 *
 *	Primes the startup script file name, used to override the command line
 *	processing.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	This function initializes the file name of the Tcl script to run at
 *	startup.
 *
 *----------------------------------------------------------------------
 */

void
TclSetStartupScriptFileName(
    CONST char *fileName)
{
    Tcl_Obj *path = Tcl_NewStringObj(fileName,-1);
    Tcl_SetStartupScript(path, NULL);
}

/*
 *----------------------------------------------------------------------
 *
 * TclGetStartupScriptFileName --
 *
 *	Gets the startup script file name, used to override the command line
 *	processing.
 *
 * Results:
 *	The startup script file name, NULL if none has been set.
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */

CONST char *
TclGetStartupScriptFileName(void)
{
    Tcl_Obj *path = Tcl_GetStartupScript(NULL);

    if (path == NULL) {
	return NULL;
    }
    return Tcl_GetString(path);
}

/*----------------------------------------------------------------------
 *
 * Tcl_SourceRCFile --
 *
 *	This function is typically invoked by Tcl_Main of Tk_Main function to
 *	source an application specific rc file into the interpreter at startup
 *	time.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	Depends on what's in the rc script.
 *
 *----------------------------------------------------------------------
 */

void
Tcl_SourceRCFile(
    Tcl_Interp *interp)		/* Interpreter to source rc file into. */
{
    Tcl_DString temp;
    CONST char *fileName;
    Tcl_Channel errChannel;

    fileName = Tcl_GetVar(interp, "tcl_rcFileName", TCL_GLOBAL_ONLY);
    if (fileName != NULL) {
	Tcl_Channel c;
	CONST char *fullName;

	Tcl_DStringInit(&temp);
	fullName = Tcl_TranslateFileName(interp, fileName, &temp);
	if (fullName == NULL) {
	    /*
	     * Couldn't translate the file name (e.g. it referred to a bogus
	     * user or there was no HOME environment variable). Just do
	     * nothing.
	     */
	} else {
	    /*
	     * Test for the existence of the rc file before trying to read it.
	     */

	    c = Tcl_OpenFileChannel(NULL, fullName, "r", 0);
	    if (c != (Tcl_Channel) NULL) {
		Tcl_Close(NULL, c);
		if (Tcl_EvalFile(interp, fullName) != TCL_OK) {
		    errChannel = Tcl_GetStdChannel(TCL_STDERR);
		    if (errChannel) {
			Tcl_WriteObj(errChannel, Tcl_GetObjResult(interp));
			Tcl_WriteChars(errChannel, "\n", 1);
 		    }
 		}
 	    }
	}
	Tcl_DStringFree(&temp);
    }
}

/*----------------------------------------------------------------------
 *
 * Tcl_Main --
 *
 *	Main program for tclsh and most other Tcl-based applications.
 *
 * Results:
 *	None. This function never returns (it exits the process when it's
 *	done).
 *
 * Side effects:
 *	This function initializes the Tcl world and then starts interpreting
 *	commands; almost anything could happen, depending on the script being
 *	interpreted.
 *
 *----------------------------------------------------------------------
 */

void
Tcl_Main(
    int argc,			/* Number of arguments. */
    char **argv,		/* Array of argument strings. */
    Tcl_AppInitProc *appInitProc)
				/* Application-specific initialization
				 * function to call after most initialization
				 * but before starting to execute commands. */
{
    Tcl_Obj *path, *resultPtr, *argvPtr, *commandPtr = NULL;
    CONST char *encodingName = NULL;
    PromptType prompt = PROMPT_START;
    int code, length, tty, exitCode = 0;
    Tcl_Channel inChannel, outChannel, errChannel;
    Tcl_Interp *interp;
    Tcl_DString appName;

    Tcl_FindExecutable(argv[0]);

    interp = Tcl_CreateInterp();
    Tcl_InitMemory(interp);

    /*
     * If the application has not already set a startup script, parse the
     * first few command line arguments to determine the script path and
     * encoding.
     */

    if (NULL == Tcl_GetStartupScript(NULL)) {

	/*
	 * Check whether first 3 args (argv[1] - argv[3]) look like
	 * 	-encoding ENCODING FILENAME
	 * or like
	 * 	FILENAME
	 */

	if ((argc > 3) && (0 == strcmp("-encoding", argv[1]))
		&& ('-' != argv[3][0])) {
	    Tcl_SetStartupScript(Tcl_NewStringObj(argv[3], -1), argv[2]);
	    argc -= 3;
	    argv += 3;
	} else if ((argc > 1) && ('-' != argv[1][0])) {
	    Tcl_SetStartupScript(Tcl_NewStringObj(argv[1], -1), NULL);
	    argc--;
	    argv++;
	}
    }

    path = Tcl_GetStartupScript(&encodingName);
    if (path == NULL) {
	Tcl_ExternalToUtfDString(NULL, argv[0], -1, &appName);
    } else {
	CONST char *pathName = Tcl_GetStringFromObj(path, &length);
	Tcl_ExternalToUtfDString(NULL, pathName, length, &appName);
	path = Tcl_NewStringObj(Tcl_DStringValue(&appName), -1);
	Tcl_SetStartupScript(path, encodingName);
    }
    Tcl_SetVar(interp, "argv0", Tcl_DStringValue(&appName), TCL_GLOBAL_ONLY);
    Tcl_DStringFree(&appName);
    argc--;
    argv++;

    Tcl_SetVar2Ex(interp, "argc", NULL, Tcl_NewIntObj(argc), TCL_GLOBAL_ONLY);

    argvPtr = Tcl_NewListObj(0, NULL);
    while (argc--) {
	Tcl_DString ds;
	Tcl_ExternalToUtfDString(NULL, *argv++, -1, &ds);
	Tcl_ListObjAppendElement(NULL, argvPtr, Tcl_NewStringObj(
		Tcl_DStringValue(&ds), Tcl_DStringLength(&ds)));
	Tcl_DStringFree(&ds);
    }
    Tcl_SetVar2Ex(interp, "argv", NULL, argvPtr, TCL_GLOBAL_ONLY);

    /*
     * Set the "tcl_interactive" variable.
     */

    tty = isatty(0);
    Tcl_SetVar(interp, "tcl_interactive", ((path == NULL) && tty) ? "1" : "0",
	    TCL_GLOBAL_ONLY);

    /*
     * Invoke application-specific initialization.
     */

    Tcl_Preserve((ClientData) interp);
    if ((*appInitProc)(interp) != TCL_OK) {
	errChannel = Tcl_GetStdChannel(TCL_STDERR);
	if (errChannel) {
	    Tcl_WriteChars(errChannel,
		    "application-specific initialization failed: ", -1);
	    Tcl_WriteObj(errChannel, Tcl_GetObjResult(interp));
	    Tcl_WriteChars(errChannel, "\n", 1);
	}
    }
    if (Tcl_InterpDeleted(interp)) {
	goto done;
    }
    if (Tcl_LimitExceeded(interp)) {
	goto done;
    }

    /*
     * If a script file was specified then just source that file and quit.
     * Must fetch it again, as the appInitProc might have reset it.
     */

    path = Tcl_GetStartupScript(&encodingName);
    if (path != NULL) {
	code = Tcl_FSEvalFileEx(interp, path, encodingName);
	if (code != TCL_OK) {
	    errChannel = Tcl_GetStdChannel(TCL_STDERR);
	    if (errChannel) {
		Tcl_Obj *options = Tcl_GetReturnOptions(interp, code);
		Tcl_Obj *keyPtr, *valuePtr;

		TclNewLiteralStringObj(keyPtr, "-errorinfo");
		Tcl_IncrRefCount(keyPtr);
		Tcl_DictObjGet(NULL, options, keyPtr, &valuePtr);
		Tcl_DecrRefCount(keyPtr);

		if (valuePtr) {
		    Tcl_WriteObj(errChannel, valuePtr);
		}
		Tcl_WriteChars(errChannel, "\n", 1);
	    }
	    exitCode = 1;
	}
	goto done;
    }

    /*
     * We're running interactively. Source a user-specific startup file if the
     * application specified one and if the file exists.
     */

    Tcl_SourceRCFile(interp);
    if (Tcl_LimitExceeded(interp)) {
	goto done;
    }

    /*
     * Process commands from stdin until there's an end-of-file. Note that we
     * need to fetch the standard channels again after every eval, since they
     * may have been changed.
     */

    commandPtr = Tcl_NewObj();
    Tcl_IncrRefCount(commandPtr);

    /*
     * Get a new value for tty if anyone writes to ::tcl_interactive
     */

    Tcl_LinkVar(interp, "tcl_interactive", (char *) &tty, TCL_LINK_BOOLEAN);
    inChannel = Tcl_GetStdChannel(TCL_STDIN);
    outChannel = Tcl_GetStdChannel(TCL_STDOUT);
    while ((inChannel != (Tcl_Channel) NULL) && !Tcl_InterpDeleted(interp)) {
	if (mainLoopProc == NULL) {
	    if (tty) {
		Prompt(interp, &prompt);
		if (Tcl_InterpDeleted(interp)) {
		    break;
		}
		if (Tcl_LimitExceeded(interp)) {
		    break;
		}
		inChannel = Tcl_GetStdChannel(TCL_STDIN);
		if (inChannel == (Tcl_Channel) NULL) {
		    break;
		}
	    }
	    if (Tcl_IsShared(commandPtr)) {
		Tcl_DecrRefCount(commandPtr);
		commandPtr = Tcl_DuplicateObj(commandPtr);
		Tcl_IncrRefCount(commandPtr);
	    }
	    length = Tcl_GetsObj(inChannel, commandPtr);
	    if (length < 0) {
		if (Tcl_InputBlocked(inChannel)) {
		    /*
		     * This can only happen if stdin has been set to
		     * non-blocking.  In that case cycle back and try again.
		     * This sets up a tight polling loop (since we have no
		     * event loop running). If this causes bad CPU hogging,
		     * we might try toggling the blocking on stdin instead.
		     */

		    continue;
		}

		/*
		 * Either EOF, or an error on stdin; we're done
		 */

		break;
	    }

	    /*
	     * Add the newline removed by Tcl_GetsObj back to the string.
	     * Have to add it back before testing completeness, because
	     * it can make a difference.  [Bug 1775878].
	     */

	    if (Tcl_IsShared(commandPtr)) {
		Tcl_DecrRefCount(commandPtr);
		commandPtr = Tcl_DuplicateObj(commandPtr);
		Tcl_IncrRefCount(commandPtr);
	    }
	    Tcl_AppendToObj(commandPtr, "\n", 1);
	    if (!TclObjCommandComplete(commandPtr)) {
		prompt = PROMPT_CONTINUE;
		continue;
	    }

	    prompt = PROMPT_START;
	    /*
	     * The final newline is syntactically redundant, and causes
	     * some error messages troubles deeper in, so lop it back off.
	     */
	    Tcl_GetStringFromObj(commandPtr, &length);
	    Tcl_SetObjLength(commandPtr, --length);
	    code = Tcl_RecordAndEvalObj(interp, commandPtr, TCL_EVAL_GLOBAL);
	    inChannel = Tcl_GetStdChannel(TCL_STDIN);
	    outChannel = Tcl_GetStdChannel(TCL_STDOUT);
	    errChannel = Tcl_GetStdChannel(TCL_STDERR);
	    Tcl_DecrRefCount(commandPtr);
	    commandPtr = Tcl_NewObj();
	    Tcl_IncrRefCount(commandPtr);
	    if (code != TCL_OK) {
		if (errChannel) {
		    Tcl_WriteObj(errChannel, Tcl_GetObjResult(interp));
		    Tcl_WriteChars(errChannel, "\n", 1);
		}
 	    } else if (tty) {
		resultPtr = Tcl_GetObjResult(interp);
		Tcl_IncrRefCount(resultPtr);
		Tcl_GetStringFromObj(resultPtr, &length);
		if ((length > 0) && outChannel) {
		    Tcl_WriteObj(outChannel, resultPtr);
		    Tcl_WriteChars(outChannel, "\n", 1);
		}
		Tcl_DecrRefCount(resultPtr);
	    }
	} else {	/* (mainLoopProc != NULL) */
	    /*
	     * If a main loop has been defined while running interactively, we
	     * want to start a fileevent based prompt by establishing a
	     * channel handler for stdin.
	     */

	    InteractiveState *isPtr = NULL;

	    if (inChannel) {
		if (tty) {
		    Prompt(interp, &prompt);
		}
		isPtr = (InteractiveState *)
			ckalloc((int) sizeof(InteractiveState));
		isPtr->input = inChannel;
		isPtr->tty = tty;
		isPtr->commandPtr = commandPtr;
		isPtr->prompt = prompt;
		isPtr->interp = interp;

		Tcl_UnlinkVar(interp, "tcl_interactive");
		Tcl_LinkVar(interp, "tcl_interactive", (char *) &(isPtr->tty),
			TCL_LINK_BOOLEAN);

		Tcl_CreateChannelHandler(inChannel, TCL_READABLE, StdinProc,
			(ClientData) isPtr);
	    }

	    (*mainLoopProc)();
	    mainLoopProc = NULL;

	    if (inChannel) {
		tty = isPtr->tty;
		Tcl_UnlinkVar(interp, "tcl_interactive");
		Tcl_LinkVar(interp, "tcl_interactive", (char *) &tty,
			TCL_LINK_BOOLEAN);
		prompt = isPtr->prompt;
		commandPtr = isPtr->commandPtr;
		if (isPtr->input != (Tcl_Channel) NULL) {
		    Tcl_DeleteChannelHandler(isPtr->input, StdinProc,
			    (ClientData) isPtr);
		}
		ckfree((char *)isPtr);
	    }
	    inChannel = Tcl_GetStdChannel(TCL_STDIN);
	    outChannel = Tcl_GetStdChannel(TCL_STDOUT);
	    errChannel = Tcl_GetStdChannel(TCL_STDERR);
	}
#ifdef TCL_MEM_DEBUG

	/*
	 * This code here only for the (unsupported and deprecated) [checkmem]
	 * command.
	 */

	if (tclMemDumpFileName != NULL) {
	    mainLoopProc = NULL;
	    Tcl_DeleteInterp(interp);
	}
#endif
    }

  done:
    if ((exitCode == 0) && (mainLoopProc != NULL)
	    && !Tcl_LimitExceeded(interp)) {
	/*
	 * If everything has gone OK so far, call the main loop proc, if it
	 * exists. Packages (like Tk) can set it to start processing events at
	 * this point.
	 */

	(*mainLoopProc)();
	mainLoopProc = NULL;
    }
    if (commandPtr != NULL) {
	Tcl_DecrRefCount(commandPtr);
    }

    /*
     * Rather than calling exit, invoke the "exit" command so that users can
     * replace "exit" with some other command to do additional cleanup on
     * exit. The Tcl_EvalObjEx call should never return.
     */

    if (!Tcl_InterpDeleted(interp)) {
	if (!Tcl_LimitExceeded(interp)) {
	    Tcl_Obj *cmd = Tcl_ObjPrintf("exit %d", exitCode);
	    Tcl_IncrRefCount(cmd);
	    Tcl_EvalObjEx(interp, cmd, TCL_EVAL_GLOBAL);
	    Tcl_DecrRefCount(cmd);
	}

	/*
	 * If Tcl_EvalObjEx returns, trying to eval [exit], something unusual
	 * is happening. Maybe interp has been deleted; maybe [exit] was
	 * redefined, maybe we've blown up because of an exceeded limit. We
	 * still want to cleanup and exit.
	 */

	if (!Tcl_InterpDeleted(interp)) {
	    Tcl_DeleteInterp(interp);
	}
    }
    Tcl_SetStartupScript(NULL, NULL);

    /*
     * If we get here, the master interp has been deleted. Allow its
     * destruction with the last matching Tcl_Release.
     */

    Tcl_Release((ClientData) interp);
    Tcl_Exit(exitCode);
}

/*
 *---------------------------------------------------------------
 *
 * Tcl_SetMainLoop --
 *
 *	Sets an alternative main loop function.
 *
 * Results:
 *	Returns the previously defined main loop function.
 *
 * Side effects:
 *	This function will be called before Tcl exits, allowing for the
 *	creation of an event loop.
 *
 *---------------------------------------------------------------
 */

void
Tcl_SetMainLoop(
    Tcl_MainLoopProc *proc)
{
    mainLoopProc = proc;
}

/*
 *----------------------------------------------------------------------
 *
 * StdinProc --
 *
 *	This function is invoked by the event dispatcher whenever standard
 *	input becomes readable. It grabs the next line of input characters,
 *	adds them to a command being assembled, and executes the command if
 *	it's complete.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	Could be almost arbitrary, depending on the command that's typed.
 *
 *----------------------------------------------------------------------
 */

    /* ARGSUSED */
static void
StdinProc(
    ClientData clientData,	/* The state of interactive cmd line */
    int mask)			/* Not used. */
{
    InteractiveState *isPtr = (InteractiveState *) clientData;
    Tcl_Channel chan = isPtr->input;
    Tcl_Obj *commandPtr = isPtr->commandPtr;
    Tcl_Interp *interp = isPtr->interp;
    int code, length;

    if (Tcl_IsShared(commandPtr)) {
	Tcl_DecrRefCount(commandPtr);
	commandPtr = Tcl_DuplicateObj(commandPtr);
	Tcl_IncrRefCount(commandPtr);
    }
    length = Tcl_GetsObj(chan, commandPtr);
    if (length < 0) {
	if (Tcl_InputBlocked(chan)) {
	    return;
	}
	if (isPtr->tty) {
	    /*
	     * Would be better to find a way to exit the mainLoop? Or perhaps
	     * evaluate [exit]? Leaving as is for now due to compatibility
	     * concerns.
	     */

	    Tcl_Exit(0);
	}
	Tcl_DeleteChannelHandler(chan, StdinProc, (ClientData) isPtr);
	return;
    }

    if (Tcl_IsShared(commandPtr)) {
	Tcl_DecrRefCount(commandPtr);
	commandPtr = Tcl_DuplicateObj(commandPtr);
	Tcl_IncrRefCount(commandPtr);
    }
    Tcl_AppendToObj(commandPtr, "\n", 1);
    if (!TclObjCommandComplete(commandPtr)) {
	isPtr->prompt = PROMPT_CONTINUE;
	goto prompt;
    }
    isPtr->prompt = PROMPT_START;
    Tcl_GetStringFromObj(commandPtr, &length);
    Tcl_SetObjLength(commandPtr, --length);

    /*
     * Disable the stdin channel handler while evaluating the command;
     * otherwise if the command re-enters the event loop we might process
     * commands from stdin before the current command is finished. Among other
     * things, this will trash the text of the command being evaluated.
     */

    Tcl_CreateChannelHandler(chan, 0, StdinProc, (ClientData) isPtr);
    code = Tcl_RecordAndEvalObj(interp, commandPtr, TCL_EVAL_GLOBAL);
    isPtr->input = chan = Tcl_GetStdChannel(TCL_STDIN);
    Tcl_DecrRefCount(commandPtr);
    isPtr->commandPtr = commandPtr = Tcl_NewObj();
    Tcl_IncrRefCount(commandPtr);
    if (chan != (Tcl_Channel) NULL) {
	Tcl_CreateChannelHandler(chan, TCL_READABLE, StdinProc,
		(ClientData) isPtr);
    }
    if (code != TCL_OK) {
	Tcl_Channel errChannel = Tcl_GetStdChannel(TCL_STDERR);
	if (errChannel != (Tcl_Channel) NULL) {
	    Tcl_WriteObj(errChannel, Tcl_GetObjResult(interp));
	    Tcl_WriteChars(errChannel, "\n", 1);
	}
    } else if (isPtr->tty) {
	Tcl_Obj *resultPtr = Tcl_GetObjResult(interp);
	Tcl_Channel outChannel = Tcl_GetStdChannel(TCL_STDOUT);
	Tcl_IncrRefCount(resultPtr);
	Tcl_GetStringFromObj(resultPtr, &length);
	if ((length >0) && (outChannel != (Tcl_Channel) NULL)) {
	    Tcl_WriteObj(outChannel, resultPtr);
	    Tcl_WriteChars(outChannel, "\n", 1);
	}
	Tcl_DecrRefCount(resultPtr);
    }

    /*
     * If a tty stdin is still around, output a prompt.
     */

  prompt:
    if (isPtr->tty && (isPtr->input != (Tcl_Channel) NULL)) {
	Prompt(interp, &(isPtr->prompt));
	isPtr->input = Tcl_GetStdChannel(TCL_STDIN);
    }
}

/*
 *----------------------------------------------------------------------
 *
 * Prompt --
 *
 *	Issue a prompt on standard output, or invoke a script to issue the
 *	prompt.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	A prompt gets output, and a Tcl script may be evaluated in interp.
 *
 *----------------------------------------------------------------------
 */

static void
Prompt(
    Tcl_Interp *interp,		/* Interpreter to use for prompting. */
    PromptType *promptPtr)	/* Points to type of prompt to print. Filled
				 * with PROMPT_NONE after a prompt is
				 * printed. */
{
    Tcl_Obj *promptCmdPtr;
    int code;
    Tcl_Channel outChannel, errChannel;

    if (*promptPtr == PROMPT_NONE) {
	return;
    }

    promptCmdPtr = Tcl_GetVar2Ex(interp,
	    ((*promptPtr == PROMPT_CONTINUE) ? "tcl_prompt2" : "tcl_prompt1"),
	    NULL, TCL_GLOBAL_ONLY);

    if (Tcl_InterpDeleted(interp)) {
	return;
    }
    if (promptCmdPtr == NULL) {
    defaultPrompt:
	outChannel = Tcl_GetStdChannel(TCL_STDOUT);
	if ((*promptPtr == PROMPT_START)
		&& (outChannel != (Tcl_Channel) NULL)) {
	    Tcl_WriteChars(outChannel, DEFAULT_PRIMARY_PROMPT,
		    strlen(DEFAULT_PRIMARY_PROMPT));
	}
    } else {
	code = Tcl_EvalObjEx(interp, promptCmdPtr, TCL_EVAL_GLOBAL);
	if (code != TCL_OK) {
	    Tcl_AddErrorInfo(interp,
		    "\n    (script that generates prompt)");
	    errChannel = Tcl_GetStdChannel(TCL_STDERR);
	    if (errChannel != (Tcl_Channel) NULL) {
		Tcl_WriteObj(errChannel, Tcl_GetObjResult(interp));
		Tcl_WriteChars(errChannel, "\n", 1);
	    }
	    goto defaultPrompt;
	}
    }

    outChannel = Tcl_GetStdChannel(TCL_STDOUT);
    if (outChannel != (Tcl_Channel) NULL) {
	Tcl_Flush(outChannel);
    }
    *promptPtr = PROMPT_NONE;
}

/*
 * Local Variables:
 * mode: c
 * c-basic-offset: 4
 * fill-column: 78
 * End:
 */
