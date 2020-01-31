/*
 * tkMain.c --
 *
 *	This file contains a generic main program for Tk-based applications.
 *	It can be used as-is for many applications, just by supplying a
 *	different appInitProc function for each specific application. Or, it
 *	can be used as a template for creating new main programs for Tk
 *	applications.
 *
 * Copyright (c) 1990-1994 The Regents of the University of California.
 * Copyright (c) 1994-1997 Sun Microsystems, Inc.
 *
 * See the file "license.terms" for information on usage and redistribution of
 * this file, and for a DISCLAIMER OF ALL WARRANTIES.
 *
 * RCS: @(#) $Id: tkMain.c,v 1.28 2007/12/13 15:24:15 dgp Exp $
 */

#include <ctype.h>
#include <stdio.h>
#include <string.h>
#include "tclInt.h"
#include "tkInt.h"
#ifdef NO_STDLIB_H
#   include "../compat/stdlib.h"
#else
#   include <stdlib.h>
#endif
#ifdef __WIN32__
#include "tkWinInt.h"
#endif
#ifdef MAC_OSX_TK
#include "tkMacOSXInt.h"
#endif


typedef struct ThreadSpecificData {
    Tcl_Interp *interp;		/* Interpreter for this thread. */
    Tcl_DString command;	/* Used to assemble lines of terminal input
				 * into Tcl commands. */
    Tcl_DString line;		/* Used to read the next line from the
				 * terminal input. */
    int tty;			/* Non-zero means standard input is a
				 * terminal-like device. Zero means it's a
				 * file. */
} ThreadSpecificData;
static Tcl_ThreadDataKey dataKey;

/*
 * Declarations for various library functions and variables (don't want to
 * include tkInt.h or tkPort.h here, because people might copy this file out
 * of the Tk source directory to make their own modified versions). Note: do
 * not declare "exit" here even though a declaration is really needed, because
 * it will conflict with a declaration elsewhere on some systems.
 */

#if !defined(__WIN32__) && !defined(_WIN32)
extern int		isatty(int fd);
extern char *		strrchr(CONST char *string, int c);
#endif

/*
 * Forward declarations for functions defined later in this file.
 */

static void		Prompt(Tcl_Interp *interp, int partial);
static void		StdinProc(ClientData clientData, int mask);

/*
 *----------------------------------------------------------------------
 *
 * Tk_MainEx --
 *
 *	Main program for Wish and most other Tk-based applications.
 *
 * Results:
 *	None. This function never returns (it exits the process when it's
 *	done.
 *
 * Side effects:
 *	This function initializes the Tk world and then starts interpreting
 *	commands; almost anything could happen, depending on the script being
 *	interpreted.
 *
 *----------------------------------------------------------------------
 */

void
Tk_MainEx(
    int argc,			/* Number of arguments. */
    char **argv,		/* Array of argument strings. */
    Tcl_AppInitProc *appInitProc,
				/* Application-specific initialization
				 * function to call after most initialization
				 * but before starting to execute commands. */
    Tcl_Interp *interp)
{
    Tcl_Obj *path, *argvPtr;
    CONST char *encodingName;
    int code, nullStdin = 0;
    Tcl_Channel inChannel, outChannel;
    ThreadSpecificData *tsdPtr;
#ifdef __WIN32__
    HANDLE handle;
#endif
    Tcl_DString appName;

    /*
     * Ensure that we are getting the matching version of Tcl. This is really
     * only an issue when Tk is loaded dynamically.
     */

    if (Tcl_InitStubs(interp, TCL_VERSION, 1) == NULL) {
	abort();
    }

    tsdPtr = (ThreadSpecificData *)
	    Tcl_GetThreadData(&dataKey, sizeof(ThreadSpecificData));

    Tcl_FindExecutable(argv[0]);
    tsdPtr->interp = interp;
    Tcl_Preserve((ClientData) interp);

#if defined(__WIN32__)
    Tk_InitConsoleChannels(interp);
#endif

#ifdef MAC_OSX_TK
    if (Tcl_GetStartupScript(NULL) == NULL) {
	TkMacOSXDefaultStartupScript();
    }
#endif

#ifdef TCL_MEM_DEBUG
    Tcl_InitMemory(interp);
#endif

    /*
     * If the application has not already set a startup script, parse the
     * first few command line arguments to determine the script path and
     * encoding.
     */

    if (NULL == Tcl_GetStartupScript(NULL)) {
	size_t length;

	/*
	 * Check whether first 3 args (argv[1] - argv[3]) look like
	 * 	-encoding ENCODING FILENAME
	 * or like
	 * 	FILENAME
	 * or like
	 *	-file FILENAME		(ancient history support only)
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
	} else if ((argc > 2) && (length = strlen(argv[1]))
		&& (length > 1) && (0 == strncmp("-file", argv[1], length))
		&& ('-' != argv[2][0])) {
	    Tcl_SetStartupScript(Tcl_NewStringObj(argv[2], -1), NULL);
	    argc -= 2;
	    argv += 2;
	}
    }

    path = Tcl_GetStartupScript(&encodingName);
    if (NULL == path) {
	Tcl_ExternalToUtfDString(NULL, argv[0], -1, &appName);
    } else {
	int numBytes;
	CONST char *pathName = Tcl_GetStringFromObj(path, &numBytes);

	Tcl_ExternalToUtfDString(NULL, pathName, numBytes, &appName);
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

#ifdef __WIN32__
    /*
     * For now, under Windows, we assume we are not running as a console mode
     * app, so we need to use the GUI console. In order to enable this, we
     * always claim to be running on a tty. This probably isn't the right way
     * to do it.
     */

    handle = GetStdHandle(STD_INPUT_HANDLE);

    if ((handle == INVALID_HANDLE_VALUE) || (handle == 0)
	     || (GetFileType(handle) == FILE_TYPE_UNKNOWN)) {
	/*
	 * If it's a bad or closed handle, then it's been connected to a wish
	 * console window.
	 */

	tsdPtr->tty = 1;
    } else if (GetFileType(handle) == FILE_TYPE_CHAR) {
	/*
	 * A character file handle is a tty by definition.
	 */

	tsdPtr->tty = 1;
    } else {
	tsdPtr->tty = 0;
    }

#else
    tsdPtr->tty = isatty(0);
#endif
#if defined(MAC_OSX_TK)
    /*
     * On TkAqua, if we don't have a TTY and stdin is a special character file
     * of length 0, (e.g. /dev/null, which is what Finder sets when double
     * clicking Wish) then use the GUI console.
     */
    
    if (!tsdPtr->tty) {
	struct stat st;

	nullStdin = fstat(0, &st) || (S_ISCHR(st.st_mode) && !st.st_blocks);
    }
#endif
    Tcl_SetVar(interp, "tcl_interactive",
	    ((path == NULL) && (tsdPtr->tty || nullStdin)) ? "1" : "0",
	    TCL_GLOBAL_ONLY);

    /*
     * Invoke application-specific initialization.
     */

    if ((*appInitProc)(interp) != TCL_OK) {
	TkpDisplayWarning(Tcl_GetStringResult(interp),
		"Application initialization failed");
    }

    /*
     * Invoke the script specified on the command line, if any. Must fetch it
     * again, as the appInitProc might have reset it.
     */

    path = Tcl_GetStartupScript(&encodingName);
    if (path != NULL) {
	Tcl_ResetResult(interp);
	code = Tcl_FSEvalFileEx(interp, path, encodingName);
	if (code != TCL_OK) {
	    /*
	     * The following statement guarantees that the errorInfo variable
	     * is set properly.
	     */

	    Tcl_AddErrorInfo(interp, "");
	    TkpDisplayWarning(Tcl_GetVar(interp, "errorInfo",
		    TCL_GLOBAL_ONLY), "Error in startup script");
	    Tcl_DeleteInterp(interp);
	    Tcl_Exit(1);
	}
	tsdPtr->tty = 0;
    } else {

	/*
	 * Evaluate the .rc file, if one has been specified.
	 */

	Tcl_SourceRCFile(interp);

	/*
	 * Establish a channel handler for stdin.
	 */

	inChannel = Tcl_GetStdChannel(TCL_STDIN);
	if (inChannel) {
	    Tcl_CreateChannelHandler(inChannel, TCL_READABLE, StdinProc,
		    (ClientData) inChannel);
	}
	if (tsdPtr->tty) {
	    Prompt(interp, 0);
	}
    }

    outChannel = Tcl_GetStdChannel(TCL_STDOUT);
    if (outChannel) {
	Tcl_Flush(outChannel);
    }
    Tcl_DStringInit(&tsdPtr->command);
    Tcl_DStringInit(&tsdPtr->line);
    Tcl_ResetResult(interp);

    /*
     * Loop infinitely, waiting for commands to execute. When there are no
     * windows left, Tk_MainLoop returns and we exit.
     */

    Tk_MainLoop();
    Tcl_DeleteInterp(interp);
    Tcl_Release((ClientData) interp);
    Tcl_SetStartupScript(NULL, NULL);
    Tcl_Exit(0);
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
    ClientData clientData,	/* Not used. */
    int mask)			/* Not used. */
{
    static int gotPartial = 0;
    char *cmd;
    int code, count;
    Tcl_Channel chan = (Tcl_Channel) clientData;
    ThreadSpecificData *tsdPtr = (ThreadSpecificData *)
	    Tcl_GetThreadData(&dataKey, sizeof(ThreadSpecificData));
    Tcl_Interp *interp = tsdPtr->interp;

    count = Tcl_Gets(chan, &tsdPtr->line);

    if (count < 0 && !gotPartial) {
	if (tsdPtr->tty) {
	    Tcl_Exit(0);
	} else {
	    Tcl_DeleteChannelHandler(chan, StdinProc, (ClientData) chan);
	}
	return;
    }

    (void) Tcl_DStringAppend(&tsdPtr->command, Tcl_DStringValue(
	    &tsdPtr->line), -1);
    cmd = Tcl_DStringAppend(&tsdPtr->command, "\n", -1);
    Tcl_DStringFree(&tsdPtr->line);
    if (!Tcl_CommandComplete(cmd)) {
	gotPartial = 1;
	goto prompt;
    }
    gotPartial = 0;

    /*
     * Disable the stdin channel handler while evaluating the command;
     * otherwise if the command re-enters the event loop we might process
     * commands from stdin before the current command is finished. Among other
     * things, this will trash the text of the command being evaluated.
     */

    Tcl_CreateChannelHandler(chan, 0, StdinProc, (ClientData) chan);
    code = Tcl_RecordAndEval(interp, cmd, TCL_EVAL_GLOBAL);

    chan = Tcl_GetStdChannel(TCL_STDIN);
    if (chan) {
	Tcl_CreateChannelHandler(chan, TCL_READABLE, StdinProc,
		(ClientData) chan);
    }
    Tcl_DStringFree(&tsdPtr->command);
    if (Tcl_GetStringResult(interp)[0] != '\0') {
	if ((code != TCL_OK) || (tsdPtr->tty)) {
	    chan = Tcl_GetStdChannel(TCL_STDOUT);
	    if (chan) {
		Tcl_WriteObj(chan, Tcl_GetObjResult(interp));
		Tcl_WriteChars(chan, "\n", 1);
	    }
	}
    }

    /*
     * Output a prompt.
     */

  prompt:
    if (tsdPtr->tty) {
	Prompt(interp, gotPartial);
    }
    Tcl_ResetResult(interp);
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
    int partial)		/* Non-zero means there already exists a
				 * partial command, so use the secondary
				 * prompt. */
{
    Tcl_Obj *promptCmd;
    int code;
    Tcl_Channel outChannel, errChannel;

    promptCmd = Tcl_GetVar2Ex(interp,
	partial ? "tcl_prompt2" : "tcl_prompt1", NULL, TCL_GLOBAL_ONLY);
    if (promptCmd == NULL) {
    defaultPrompt:
	if (!partial) {
	    /*
	     * We must check that outChannel is a real channel - it is
	     * possible that someone has transferred stdout out of this
	     * interpreter with "interp transfer".
	     */

	    outChannel = Tcl_GetChannel(interp, "stdout", NULL);
	    if (outChannel != (Tcl_Channel) NULL) {
		Tcl_WriteChars(outChannel, "% ", 2);
	    }
	}
    } else {
	code = Tcl_EvalObjEx(interp, promptCmd, TCL_EVAL_GLOBAL);
	if (code != TCL_OK) {
	    Tcl_AddErrorInfo(interp,
		    "\n    (script that generates prompt)");

	    /*
	     * We must check that errChannel is a real channel - it is
	     * possible that someone has transferred stderr out of this
	     * interpreter with "interp transfer".
	     */

	    errChannel = Tcl_GetChannel(interp, "stderr", NULL);
	    if (errChannel != (Tcl_Channel) NULL) {
		Tcl_WriteObj(errChannel, Tcl_GetObjResult(interp));
		Tcl_WriteChars(errChannel, "\n", 1);
	    }
	    goto defaultPrompt;
	}
    }
    outChannel = Tcl_GetChannel(interp, "stdout", NULL);
    if (outChannel != (Tcl_Channel) NULL) {
	Tcl_Flush(outChannel);
    }
}

/*
 * Local Variables:
 * mode: c
 * c-basic-offset: 4
 * fill-column: 78
 * End:
 */
