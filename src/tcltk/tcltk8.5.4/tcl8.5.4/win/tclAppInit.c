/*
 * tclAppInit.c --
 *
 *	Provides a default version of the main program and Tcl_AppInit
 *	function for Tcl applications (without Tk). Note that this program
 *	must be built in Win32 console mode to work properly.
 *
 * Copyright (c) 1996-1997 by Sun Microsystems, Inc.
 * Copyright (c) 1998-1999 by Scriptics Corporation.
 *
 * See the file "license.terms" for information on usage and redistribution of
 * this file, and for a DISCLAIMER OF ALL WARRANTIES.
 *
 * RCS: @(#) $Id: tclAppInit.c,v 1.25 2007/04/16 13:36:36 dkf Exp $
 */

#include "tcl.h"
#include <windows.h>
#include <locale.h>

#ifdef TCL_TEST
extern Tcl_PackageInitProc	Procbodytest_Init;
extern Tcl_PackageInitProc	Procbodytest_SafeInit;
extern Tcl_PackageInitProc	Tcltest_Init;
extern Tcl_PackageInitProc	TclObjTest_Init;
#endif /* TCL_TEST */

#if defined(__GNUC__)
static void		setargv(int *argcPtr, char ***argvPtr);
#endif /* __GNUC__ */

/*
 *----------------------------------------------------------------------
 *
 * main --
 *
 *	This is the main program for the application.
 *
 * Results:
 *	None: Tcl_Main never returns here, so this function never returns
 *	either.
 *
 * Side effects:
 *	Whatever the application does.
 *
 *----------------------------------------------------------------------
 */

int
main(
    int argc,
    char *argv[])
{
    /*
     * The following #if block allows you to change the AppInit function by
     * using a #define of TCL_LOCAL_APPINIT instead of rewriting this entire
     * file. The #if checks for that #define and uses Tcl_AppInit if it
     * doesn't exist.
     */

#ifndef TCL_LOCAL_APPINIT
#define TCL_LOCAL_APPINIT Tcl_AppInit
#endif
    extern int TCL_LOCAL_APPINIT _ANSI_ARGS_((Tcl_Interp *interp));

    /*
     * The following #if block allows you to change how Tcl finds the startup
     * script, prime the library or encoding paths, fiddle with the argv,
     * etc., without needing to rewrite Tcl_Main()
     */

#ifdef TCL_LOCAL_MAIN_HOOK
    extern int TCL_LOCAL_MAIN_HOOK _ANSI_ARGS_((int *argc, char ***argv));
#endif

    char *p;

    /*
     * Set up the default locale to be standard "C" locale so parsing is
     * performed correctly.
     */

#if defined(__GNUC__)
    setargv( &argc, &argv );
#endif
    setlocale(LC_ALL, "C");

    /*
     * Forward slashes substituted for backslashes.
     */

    for (p = argv[0]; *p != '\0'; p++) {
	if (*p == '\\') {
	    *p = '/';
	}
    }

#ifdef TCL_LOCAL_MAIN_HOOK
    TCL_LOCAL_MAIN_HOOK(&argc, &argv);
#endif

    Tcl_Main(argc, argv, TCL_LOCAL_APPINIT);

    return 0;			/* Needed only to prevent compiler warning. */
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_AppInit --
 *
 *	This function performs application-specific initialization. Most
 *	applications, especially those that incorporate additional packages,
 *	will have their own version of this function.
 *
 * Results:
 *	Returns a standard Tcl completion code, and leaves an error message in
 *	the interp's result if an error occurs.
 *
 * Side effects:
 *	Depends on the startup script.
 *
 *----------------------------------------------------------------------
 */

int
Tcl_AppInit(
    Tcl_Interp *interp)		/* Interpreter for application. */
{
    if (Tcl_Init(interp) == TCL_ERROR) {
	return TCL_ERROR;
    }

#ifdef TCL_TEST
    if (Tcltest_Init(interp) == TCL_ERROR) {
	return TCL_ERROR;
    }
    Tcl_StaticPackage(interp, "Tcltest", Tcltest_Init, NULL);
    if (TclObjTest_Init(interp) == TCL_ERROR) {
	return TCL_ERROR;
    }
    if (Procbodytest_Init(interp) == TCL_ERROR) {
	return TCL_ERROR;
    }
    Tcl_StaticPackage(interp, "procbodytest", Procbodytest_Init,
	    Procbodytest_SafeInit);
#endif /* TCL_TEST */

#if defined(STATIC_BUILD) && TCL_USE_STATIC_PACKAGES
    {
	extern Tcl_PackageInitProc Registry_Init;
	extern Tcl_PackageInitProc Dde_Init;
	extern Tcl_PackageInitProc Dde_SafeInit;

	if (Registry_Init(interp) == TCL_ERROR) {
	    return TCL_ERROR;
	}
	Tcl_StaticPackage(interp, "registry", Registry_Init, NULL);

	if (Dde_Init(interp) == TCL_ERROR) {
	    return TCL_ERROR;
	}
	Tcl_StaticPackage(interp, "dde", Dde_Init, Dde_SafeInit);
   }
#endif

    /*
     * Call the init functions for included packages. Each call should look
     * like this:
     *
     * if (Mod_Init(interp) == TCL_ERROR) {
     *     return TCL_ERROR;
     * }
     *
     * where "Mod" is the name of the module.
     */

    /*
     * Call Tcl_CreateCommand for application-specific commands, if they
     * weren't already created by the init functions called above.
     */

    /*
     * Specify a user-specific startup file to invoke if the application is
     * run interactively. Typically the startup file is "~/.apprc" where "app"
     * is the name of the application. If this line is deleted then no
     * user-specific startup file will be run under any conditions.
     */

    Tcl_SetVar(interp, "tcl_rcFileName", "~/tclshrc.tcl", TCL_GLOBAL_ONLY);
    return TCL_OK;
}

/*
 *-------------------------------------------------------------------------
 *
 * setargv --
 *
 *	Parse the Windows command line string into argc/argv. Done here
 *	because we don't trust the builtin argument parser in crt0. Windows
 *	applications are responsible for breaking their command line into
 *	arguments.
 *
 *	2N backslashes + quote -> N backslashes + begin quoted string
 *	2N + 1 backslashes + quote -> literal
 *	N backslashes + non-quote -> literal
 *	quote + quote in a quoted string -> single quote
 *	quote + quote not in quoted string -> empty string
 *	quote -> begin quoted string
 *
 * Results:
 *	Fills argcPtr with the number of arguments and argvPtr with the array
 *	of arguments.
 *
 * Side effects:
 *	Memory allocated.
 *
 *--------------------------------------------------------------------------
 */

#if defined(__GNUC__)
static void
setargv(
    int *argcPtr,		/* Filled with number of argument strings. */
    char ***argvPtr)		/* Filled with argument strings (malloc'd). */
{
    char *cmdLine, *p, *arg, *argSpace;
    char **argv;
    int argc, size, inquote, copy, slashes;

    cmdLine = GetCommandLine();	/* INTL: BUG */

    /*
     * Precompute an overly pessimistic guess at the number of arguments in
     * the command line by counting non-space spans.
     */

    size = 2;
    for (p = cmdLine; *p != '\0'; p++) {
	if ((*p == ' ') || (*p == '\t')) {	/* INTL: ISO space. */
	    size++;
	    while ((*p == ' ') || (*p == '\t')) { /* INTL: ISO space. */
		p++;
	    }
	    if (*p == '\0') {
		break;
	    }
	}
    }
    argSpace = (char *) ckalloc(
	    (unsigned) (size * sizeof(char *) + strlen(cmdLine) + 1));
    argv = (char **) argSpace;
    argSpace += size * sizeof(char *);
    size--;

    p = cmdLine;
    for (argc = 0; argc < size; argc++) {
	argv[argc] = arg = argSpace;
	while ((*p == ' ') || (*p == '\t')) {	/* INTL: ISO space. */
	    p++;
	}
	if (*p == '\0') {
	    break;
	}

	inquote = 0;
	slashes = 0;
	while (1) {
	    copy = 1;
	    while (*p == '\\') {
		slashes++;
		p++;
	    }
	    if (*p == '"') {
		if ((slashes & 1) == 0) {
		    copy = 0;
		    if ((inquote) && (p[1] == '"')) {
			p++;
			copy = 1;
		    } else {
			inquote = !inquote;
		    }
		}
		slashes >>= 1;
	    }

	    while (slashes) {
		*arg = '\\';
		arg++;
		slashes--;
	    }

	    if ((*p == '\0') || (!inquote &&
		    ((*p == ' ') || (*p == '\t')))) {	/* INTL: ISO space. */
		break;
	    }
	    if (copy != 0) {
		*arg = *p;
		arg++;
	    }
	    p++;
	}
	*arg = '\0';
	argSpace = arg + 1;
    }
    argv[argc] = NULL;

    *argcPtr = argc;
    *argvPtr = argv;
}
#endif /* __GNUC__ */

/*
 * Local Variables:
 * mode: c
 * c-basic-offset: 4
 * fill-column: 78
 * End:
 */
