/*
 * tclPanic.c --
 *
 *	Source code for the "Tcl_Panic" library procedure for Tcl; individual
 *	applications will probably call Tcl_SetPanicProc() to set an
 *	application-specific panic procedure.
 *
 * Copyright (c) 1988-1993 The Regents of the University of California.
 * Copyright (c) 1994 Sun Microsystems, Inc.
 * Copyright (c) 1998-1999 by Scriptics Corporation.
 *
 * See the file "license.terms" for information on usage and redistribution of
 * this file, and for a DISCLAIMER OF ALL WARRANTIES.
 *
 * RCS: @(#) $Id: tclPanic.c,v 1.10 2006/03/09 23:13:25 dgp Exp $
 */

#include "tclInt.h"

/*
 * The panicProc variable contains a pointer to an application specific panic
 * procedure.
 */

static Tcl_PanicProc *panicProc = NULL;

/*
 * The platformPanicProc variable contains a pointer to a platform specific
 * panic procedure, if any. (TclpPanic may be NULL via a macro.)
 */

static Tcl_PanicProc *CONST platformPanicProc = TclpPanic;

/*
 *----------------------------------------------------------------------
 *
 * Tcl_SetPanicProc --
 *
 *	Replace the default panic behavior with the specified function.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	Sets the panicProc variable.
 *
 *----------------------------------------------------------------------
 */

void
Tcl_SetPanicProc(
    Tcl_PanicProc *proc)
{
    panicProc = proc;
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_PanicVA --
 *
 *	Print an error message and kill the process.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	The process dies, entering the debugger if possible.
 *
 *----------------------------------------------------------------------
 */

void
Tcl_PanicVA(
    CONST char *format,		/* Format string, suitable for passing to
				 * fprintf. */
    va_list argList)		/* Variable argument list. */
{
    char *arg1, *arg2, *arg3, *arg4;	/* Additional arguments (variable in
					 * number) to pass to fprintf. */
    char *arg5, *arg6, *arg7, *arg8;

    arg1 = va_arg(argList, char *);
    arg2 = va_arg(argList, char *);
    arg3 = va_arg(argList, char *);
    arg4 = va_arg(argList, char *);
    arg5 = va_arg(argList, char *);
    arg6 = va_arg(argList, char *);
    arg7 = va_arg(argList, char *);
    arg8 = va_arg(argList, char *);

    if (panicProc != NULL) {
	(void) (*panicProc)(format, arg1, arg2, arg3, arg4,
		arg5, arg6, arg7, arg8);
    } else if (platformPanicProc != NULL) {
	(void) (*platformPanicProc)(format, arg1, arg2, arg3, arg4,
		arg5, arg6, arg7, arg8);
    } else {
	(void) fprintf(stderr, format, arg1, arg2, arg3, arg4, arg5, arg6,
		arg7, arg8);
	(void) fprintf(stderr, "\n");
	(void) fflush(stderr);
	abort();
    }
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_Panic --
 *
 *	Print an error message and kill the process.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	The process dies, entering the debugger if possible.
 *
 *----------------------------------------------------------------------
 */

	/* ARGSUSED */
void
Tcl_Panic(
    CONST char *format,
    ...)
{
    va_list argList;

    va_start(argList, format);
    Tcl_PanicVA(format, argList);
    va_end (argList);
}

/*
 * Local Variables:
 * mode: c
 * c-basic-offset: 4
 * fill-column: 78
 * End:
 */
