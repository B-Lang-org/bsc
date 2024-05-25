/*
 * tclAppInit.c --
 *
 *        Provides a default version of the main program and Tcl_AppInit
 *        procedure for Tcl applications (without Tk).
 *
 * Copyright (c) 1993 The Regents of the University of California.
 * Copyright (c) 1994-1997 Sun Microsystems, Inc.
 * Copyright (c) 1998-1999 by Scriptics Corporation.
 *
 * See the file "license.terms" for information on usage and redistribution
 * of this file, and for a DISCLAIMER OF ALL WARRANTIES.
 *
 * RCS: @(#) $Id: tclAppInit.c,v 1.11 2002/05/31 22:20:22 dgp Exp $
 */

#include "tcl.h"
#include "stdlib.h"

extern int htcl_initHaskellRTS(int *argc, char **argv[]) ;
extern char *TclSetPreInitScript (char *string);

// Include for the export from Haskell
#ifdef __GLASGOW_HASKELL__
#include "BlueTcl_stub.h"
#endif
#ifdef __GLASGOW_HASKELL__
extern void __stginit_BlueTcl ( void );
#endif

int bluetcl_AppInit(Tcl_Interp *interp);
int Bluespec_Init(Tcl_Interp *interp);

/*
 *----------------------------------------------------------------------
 *
 * main --
 *
 *        This is the main program for the application.
 *
 * Results:
 *        None: Tcl_Main never returns here, so this procedure never
 *        returns either.
 *
 * Side effects:
 *        Whatever the application does.
 *
 *----------------------------------------------------------------------
 */

int
main(int argc, char **argv)
{
  // Initialize Haskell
  int stat = htcl_initHaskellRTS( &argc, &argv );
  if (stat != 0) exit(stat);

#ifdef __GLASGOW_HASKELL__
#if (__GLASGOW_HASKELL__ < 804)
  hs_add_root(__stginit_BlueTcl);
#endif
#endif

  Tcl_Main(argc, argv, bluetcl_AppInit);

  return 0;                        /* Needed only to prevent compiler warning. */
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_AppInit --
 *
 *        This procedure performs application-specific initialization.
 *        Most applications, especially those that incorporate additional
 *        packages, will have their own version of this procedure.
 *
 * Results:
 *        Returns a standard Tcl completion code, and leaves an error
 *        message in the interp's result if an error occurs.
 *
 * Side effects:
 *        Depends on the startup script.
 *
 *----------------------------------------------------------------------
 */

// Source the Bluetcl init script
char startBS[] = "source $env(BLUESPECDIR)/tcllib/bluespec/bluespec.tcl ;";

char userStartFile[] = "~/.bluetclrc";


/* Bluespec Shell initialization
  0. The tcl interpreter is already started.
  1. No setup of path or tcl_library needed before loading standard tcl files
  2. Load the standard tcl libraries (under Tcl_Init)
  3. Load the Bluetcl package (Bluespec_Init, also names the user rc file to load)
  4. Source the startBS script from the library
     (will add the Bluespec tcllib to the tcl search path and
      will source the user's rc file)
 */

int
bluetcl_AppInit(Tcl_Interp *interp)
{

  // TCL library must be loaded from $BLUESPECDIR, so setup the right tcllibrary path here
  char *bsdir = getenv("BLUESPECDIR");
  if ( bsdir == 0 ) {
    fprintf(stderr,"BLUESPECDIR is not set.\n" );
    exit(-1);
  }

  // Run the tcl init scripts
  // This will, among other things, initialize auto_path with TCLLIBPATH
  // from the user's environment, but only if auto_path has not yet been
  // assigned
  //
  if (Tcl_Init(interp) != TCL_OK) {
    fprintf(stderr,"Unable to start tcl -- %s\n", Tcl_GetStringResult(interp));
    exit (-1);
  }

  // Initialize the Bluespec package
  if (Bluespec_Init (interp) != TCL_OK) {
    fprintf(stderr,"Unable to initialize Bluespec extensions -- %s\n", Tcl_GetStringResult(interp));
    exit (-1);
  }
  Tcl_StaticPackage( interp, "Bluetcl", Bluespec_Init, Bluespec_Init);

  // Finish the Bluespec initialization
  if (Tcl_Eval(interp, startBS) != TCL_OK) {
    fprintf(stderr,"Trouble starting bluetcl -- %s\n", Tcl_GetStringResult(interp));
    exit(-1);
  }

  return TCL_OK;
}

int Bluespec_Init(Tcl_Interp *interp)
{
  int stat = TCL_ERROR ;
  stat = blueshell_Init_Foreign ( interp ) ;

  // Specific user startup file when ever starting a new interp.
  Tcl_SetVar(interp, "tcl_rcFileName", userStartFile, TCL_GLOBAL_ONLY);

  if ( stat == TCL_OK )
    stat = Tcl_PkgProvide(interp, "Bluetcl", "1.0");

  return stat ;
}
