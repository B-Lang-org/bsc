/*
 * tkAppInit.c --
 *
 *	Provides a default version of the Tcl_AppInit procedure for
 *	use in wish and similar Tk-based applications.
 *
 * Copyright (c) 1993 The Regents of the University of California.
 * Copyright (c) 1994-1997 Sun Microsystems, Inc.
 *
 * See the file "license.terms" for information on usage and redistribution
 * of this file, and for a DISCLAIMER OF ALL WARRANTIES.
 *
 * RCS: @(#) $Id: tkAppInit.c,v 1.7 2002/06/21 20:24:29 dgp Exp $
 */

#include "tcl.h"
#include "tk.h"
#include "stdlib.h"


extern int init_haskellSystem(int *argc, char **argv[]) ;
extern char *TclSetPreInitScript (char *string);

/// Include for the export from Haskell
#ifdef __GLASGOW_HASKELL__
#include "BlueTcl_stub.h"
#endif
#ifdef __GLASGOW_HASKELL__
extern void __stginit_BlueTcl ( void );
#endif

int bluewish_AppInit(Tcl_Interp *interp);
int Bluespec_Init(Tcl_Interp *interp) ;

extern int Itcl_Init(Tcl_Interp *interp) ;
extern int Tk_Init(Tcl_Interp *interp) ;
extern int Itk_Init(Tcl_Interp *interp) ;
extern int Itcl_SafeInit(Tcl_Interp *interp) ;
extern int Tk_SafeInit(Tcl_Interp *interp) ;
extern int Itk_SafeInit(Tcl_Interp *interp) ;


/*
 *----------------------------------------------------------------------
 *
 * main --
 *
 *	This is the main program for the application.
 *
 * Results:
 *	None: Tk_Main never returns here, so this procedure never
 *	returns either.
 *
 * Side effects:
 *	Whatever the application does.
 *
 *----------------------------------------------------------------------
 */

int
main(argc, argv)
    int argc;			/* Number of command-line arguments. */
    char **argv;		/* Values of command-line arguments. */
{
  // Initialize Haskell
  int stat = init_haskellSystem( &argc, &argv );
  if (stat != 0) exit(stat);

#ifdef __GLASGOW_HASKELL__
#if (__GLASGOW_HASKELL__ < 804)
  hs_add_root(__stginit_BlueTcl);
#endif
#endif

  Tk_Main(argc, argv, bluewish_AppInit);
  return 0;			/* Needed only to prevent compiler warning. */
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_AppInit --
 *
 *	This procedure performs application-specific initialization.
 *	Most applications, especially those that incorporate additional
 *	packages, will have their own version of this procedure.
 *
 * Results:
 *	Returns a standard Tcl completion code, and leaves an error
 *	message in the interp's result if an error occurs.
 *
 * Side effects:
 *	Depends on the startup script.
 *
 *----------------------------------------------------------------------
 */

// Set up the libraries for the blueshell
char initScript2[] = "\
  lappend auto_path $env(BLUESPECDIR)/tcllib/bluespec ; \
  set tk_library $env(BLUESPECDIR)/tcllib/tk8.5 ; \
  set tcl_library $env(BLUESPECDIR)/tcllib/tcl8.5 ; \
" ;

// Startoff the execution -- seperate from user source.
char startBS[] = "source $env(BLUESPECDIR)/tcllib/bluespec/bluespec.tcl ;";


char userStartFile[] = "~/.bluetclrc";


/* Bluespec Shell initialization
  0. The tcl interperter is already started.
  1. set up the path and tcl_library for tcl before loading standard tcl files
  2. load the standard tcl libraries (under Tcl_Init)
  3. Start the Haskell engine for bluespec
  4. Source the startBS script from the library
  5. Set the user's file to source.  (Done later)
 */

int
bluewish_AppInit(interp)
    Tcl_Interp *interp;		/* Interpreter for application. */
{

  // TCL library must be loaded from $BLUESPECDIR, so setup the right tcllibrary path here
  char *bsdir = getenv("BLUESPECDIR");
  if ( bsdir == 0 ) {
    fprintf(stderr,"BLUESPECDIR is not set.\n" );
    exit(-1);
  }

  TclSetPreInitScript( initScript2 );

  if (Tcl_Init(interp) != TCL_OK) {
    fprintf(stderr,"Unable to start tcl -- %s\n", Tcl_GetStringResult(interp));
    exit (-1);
  }

  // Tk startup
  if (Tk_Init(interp) != TCL_OK) {
    fprintf(stderr,"Unable to start tk -- %s\n", Tcl_GetStringResult(interp));
    exit (-1);
  }
  Tcl_StaticPackage(interp, "Tk", Tk_Init, Tk_SafeInit);

  // Itcl startup
  if (Itcl_Init(interp) != TCL_OK) {
    fprintf(stderr,"Unable to start itcl -- %s\n", Tcl_GetStringResult(interp));
    exit (-1);
  }
  Tcl_StaticPackage(interp, "Itcl", Itcl_Init, Itcl_SafeInit);

  // ITk startup
  if (Itk_Init(interp) != TCL_OK) {
    fprintf(stderr,"Unable to start itk -- %s\n", Tcl_GetStringResult(interp));
    exit (-1);
  }
  Tcl_StaticPackage(interp, "Itk", Itk_Init, Itk_SafeInit);

  // Bluespec startup
  if (Bluespec_Init (interp) != TCL_OK) {
    fprintf(stderr,"Unable to initialize Bluespec extensions -- %s\n", Tcl_GetStringResult(interp));
    exit (-1);
  }
  Tcl_StaticPackage( interp, "Bluetcl", Bluespec_Init, Bluespec_Init);

  // Bluespec library file
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
