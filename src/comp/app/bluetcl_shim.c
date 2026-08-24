/*
 * C shim for bluetcl, adapted from src/comp/bluetcl_Main.hsc.
 *
 * Differs from the Makefile build's bluetcl_Main.hsc: there the C `main`
 * initializes the Haskell RTS (htcl_initHaskellRTS) and then calls Tcl_Main.
 * Here the executable has a normal Haskell `main` (so the RTS is already up),
 * which calls run_bluetcl() below to hand off to Tcl.
 */
#include "tcl.h"
#include <stdlib.h>
#include <stdio.h>

/* Haskell foreign export from BlueTcl (bluetcl.hs):
   foreign export ccall "blueshell_Init_Foreign" blueshell_Init :: TclInterp -> IO Int
   Declared here so we don't depend on the generated BlueTcl_stub.h. */
extern int blueshell_Init_Foreign(Tcl_Interp *interp);

/* Source the Bluetcl init script from $BLUESPECDIR. */
static char startBS[] = "source $env(BLUESPECDIR)/tcllib/bluespec/bluespec.tcl ;";
static char userStartFile[] = "~/.bluetclrc";

int Bluespec_Init(Tcl_Interp *interp)
{
  int stat = blueshell_Init_Foreign(interp);
  Tcl_SetVar(interp, "tcl_rcFileName", userStartFile, TCL_GLOBAL_ONLY);
  if (stat == TCL_OK)
    stat = Tcl_PkgProvide(interp, "Bluetcl", "1.0");
  return stat;
}

int bluetcl_AppInit(Tcl_Interp *interp)
{
  if (getenv("BLUESPECDIR") == NULL) {
    fprintf(stderr, "BLUESPECDIR is not set.\n");
    exit(-1);
  }
  if (Tcl_Init(interp) != TCL_OK) {
    fprintf(stderr, "Unable to start tcl -- %s\n", Tcl_GetStringResult(interp));
    exit(-1);
  }
  if (Bluespec_Init(interp) != TCL_OK) {
    fprintf(stderr, "Unable to initialize Bluespec extensions -- %s\n",
            Tcl_GetStringResult(interp));
    exit(-1);
  }
  Tcl_StaticPackage(interp, "Bluetcl", Bluespec_Init, Bluespec_Init);
  if (Tcl_Eval(interp, startBS) != TCL_OK) {
    fprintf(stderr, "Trouble starting bluetcl -- %s\n", Tcl_GetStringResult(interp));
    exit(-1);
  }
  return TCL_OK;
}

/* Entry point called from the Haskell main (RTS already running).
   Tcl_Main runs the interpreter loop and does not return. */
void run_bluetcl(int argc, char **argv)
{
  Tcl_Main(argc, argv, bluetcl_AppInit);
}
