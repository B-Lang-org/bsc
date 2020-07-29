#include <stdio.h>
#include <stdlib.h>

#include "HsFFI.h"
#include "Rts.h"

#include "tcl.h"

// initialize the haskell runtime system
int
htcl_initHaskellRTS(int *argc, char **argv[])
{
  RtsConfig conf = defaultRtsConfig;

  conf.rts_opts_enabled = RtsOptsAll;
  conf.rts_opts = "-H256m -K10m -i1";
  hs_init_ghc(argc, argv, conf);

  // register haskell exit function, finish
  return atexit(hs_exit);
}

// finalizer callback for Tcl objects; we need a function pointer to this
// callback, and Tcl_DecrRefCount is a macro, so we have to write a manual
// wrapper (not even CApiFFI works for the ptr-to-fn use case)
void
htcl_finalizeTclObj(Tcl_Obj* o)
{
#if defined(__APPLE__) && defined(__MACH__)
/* Workaround for https://sourceforge.net/p/tcl/bugs/4043/ */
  if (Tcl_IsShared(o) == 1)
#endif
  Tcl_DecrRefCount(o);
}
