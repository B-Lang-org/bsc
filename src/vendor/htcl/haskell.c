#include "HsFFI.h"
#include "Rts.h"

#include "tcl.h"

// releases a Tcl object whose reference Haskell held (HTcl.htclReleaseObjs),
// with the Tcl 8.5 workaround below
void
htcl_finalizeTclObj(Tcl_Obj* o)
{
#ifdef TCL85
/* Workaround for https://sourceforge.net/p/tcl/bugs/4043/ */
  if (Tcl_IsShared(o) == 1)
#endif
  Tcl_DecrRefCount(o);
}
