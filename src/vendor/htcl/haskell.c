#include "HsFFI.h"
#include "Rts.h"

#include "tcl.h"

// finalizer callback for Tcl objects; we need a function pointer to this
// callback, and Tcl_DecrRefCount is a macro, so we have to write a manual
// wrapper (not even CApiFFI works for the ptr-to-fn use case)
void
htcl_finalizeTclObj(Tcl_Obj* o)
{
#ifdef TCL85
/* Workaround for https://sourceforge.net/p/tcl/bugs/4043/ */
  if (Tcl_IsShared(o) == 1)
#endif
  Tcl_DecrRefCount(o);
}
