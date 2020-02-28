// Functions which are needed for the Haskell interface to tcl

#include "htclFunctions.h"


// Need to have real functions and not Macros
void HTcl_DecrRefCount ( Tcl_Obj *o)
{
  Tcl_DecrRefCount (o);
}

void HTcl_IncrRefCount ( Tcl_Obj *o)
{
  Tcl_IncrRefCount (o);
}

int HTcl_TclOKValue ()
{
  return TCL_OK ;
}

int HTcl_TclErrorValue ()
{
  return TCL_ERROR ;
}
