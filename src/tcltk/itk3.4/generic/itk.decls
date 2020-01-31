# itk.decls --
#
#	This file contains the declarations for all supported public
#	functions that are exported by the Itk library via the stubs table.
#	This file is used to generate the itkDecls.h file.
#	
# See the file "license.terms" for information on usage and redistribution
# of this file, and for a DISCLAIMER OF ALL WARRANTIES.
# 
# RCS: $Id: itk.decls,v 1.5 2002/03/03 01:57:11 andreas_kupries Exp $

library itk
interface itk

# Declare each of the functions in the public Itk interface.  Note that
# the an index should never be reused for a different function in order
# to preserve backwards compatibility.


#
#  Exported functions:
#

declare 0 generic {
    int Itk_Init (Tcl_Interp *interp)
}
declare 1 generic {
    int Itk_SafeInit (Tcl_Interp *interp)
}


#
#  Functions used internally by this package:
#

declare 2 generic {
    int Itk_ConfigBodyCmd (ClientData cdata, Tcl_Interp *interp, \
        int objc, Tcl_Obj *CONST objv[])
}
declare 3 generic {
    int Itk_UsualCmd (ClientData cdata, Tcl_Interp *interp, int objc, \
        Tcl_Obj *CONST objv[])
}


#
#  Functions for managing options included in class definitions:
#

declare 4 generic {
    int Itk_ClassOptionDefineCmd (ClientData cdata, Tcl_Interp *interp, \
        int objc, Tcl_Obj *CONST objv[])
}
declare 5 generic {
    int Itk_ClassOptionIllegalCmd (ClientData cdata, Tcl_Interp *interp, \
        int objc, Tcl_Obj *CONST objv[])
}
declare 6 generic {
    int Itk_ConfigClassOption (Tcl_Interp *interp, ItclObject *contextObj, \
        ClientData cdata, CONST char* newVal)
}
declare 7 generic {
    ItkClassOptTable* Itk_CreateClassOptTable( Tcl_Interp *interp, \
        ItclClass *cdefn)
}
declare 8 generic {
    ItkClassOptTable* Itk_FindClassOptTable (ItclClass *cdefn)
}
#declare 9 generic {
#    void Itk_DeleteClassOptTable (Tcl_Interp *interp, ItclClass *cdefn)
#}
declare 10 generic {
    int Itk_CreateClassOption (Tcl_Interp *interp, ItclClass *cdefn, \
        char *switchName, char *resName, char *resClass, char *defVal, \
        char *config, ItkClassOption **optPtr)
}
declare 11 generic {
    ItkClassOption* Itk_FindClassOption (ItclClass *cdefn, char *switchName)
}
declare 12 generic {
    void Itk_DelClassOption (ItkClassOption *opt)
}


#
#  Functions needed for the Archetype base class:
#

declare 13 generic {
    int Itk_ArchetypeInit (Tcl_Interp* interp)
}


#
#  Functions for maintaining the ordered option list:
#

declare 14 generic {
    void Itk_OptListInit (ItkOptList* olist, Tcl_HashTable *options)
}
declare 15 generic {
    void Itk_OptListFree (ItkOptList* olist)
}
declare 16 generic {
    void Itk_OptListAdd (ItkOptList* olist, Tcl_HashEntry *entry)
}
declare 17 generic {
    void Itk_OptListRemove (ItkOptList* olist, Tcl_HashEntry *entry)
}
