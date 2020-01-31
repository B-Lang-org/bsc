# itcl.decls --
#
#	This file contains the declarations for all supported public
#	functions that are exported by the Itcl library via the stubs table.
#	This file is used to generate the itclDecls.h, itclPlatDecls.h,
#	itclStub.c, and itclPlatStub.c files.
#	
#
# Copyright (c) 1998-1999 by Scriptics Corporation.
# See the file "license.terms" for information on usage and redistribution
# of this file, and for a DISCLAIMER OF ALL WARRANTIES.
# 
# RCS: $Id: itcl.decls,v 1.3 2003/12/17 02:25:37 davygrvy Exp $

library itcl

# Define the itcl interface with several sub interfaces:
#     itclPlat	 - platform specific public
#     itclInt	 - generic private
#     itclPlatInt - platform specific private

interface itcl
hooks {itclInt}

# Declare each of the functions in the public Tcl interface.  Note that
# the an index should never be reused for a different function in order
# to preserve backwards compatibility.

declare 0 generic {
    int Itcl_Init(Tcl_Interp *interp)
}
declare 1 generic {
    int Itcl_SafeInit(Tcl_Interp *interp)
}
declare 2 generic {
    int Itcl_RegisterC(Tcl_Interp *interp, CONST char *name, \
        Tcl_CmdProc *proc, ClientData clientData, \
        Tcl_CmdDeleteProc *deleteProc)
}
declare 3 generic {
    int Itcl_RegisterObjC (Tcl_Interp *interp, CONST char *name, \
        Tcl_ObjCmdProc *proc, ClientData clientData, \
        Tcl_CmdDeleteProc *deleteProc)
}
declare 4 generic {
    int Itcl_FindC(Tcl_Interp *interp, CONST char *name, \
	Tcl_CmdProc **argProcPtr, Tcl_ObjCmdProc **objProcPtr, \
	ClientData *cDataPtr)
}
declare 5 generic {
    void Itcl_InitStack(Itcl_Stack *stack)
}
declare 6 generic {
    void Itcl_DeleteStack(Itcl_Stack *stack)
}
declare 7 generic {
    void Itcl_PushStack(ClientData cdata, Itcl_Stack *stack)
}
declare 8 generic {
    ClientData Itcl_PopStack(Itcl_Stack *stack)
}
declare 9 generic {
    ClientData Itcl_PeekStack(Itcl_Stack *stack)
}
declare 10 generic {
    ClientData Itcl_GetStackValue(Itcl_Stack *stack, int pos)
}
declare 11 generic {
    void Itcl_InitList(Itcl_List *listPtr)
}
declare 12 generic {
    void Itcl_DeleteList(Itcl_List *listPtr)
}
declare 13 generic {
    Itcl_ListElem* Itcl_CreateListElem(Itcl_List *listPtr)
}
declare 14 generic {
    Itcl_ListElem* Itcl_DeleteListElem(Itcl_ListElem *elemPtr)
}
declare 15 generic {
    Itcl_ListElem* Itcl_InsertList(Itcl_List *listPtr, ClientData val)
}
declare 16 generic {
    Itcl_ListElem* Itcl_InsertListElem (Itcl_ListElem *pos, ClientData val)
}
declare 17 generic {
    Itcl_ListElem* Itcl_AppendList(Itcl_List *listPtr, ClientData val)
}
declare 18 generic {
    Itcl_ListElem* Itcl_AppendListElem(Itcl_ListElem *pos, ClientData val)
}
declare 19 generic {
    void Itcl_SetListValue(Itcl_ListElem *elemPtr, ClientData val)
}
declare 20 generic {
    void Itcl_EventuallyFree(ClientData cdata, Tcl_FreeProc *fproc)
}
declare 21 generic {
    void Itcl_PreserveData(ClientData cdata)
}
declare 22 generic {
    void Itcl_ReleaseData(ClientData cdata)
}
declare 23 generic {
    Itcl_InterpState Itcl_SaveInterpState(Tcl_Interp* interp, int status)
}
declare 24 generic {
    int Itcl_RestoreInterpState(Tcl_Interp* interp, Itcl_InterpState state)
}
declare 25 generic {
    void Itcl_DiscardInterpState(Itcl_InterpState state)
}
