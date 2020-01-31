# itclInt.decls --
#
#	This file contains the declarations for all unsupported
#	functions that are exported by the Itcl library.
#
#	By "unsupported", it should be noted that due to Tcl's hiding
#	of the data types used, we inherit this hidden-ness ourselves,
#	too, unfortunately.
#
# Copyright (c) 1998-1999 by Scriptics Corporation.
# See the file "license.terms" for information on usage and redistribution
# of this file, and for a DISCLAIMER OF ALL WARRANTIES.
# 
# RCS: @(#) $Id: itclInt.decls,v 1.9 2007/05/24 21:40:23 hobbs Exp $

library itcl

# Define the unsupported generic interfaces.

interface itclInt


#
# Functions used within the package, but not considered "public"
#

declare 0 generic {
    int Itcl_IsClassNamespace(Tcl_Namespace *namesp)
}
declare 1 generic {
    int Itcl_IsClass (Tcl_Command cmd)
}
declare 2 generic {
    ItclClass* Itcl_FindClass (Tcl_Interp* interp, CONST char* path, int autoload)
}
declare 3 generic {
    int Itcl_FindObject (Tcl_Interp *interp, CONST char *name, ItclObject **roPtr)
}
declare 4 generic {   
    int Itcl_IsObject (Tcl_Command cmd)
}
declare 5 generic {
    int Itcl_ObjectIsa (ItclObject *contextObj, ItclClass *cdefn)
}
declare 6 generic {
    int Itcl_Protection (Tcl_Interp *interp, int newLevel)
}
declare 7 generic {
    char* Itcl_ProtectionStr (int pLevel)
}
declare 8 generic {
    int Itcl_CanAccess (ItclMember* memberPtr, Tcl_Namespace* fromNsPtr)
}
declare 9 generic {
    int Itcl_CanAccessFunc (ItclMemberFunc* mfunc, Tcl_Namespace* fromNsPtr)
}
declare 10 generic {
    Tcl_Namespace* Itcl_GetTrueNamespace (Tcl_Interp *interp, \
        ItclObjectInfo *info)
}
declare 11 generic {
    void Itcl_ParseNamespPath (CONST char *name, Tcl_DString *buffer, \
        char **head, char **tail)
}
declare 12 generic {
    int Itcl_DecodeScopedCommand (Tcl_Interp *interp, CONST char *name, \
        Tcl_Namespace **rNsPtr, char **rCmdPtr)
}
declare 13 generic {
    int Itcl_EvalArgs (Tcl_Interp *interp, int objc, Tcl_Obj *CONST objv[])
}
declare 14 generic {
    Tcl_Obj* Itcl_CreateArgs (Tcl_Interp *interp, CONST char *string, \
        int objc, Tcl_Obj *CONST objv[])
}
declare 15 generic {
    int Itcl_PushContext (Tcl_Interp *interp, ItclMember *member, \
        ItclClass *contextClass, ItclObject *contextObj, \
        ItclContext *contextPtr)
}
declare 16 generic {
    void Itcl_PopContext (Tcl_Interp *interp, ItclContext *contextPtr)
}
declare 17 generic {
    int Itcl_GetContext (Tcl_Interp *interp, ItclClass **cdefnPtr, \
        ItclObject **odefnPtr)
}
declare 18 generic {
    void Itcl_InitHierIter (ItclHierIter *iter, ItclClass *cdefn)
}
declare 19 generic {
    void Itcl_DeleteHierIter (ItclHierIter *iter)
}
declare 20 generic {
    ItclClass* Itcl_AdvanceHierIter (ItclHierIter *iter)
}
declare 21 generic {
    int Itcl_FindClassesCmd (ClientData clientData, Tcl_Interp *interp, \
        int objc, Tcl_Obj *CONST objv[])
}
declare 22 generic {
    int Itcl_FindObjectsCmd (ClientData clientData, Tcl_Interp *interp, \
        int objc, Tcl_Obj *CONST objv[])
}
declare 23 generic {
    int Itcl_ProtectionCmd (ClientData clientData, Tcl_Interp *interp, \
        int objc, Tcl_Obj *CONST objv[])
}
declare 24 generic {
    int Itcl_DelClassCmd (ClientData clientData, Tcl_Interp *interp, \
        int objc, Tcl_Obj *CONST objv[])
}
declare 25 generic {
    int Itcl_DelObjectCmd (ClientData clientData, Tcl_Interp *interp, \
        int objc, Tcl_Obj *CONST objv[])
}
declare 26 generic {
    int Itcl_ScopeCmd (ClientData clientData, Tcl_Interp *interp, \
        int objc, Tcl_Obj *CONST objv[])
}
declare 27 generic {
    int Itcl_CodeCmd (ClientData clientData, Tcl_Interp *interp, \
        int objc, Tcl_Obj *CONST objv[])
}
declare 28 generic {	
    int Itcl_StubCreateCmd (ClientData clientData, Tcl_Interp *interp, \
        int objc, Tcl_Obj *CONST objv[])
}
declare 29 generic {
    int Itcl_StubExistsCmd (ClientData clientData, Tcl_Interp *interp, \
        int objc, Tcl_Obj *CONST objv[])
}
declare 30 generic {
    int Itcl_IsStub (Tcl_Command cmd)
}


#
#  Functions for manipulating classes
#

declare 31 generic {
    int Itcl_CreateClass (Tcl_Interp* interp, CONST char* path, \
        ItclObjectInfo *info, ItclClass **rPtr)
}
declare 32 generic {
    int Itcl_DeleteClass (Tcl_Interp *interp, ItclClass *cdefnPtr)
}
declare 33 generic {
    Tcl_Namespace* Itcl_FindClassNamespace (Tcl_Interp* interp, CONST char* path)
}
declare 34 generic {
    int Itcl_HandleClass (ClientData clientData, Tcl_Interp *interp, \
        int objc, Tcl_Obj *CONST objv[])
}
declare 35 generic {
    int Itcl_ClassCmdResolver (Tcl_Interp *interp, CONST char* name, \
        Tcl_Namespace *context, int flags, Tcl_Command *rPtr)
}
declare 36 generic {
    int Itcl_ClassVarResolver (Tcl_Interp *interp, CONST char* name, \
        Tcl_Namespace *context, int flags, Tcl_Var *rPtr)
}
declare 37 generic {
    int Itcl_ClassCompiledVarResolver (Tcl_Interp *interp, CONST char* name, \
        int length, Tcl_Namespace *context, Tcl_ResolvedVarInfo **rPtr)
}
declare 38 generic {
    void Itcl_BuildVirtualTables (ItclClass* cdefnPtr)
}
declare 39 generic {
    int Itcl_CreateVarDefn (Tcl_Interp *interp, ItclClass* cdefn, \
        char* name, char* init, char* config, ItclVarDefn** vdefnPtr)
}
declare 40 generic {
    void Itcl_DeleteVarDefn (ItclVarDefn *vdefn)
}
declare 41 generic {
    CONST char* Itcl_GetCommonVar (Tcl_Interp *interp, CONST char *name, \
        ItclClass *contextClass)
}
declare 42 generic {
    ItclMember* Itcl_CreateMember (Tcl_Interp* interp, ItclClass *cdefn, \
        CONST char* name)
}
declare 43 generic {
    void Itcl_DeleteMember (ItclMember *memPtr)
}


#
#  Functions for manipulating objects
#

declare 44 generic {
    int Itcl_CreateObject (Tcl_Interp *interp, CONST char* name, ItclClass *cdefn, \
        int objc, Tcl_Obj *CONST objv[], ItclObject **roPtr)
}
declare 45 generic {
    int Itcl_DeleteObject (Tcl_Interp *interp, ItclObject *contextObj)
}
declare 46 generic {
    int Itcl_DestructObject (Tcl_Interp *interp, ItclObject *contextObj, \
        int flags)
}
declare 47 generic {
    int Itcl_HandleInstance (ClientData clientData, Tcl_Interp *interp, \
        int objc, Tcl_Obj *CONST objv[])
}
declare 48 generic {
    CONST char* Itcl_GetInstanceVar (Tcl_Interp *interp, CONST char *name, \
        ItclObject *contextObj, ItclClass *contextClass)
}
declare 49 generic {
    int Itcl_ScopedVarResolver (Tcl_Interp *interp, CONST char *name, \
        Tcl_Namespace *contextNs, int flags, Tcl_Var *rPtr)
}


#
#  Functions for manipulating methods and procs
#

declare 50 generic {
    int Itcl_BodyCmd (ClientData dummy, Tcl_Interp *interp, int objc, \
        Tcl_Obj *CONST objv[])
}
declare 51 generic {
    int Itcl_ConfigBodyCmd (ClientData dummy, Tcl_Interp *interp, int objc, \
        Tcl_Obj *CONST objv[])
}
declare 52 generic {
    int Itcl_CreateMethod (Tcl_Interp* interp, ItclClass *cdefn,
	CONST char* name, CONST char* arglist, CONST char* body)
}
declare 53 generic {
    int Itcl_CreateProc (Tcl_Interp* interp, ItclClass *cdefn,
	CONST char* name, CONST char* arglist, CONST char* body)
}
declare 54 generic {
    int Itcl_CreateMemberFunc (Tcl_Interp* interp, ItclClass *cdefn, \
        CONST char* name, CONST char* arglist, CONST char* body, \
	ItclMemberFunc** mfuncPtr)
}
declare 55 generic {
    int Itcl_ChangeMemberFunc (Tcl_Interp* interp, ItclMemberFunc* mfunc, \
        CONST char* arglist, CONST char* body)
}
declare 56 generic {
    void Itcl_DeleteMemberFunc (CONST char* cdata)
}
declare 57 generic {
    int Itcl_CreateMemberCode (Tcl_Interp* interp, ItclClass *cdefn, \
        CONST char* arglist, CONST char* body, ItclMemberCode** mcodePtr)
}
declare 58 generic {
    void Itcl_DeleteMemberCode (CONST char* cdata)
}
declare 59 generic {
    int Itcl_GetMemberCode (Tcl_Interp* interp, ItclMember* member)
}
#declare 60 generic {
#    int Itcl_CompileMemberCodeBody (Tcl_Interp *interp, ItclMember *member, \
#        char *desc, Tcl_Obj *bodyPtr)
#}
declare 61 generic {
    int Itcl_EvalMemberCode (Tcl_Interp *interp, ItclMemberFunc *mfunc, \
        ItclMember *member, ItclObject *contextObj, int objc, \
        Tcl_Obj *CONST objv[])
}
declare 62 generic {
    int Itcl_CreateArgList (Tcl_Interp* interp, CONST char* decl, int* argcPtr, \
        CompiledLocal** argPtr)
}
declare 63 generic {
    CompiledLocal* Itcl_CreateArg (CONST char* name, CONST char* init)
}
declare 64 generic {
    void Itcl_DeleteArgList (CompiledLocal *arglist)
}
declare 65 generic {
    Tcl_Obj* Itcl_ArgList (int argc, CompiledLocal* arglist)
}
declare 66 generic {
    int Itcl_EquivArgLists (CompiledLocal* arg1, int arg1c, \
        CompiledLocal* arg2, int arg2c)
}
declare 67 generic {
    void Itcl_GetMemberFuncUsage (ItclMemberFunc *mfunc, \
        ItclObject *contextObj, Tcl_Obj *objPtr)
}
declare 68 generic {
    int Itcl_ExecMethod (ClientData clientData, Tcl_Interp *interp, int objc, \
        Tcl_Obj *CONST objv[])
}
declare 69 generic {
    int Itcl_ExecProc (ClientData clientData, Tcl_Interp *interp, \
        int objc, Tcl_Obj *CONST objv[])
}
declare 70 generic {
    int Itcl_AssignArgs (Tcl_Interp *interp, int objc, Tcl_Obj *CONST objv[], \
        ItclMemberFunc *mfunc)
}
declare 71 generic {
    int Itcl_ConstructBase (Tcl_Interp *interp, ItclObject *contextObj, \
        ItclClass *contextClass)
}
declare 72 generic {
    int Itcl_InvokeMethodIfExists (Tcl_Interp *interp, CONST char *name, \
        ItclClass *contextClass, ItclObject *contextObj, int objc, \
        Tcl_Obj *CONST objv[])
}
#declare 73 generic {
#    int Itcl_EvalBody (Tcl_Interp *interp, Tcl_Obj *bodyPtr)
#}
declare 74 generic {
    int Itcl_ReportFuncErrors (Tcl_Interp* interp, ItclMemberFunc *mfunc, \
        ItclObject *contextObj, int result)
}


#
#  Commands for parsing class definitions
#

declare 75 generic {
    int Itcl_ParseInit (Tcl_Interp *interp, ItclObjectInfo *info)
}
declare 76 generic {
    int Itcl_ClassCmd (ClientData clientData, Tcl_Interp *interp, int objc, \
        Tcl_Obj *CONST objv[])
}
declare 77 generic {
    int Itcl_ClassInheritCmd (ClientData clientData, Tcl_Interp *interp, \
        int objc, Tcl_Obj *CONST objv[])
}
declare 78 generic {
    int Itcl_ClassProtectionCmd (ClientData clientData, Tcl_Interp *interp, \
        int objc, Tcl_Obj *CONST objv[])
}
declare 79 generic {
    int Itcl_ClassConstructorCmd (ClientData clientData, Tcl_Interp *interp, \
        int objc, Tcl_Obj *CONST objv[])
}
declare 80 generic {
    int Itcl_ClassDestructorCmd (ClientData clientData, Tcl_Interp *interp, \
        int objc, Tcl_Obj *CONST objv[])
}
declare 81 generic {
    int Itcl_ClassMethodCmd (ClientData clientData, Tcl_Interp *interp, \
        int objc, Tcl_Obj *CONST objv[])
}
declare 82 generic {
    int Itcl_ClassProcCmd (ClientData clientData, Tcl_Interp *interp, \
        int objc, Tcl_Obj *CONST objv[])
}
declare 83 generic {
    int Itcl_ClassVariableCmd (ClientData clientData, Tcl_Interp *interp, \
        int objc, Tcl_Obj *CONST objv[])
}
declare 84 generic {
    int Itcl_ClassCommonCmd (ClientData clientData, Tcl_Interp *interp, \
        int objc, Tcl_Obj *CONST objv[])
}
declare 85 generic {
    int Itcl_ParseVarResolver (Tcl_Interp *interp, CONST char* name, \
        Tcl_Namespace *contextNs, int flags, Tcl_Var* rPtr)
}


#
#  Commands in the "builtin" namespace
#

declare 86 generic {
    int Itcl_BiInit (Tcl_Interp *interp)
}
declare 87 generic {
    int Itcl_InstallBiMethods (Tcl_Interp *interp, ItclClass *cdefn)
}
declare 88 generic {
    int Itcl_BiIsaCmd (ClientData clientData, Tcl_Interp *interp, \
        int objc, Tcl_Obj *CONST objv[])
}
declare 89 generic {
    int Itcl_BiConfigureCmd (ClientData clientData, Tcl_Interp *interp, \
        int objc, Tcl_Obj *CONST objv[])
}
declare 90 generic {
    int Itcl_BiCgetCmd (ClientData clientData, Tcl_Interp *interp, int objc, \
        Tcl_Obj *CONST objv[])
}
declare 91 generic {
    int Itcl_BiChainCmd (ClientData dummy, Tcl_Interp *interp, int objc, \
        Tcl_Obj *CONST objv[])
}
declare 92 generic {
    int Itcl_BiInfoClassCmd (ClientData dummy, Tcl_Interp *interp, int objc, \
        Tcl_Obj *CONST objv[])
}
declare 93 generic {
    int Itcl_BiInfoInheritCmd (ClientData dummy, Tcl_Interp *interp, int objc, \
        Tcl_Obj *CONST objv[])
}
declare 94 generic {
    int Itcl_BiInfoHeritageCmd (ClientData dummy, Tcl_Interp *interp, \
        int objc, Tcl_Obj *CONST objv[])
}
declare 95 generic {
    int Itcl_BiInfoFunctionCmd (ClientData dummy, Tcl_Interp *interp, \
        int objc, Tcl_Obj *CONST objv[])
}
declare 96 generic {
    int Itcl_BiInfoVariableCmd (ClientData dummy, Tcl_Interp *interp, \
        int objc, Tcl_Obj *CONST objv[])
}
declare 97 generic {
    int Itcl_BiInfoBodyCmd (ClientData dummy, Tcl_Interp *interp, int objc, \
        Tcl_Obj *CONST objv[])
}
declare 98 generic {
    int Itcl_BiInfoArgsCmd (ClientData dummy, Tcl_Interp *interp, int objc, \
        Tcl_Obj *CONST objv[])
}
declare 99 generic {
    int Itcl_DefaultInfoCmd (ClientData dummy, Tcl_Interp *interp, int objc, \
        Tcl_Obj *CONST objv[])
}


#
#  Ensembles
#

declare 100 generic {
    int Itcl_EnsembleInit (Tcl_Interp *interp)
}
declare 101 generic {
    int Itcl_CreateEnsemble (Tcl_Interp *interp, CONST char* ensName)
}
declare 102 generic {
    int Itcl_AddEnsemblePart (Tcl_Interp *interp, CONST char* ensName, \
        CONST char* partName, CONST char* usageInfo, Tcl_ObjCmdProc *objProc, \
        ClientData clientData, Tcl_CmdDeleteProc *deleteProc)
}
declare 103 generic {
    int Itcl_GetEnsemblePart (Tcl_Interp *interp, CONST char *ensName, \
        CONST char *partName, Tcl_CmdInfo *infoPtr)
}
declare 104 generic {
    int Itcl_IsEnsemble (Tcl_CmdInfo* infoPtr)
}
declare 105 generic {
    int Itcl_GetEnsembleUsage (Tcl_Interp *interp, CONST char *ensName, \
        Tcl_Obj *objPtr)
}
declare 106 generic {
    int Itcl_GetEnsembleUsageForObj (Tcl_Interp *interp, Tcl_Obj *ensObjPtr, \
        Tcl_Obj *objPtr)
}
declare 107 generic {
    int Itcl_EnsembleCmd (ClientData clientData, Tcl_Interp *interp, int objc, \
        Tcl_Obj *CONST objv[])
}
declare 108 generic {
    int Itcl_EnsPartCmd (ClientData clientData, Tcl_Interp *interp, int objc, \
        Tcl_Obj *CONST objv[])
}
declare 109 generic {
    int Itcl_EnsembleErrorCmd (ClientData clientData, Tcl_Interp *interp, \
        int objc, Tcl_Obj *CONST objv[])
}


#
#  Commands provided for backward compatibility
#

# not used anymore (3.3)
#declare 110 generic {
#    int Itcl_OldInit (Tcl_Interp* interp, ItclObjectInfo* info)
#}
#declare 111 generic {
#    int Itcl_InstallOldBiMethods (Tcl_Interp *interp, ItclClass *cdefn)
#}


#
#  Things that should be in the Tcl core.
#

declare 112 generic {
    Itcl_CallFrame* _Tcl_GetCallFrame (Tcl_Interp *interp, int level)
}
declare 113 generic {
    Itcl_CallFrame* _Tcl_ActivateCallFrame (Tcl_Interp *interp, \
        Itcl_CallFrame *framePtr)
}
declare 114 generic {
    Var* _TclNewVar (void)
}
declare 115 generic {
    void Itcl_Assert (CONST char *testExpr, CONST char *fileName, int lineNum)
}

declare 116 generic {
    int Itcl_IsObjectCmd (ClientData clientData, Tcl_Interp *interp, \
    int objc, Tcl_Obj *CONST objv[])
}
declare 117 generic {
    int Itcl_IsClassCmd (ClientData clientData, Tcl_Interp *interp, \
    int objc, Tcl_Obj *CONST objv[])
}
