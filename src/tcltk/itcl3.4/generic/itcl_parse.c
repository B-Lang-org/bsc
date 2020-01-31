/*
 * ------------------------------------------------------------------------
 *      PACKAGE:  [incr Tcl]
 *  DESCRIPTION:  Object-Oriented Extensions to Tcl
 *
 *  [incr Tcl] provides object-oriented extensions to Tcl, much as
 *  C++ provides object-oriented extensions to C.  It provides a means
 *  of encapsulating related procedures together with their shared data
 *  in a local namespace that is hidden from the outside world.  It
 *  promotes code re-use through inheritance.  More than anything else,
 *  it encourages better organization of Tcl applications through the
 *  object-oriented paradigm, leading to code that is easier to
 *  understand and maintain.
 *
 *  Procedures in this file support the new syntax for [incr Tcl]
 *  class definitions:
 *
 *    itcl_class <className> {
 *        inherit <base-class>...
 *
 *        constructor {<arglist>} ?{<init>}? {<body>}
 *        destructor {<body>}
 *
 *        method <name> {<arglist>} {<body>}
 *        proc <name> {<arglist>} {<body>}
 *        variable <name> ?<init>? ?<config>?
 *        common <name> ?<init>?
 *
 *        public <thing> ?<args>...?
 *        protected <thing> ?<args>...?
 *        private <thing> ?<args>...?
 *    }
 *
 * ========================================================================
 *  AUTHOR:  Michael J. McLennan
 *           Bell Labs Innovations for Lucent Technologies
 *           mmclennan@lucent.com
 *           http://www.tcltk.com/itcl
 *
 *     RCS:  $Id: itcl_parse.c,v 1.12 2007/08/07 20:05:30 msofer Exp $
 * ========================================================================
 *           Copyright (c) 1993-1998  Lucent Technologies, Inc.
 * ------------------------------------------------------------------------
 * See the file "license.terms" for information on usage and redistribution
 * of this file, and for a DISCLAIMER OF ALL WARRANTIES.
 */
#include "itclInt.h"

/*
 *  Info needed for public/protected/private commands:
 */
typedef struct ProtectionCmdInfo {
    int pLevel;               /* protection level */
    ItclObjectInfo *info;     /* info regarding all known objects */
} ProtectionCmdInfo;

/*
 *  FORWARD DECLARATIONS
 */
static void ItclFreeParserCommandData _ANSI_ARGS_((char* cdata));


/*
 * ------------------------------------------------------------------------
 *  Itcl_ParseInit()
 *
 *  Invoked by Itcl_Init() whenever a new interpeter is created to add
 *  [incr Tcl] facilities.  Adds the commands needed to parse class
 *  definitions.
 * ------------------------------------------------------------------------
 */
int
Itcl_ParseInit(interp, info)
    Tcl_Interp *interp;     /* interpreter to be updated */
    ItclObjectInfo *info;   /* info regarding all known objects */
{
    Tcl_Namespace *parserNs;
    ProtectionCmdInfo *pInfo;

    /*
     *  Create the "itcl::parser" namespace used to parse class
     *  definitions.
     */
    parserNs = Tcl_CreateNamespace(interp, "::itcl::parser",
        (ClientData)info, Itcl_ReleaseData);

    if (!parserNs) {
        Tcl_AppendResult(interp,
            " (cannot initialize itcl parser)",
            (char*)NULL);
        return TCL_ERROR;
    }
    Itcl_PreserveData((ClientData)info);

    /*
     *  Add commands for parsing class definitions.
     */
    Tcl_CreateObjCommand(interp, "::itcl::parser::inherit",
        Itcl_ClassInheritCmd, (ClientData)info, (Tcl_CmdDeleteProc*)NULL);

    Tcl_CreateObjCommand(interp, "::itcl::parser::constructor",
        Itcl_ClassConstructorCmd, (ClientData)info, (Tcl_CmdDeleteProc*)NULL);

    Tcl_CreateObjCommand(interp, "::itcl::parser::destructor",
        Itcl_ClassDestructorCmd, (ClientData)info, (Tcl_CmdDeleteProc*)NULL);

    Tcl_CreateObjCommand(interp, "::itcl::parser::method",
        Itcl_ClassMethodCmd, (ClientData)info, (Tcl_CmdDeleteProc*)NULL);

    Tcl_CreateObjCommand(interp, "::itcl::parser::proc",
        Itcl_ClassProcCmd, (ClientData)info, (Tcl_CmdDeleteProc*)NULL);

    Tcl_CreateObjCommand(interp, "::itcl::parser::common",
        Itcl_ClassCommonCmd, (ClientData)info, (Tcl_CmdDeleteProc*)NULL);

    Tcl_CreateObjCommand(interp, "::itcl::parser::variable",
        Itcl_ClassVariableCmd, (ClientData)info, (Tcl_CmdDeleteProc*)NULL);

    pInfo = (ProtectionCmdInfo*)ckalloc(sizeof(ProtectionCmdInfo));
    pInfo->pLevel = ITCL_PUBLIC;
    pInfo->info = info;

    Tcl_CreateObjCommand(interp, "::itcl::parser::public",
        Itcl_ClassProtectionCmd, (ClientData)pInfo,
	    (Tcl_CmdDeleteProc*) ItclFreeParserCommandData);

    pInfo = (ProtectionCmdInfo*)ckalloc(sizeof(ProtectionCmdInfo));
    pInfo->pLevel = ITCL_PROTECTED;
    pInfo->info = info;

    Tcl_CreateObjCommand(interp, "::itcl::parser::protected",
        Itcl_ClassProtectionCmd, (ClientData)pInfo,
	    (Tcl_CmdDeleteProc*) ItclFreeParserCommandData);

    pInfo = (ProtectionCmdInfo*)ckalloc(sizeof(ProtectionCmdInfo));
    pInfo->pLevel = ITCL_PRIVATE;
    pInfo->info = info;

    Tcl_CreateObjCommand(interp, "::itcl::parser::private",
        Itcl_ClassProtectionCmd, (ClientData)pInfo,
	    (Tcl_CmdDeleteProc*) ItclFreeParserCommandData);

    /*
     *  Set the runtime variable resolver for the parser namespace,
     *  to control access to "common" data members while parsing
     *  the class definition.
     */
    Tcl_SetNamespaceResolvers(parserNs, (Tcl_ResolveCmdProc*)NULL,
        Itcl_ParseVarResolver, (Tcl_ResolveCompiledVarProc*)NULL);

    /*
     *  Install the "class" command for defining new classes.
     */
    Tcl_CreateObjCommand(interp, "::itcl::class", Itcl_ClassCmd,
        (ClientData)info, Itcl_ReleaseData);
    Itcl_PreserveData((ClientData)info);

    return TCL_OK;
}


/*
 * ------------------------------------------------------------------------
 *  Itcl_ClassCmd()
 *
 *  Invoked by Tcl whenever the user issues an "itcl::class" command to
 *  specify a class definition.  Handles the following syntax:
 *
 *    itcl::class <className> {
 *        inherit <base-class>...
 *
 *        constructor {<arglist>} ?{<init>}? {<body>}
 *        destructor {<body>}
 *
 *        method <name> {<arglist>} {<body>}
 *        proc <name> {<arglist>} {<body>}
 *        variable <varname> ?<init>? ?<config>?
 *        common <varname> ?<init>?
 *
 *        public <args>...
 *        protected <args>...
 *        private <args>...
 *    }
 *
 * ------------------------------------------------------------------------
 */
int
Itcl_ClassCmd(clientData, interp, objc, objv)
    ClientData clientData;   /* info for all known objects */
    Tcl_Interp *interp;      /* current interpreter */
    int objc;                /* number of arguments */
    Tcl_Obj *CONST objv[];   /* argument objects */
{
    ItclObjectInfo* info = (ItclObjectInfo*)clientData;

    int result, len;
    char *className;
    Tcl_Namespace *parserNs;
    ItclClass *cdefnPtr;
    Itcl_CallFrame frame;

    if (objc != 3) {
        Tcl_WrongNumArgs(interp, 1, objv, "name { definition }");
        return TCL_ERROR;
    }
    className = Tcl_GetStringFromObj(objv[1], &len);
    if (len == 0) {
        Tcl_AppendResult(interp, "invalid class name \"\"", (char *) NULL);
        return TCL_ERROR;
    }

    /*
     *  Find the namespace to use as a parser for the class definition.
     *  If for some reason it is destroyed, bail out here.
     */
    parserNs = Tcl_FindNamespace(interp, "::itcl::parser",
        (Tcl_Namespace*)NULL, TCL_LEAVE_ERR_MSG);

    if (parserNs == NULL) {
        char msg[256];
        sprintf(msg, "\n    (while parsing class definition for \"%.100s\")",
            className);
        Tcl_AddErrorInfo(interp, msg);
        return TCL_ERROR;
    }

    /*
     *  Try to create the specified class and its namespace.
     */
    if (Itcl_CreateClass(interp, className, info, &cdefnPtr) != TCL_OK) {
        return TCL_ERROR;
    }

    /*
     *  Import the built-in commands from the itcl::builtin namespace.
     *  Do this before parsing the class definition, so methods/procs
     *  can override the built-in commands.
     */
    result = Tcl_Import(interp, cdefnPtr->namesp, "::itcl::builtin::*",
        /* allowOverwrite */ 1);

    if (result != TCL_OK) {
        char msg[256];
        sprintf(msg, "\n    (while installing built-in commands for class \"%.100s\")", className);
        Tcl_AddErrorInfo(interp, msg);

        Tcl_DeleteNamespace(cdefnPtr->namesp);
        return TCL_ERROR;
    }

    /*
     *  Push this class onto the class definition stack so that it
     *  becomes the current context for all commands in the parser.
     *  Activate the parser and evaluate the class definition.
     */
    Itcl_PushStack((ClientData)cdefnPtr, &info->cdefnStack);

    result = Tcl_PushCallFrame(interp, (Tcl_CallFrame *) &frame, parserNs,
        /* isProcCallFrame */ 0);

    if (result == TCL_OK) {
        result = Tcl_EvalObj(interp, objv[2]);
        Tcl_PopCallFrame(interp);
    }
    Itcl_PopStack(&info->cdefnStack);

    if (result != TCL_OK) {
        char msg[256];
        sprintf(msg, "\n    (class \"%.200s\" body line %d)",
            className, interp->errorLine);
        Tcl_AddErrorInfo(interp, msg);

        Tcl_DeleteNamespace(cdefnPtr->namesp);
        return TCL_ERROR;
    }

    /*
     *  At this point, parsing of the class definition has succeeded.
     *  Add built-in methods such as "configure" and "cget"--as long
     *  as they don't conflict with those defined in the class.
     */
    if (Itcl_InstallBiMethods(interp, cdefnPtr) != TCL_OK) {
        Tcl_DeleteNamespace(cdefnPtr->namesp);
        return TCL_ERROR;
    }

    /*
     *  Build the name resolution tables for all data members.
     */
    Itcl_BuildVirtualTables(cdefnPtr);

    Tcl_ResetResult(interp);
    return TCL_OK;
}


/*
 * ------------------------------------------------------------------------
 *  Itcl_ClassInheritCmd()
 *
 *  Invoked by Tcl during the parsing of a class definition whenever
 *  the "inherit" command is invoked to define one or more base classes.
 *  Handles the following syntax:
 *
 *      inherit <baseclass> ?<baseclass>...?
 *
 * ------------------------------------------------------------------------
 */
int
Itcl_ClassInheritCmd(clientData, interp, objc, objv)
    ClientData clientData;   /* info for all known objects */
    Tcl_Interp *interp;      /* current interpreter */
    int objc;                /* number of arguments */
    Tcl_Obj *CONST objv[];   /* argument objects */
{
    ItclObjectInfo *info = (ItclObjectInfo*)clientData;
    ItclClass *cdefnPtr = (ItclClass*)Itcl_PeekStack(&info->cdefnStack);

    int result, i, newEntry = 1;
    char *token;
    Itcl_ListElem *elem, *elem2;
    ItclClass *cdPtr, *baseCdefnPtr, *badCdPtr;
    ItclHierIter hier;
    Itcl_Stack stack;
    Itcl_CallFrame frame;

    if (objc < 2) {
        Tcl_WrongNumArgs(interp, 1, objv, "class ?class...?");
        return TCL_ERROR;
    }

    /*
     *  In "inherit" statement can only be included once in a
     *  class definition.
     */
    elem = Itcl_FirstListElem(&cdefnPtr->bases);
    if (elem != NULL) {
        Tcl_AppendToObj(Tcl_GetObjResult(interp), "inheritance \"", -1);

        while (elem) {
            cdPtr = (ItclClass*)Itcl_GetListValue(elem);
            Tcl_AppendResult(interp,
                cdPtr->name, " ", (char*)NULL);

            elem = Itcl_NextListElem(elem);
        }

        Tcl_AppendResult(interp,
            "\" already defined for class \"", cdefnPtr->fullname, "\"",
            (char*)NULL);
        return TCL_ERROR;
    }

    /*
     *  Validate each base class and add it to the "bases" list.
     */
    result = Tcl_PushCallFrame(interp, (Tcl_CallFrame *) &frame,
	    cdefnPtr->namesp->parentPtr, /* isProcCallFrame */ 0);

    if (result != TCL_OK) {
        return TCL_ERROR;
    }

    for (objc--,objv++; objc > 0; objc--,objv++) {

        /*
         *  Make sure that the base class name is known in the
         *  parent namespace (currently active).  If not, try
         *  to autoload its definition.
         */
        token = Tcl_GetString(*objv);
        baseCdefnPtr = Itcl_FindClass(interp, token, /* autoload */ 1);
        if (!baseCdefnPtr) {
            Tcl_Obj *resultPtr = Tcl_GetObjResult(interp);
            int errlen;
            char *errmsg;

            Tcl_IncrRefCount(resultPtr);
            errmsg = Tcl_GetStringFromObj(resultPtr, &errlen);

            Tcl_ResetResult(interp);
            Tcl_AppendResult(interp,
                "cannot inherit from \"", token, "\"",
                (char*)NULL);

            if (errlen > 0) {
                Tcl_AppendResult(interp,
                    " (", errmsg, ")", (char*)NULL);
            }
            Tcl_DecrRefCount(resultPtr);
            goto inheritError;
        }

        /*
         *  Make sure that the base class is not the same as the
         *  class that is being built.
         */
        if (baseCdefnPtr == cdefnPtr) {
            Tcl_AppendResult(interp,
                "class \"", cdefnPtr->name, "\" cannot inherit from itself",
                (char*)NULL);
            goto inheritError;
        }

        Itcl_AppendList(&cdefnPtr->bases, (ClientData)baseCdefnPtr);
        Itcl_PreserveData((ClientData)baseCdefnPtr);
    }

    /*
     *  Scan through the inheritance list to make sure that no
     *  class appears twice.
     */
    elem = Itcl_FirstListElem(&cdefnPtr->bases);
    while (elem) {
        elem2 = Itcl_NextListElem(elem);
        while (elem2) {
            if (Itcl_GetListValue(elem) == Itcl_GetListValue(elem2)) {
                cdPtr = (ItclClass*)Itcl_GetListValue(elem);
                Tcl_AppendResult(interp,
                    "class \"", cdefnPtr->fullname,
                    "\" cannot inherit base class \"",
                    cdPtr->fullname, "\" more than once",
                    (char*)NULL);
                goto inheritError;
            }
            elem2 = Itcl_NextListElem(elem2);
        }
        elem = Itcl_NextListElem(elem);
    }

    /*
     *  Add each base class and all of its base classes into
     *  the heritage for the current class.  Along the way, make
     *  sure that no class appears twice in the heritage.
     */
    Itcl_InitHierIter(&hier, cdefnPtr);
    cdPtr = Itcl_AdvanceHierIter(&hier);  /* skip the class itself */
    cdPtr = Itcl_AdvanceHierIter(&hier);
    while (cdPtr != NULL) {
        (void) Tcl_CreateHashEntry(&cdefnPtr->heritage,
            (char*)cdPtr, &newEntry);

        if (!newEntry) {
            break;
        }
        cdPtr = Itcl_AdvanceHierIter(&hier);
    }
    Itcl_DeleteHierIter(&hier);

    /*
     *  Same base class found twice in the hierarchy?
     *  Then flag error.  Show the list of multiple paths
     *  leading to the same base class.
     */
    if (!newEntry) {
        badCdPtr = cdPtr;
        Tcl_AppendResult(interp,
            "class \"", cdefnPtr->fullname, "\" inherits base class \"",
            badCdPtr->fullname, "\" more than once:",
            (char*)NULL);

        cdPtr = cdefnPtr;
        Itcl_InitStack(&stack);
        Itcl_PushStack((ClientData)cdPtr, &stack);

        /*
         *  Show paths leading to bad base class
         */
        while (Itcl_GetStackSize(&stack) > 0) {
            cdPtr = (ItclClass*)Itcl_PopStack(&stack);

            if (cdPtr == badCdPtr) {
                Tcl_AppendResult(interp, "\n  ", (char *) NULL);
                for (i=0; i < Itcl_GetStackSize(&stack); i++) {
                    if (Itcl_GetStackValue(&stack, i) == NULL) {
                        cdPtr = (ItclClass*)Itcl_GetStackValue(&stack, i-1);
                        Tcl_AppendResult(interp, cdPtr->name, "->",
				(char*)NULL);
                    }
                }
                Tcl_AppendResult(interp, badCdPtr->name, (char *) NULL);
            }
            else if (!cdPtr) {
                (void)Itcl_PopStack(&stack);
            }
            else {
                elem = Itcl_LastListElem(&cdPtr->bases);
                if (elem) {
                    Itcl_PushStack((ClientData)cdPtr, &stack);
                    Itcl_PushStack((ClientData)NULL, &stack);
                    while (elem) {
                        Itcl_PushStack(Itcl_GetListValue(elem), &stack);
                        elem = Itcl_PrevListElem(elem);
                    }
                }
            }
        }
        Itcl_DeleteStack(&stack);
        goto inheritError;
    }

    /*
     *  At this point, everything looks good.
     *  Finish the installation of the base classes.  Update
     *  each base class to recognize the current class as a
     *  derived class.
     */
    elem = Itcl_FirstListElem(&cdefnPtr->bases);
    while (elem) {
        baseCdefnPtr = (ItclClass*)Itcl_GetListValue(elem);

        Itcl_AppendList(&baseCdefnPtr->derived, (ClientData)cdefnPtr);
        Itcl_PreserveData((ClientData)cdefnPtr);

        elem = Itcl_NextListElem(elem);
    }

    Tcl_PopCallFrame(interp);
    return TCL_OK;


    /*
     *  If the "inherit" list cannot be built properly, tear it
     *  down and return an error.
     */
inheritError:
    Tcl_PopCallFrame(interp);

    elem = Itcl_FirstListElem(&cdefnPtr->bases);
    while (elem) {
        Itcl_ReleaseData( Itcl_GetListValue(elem) );
        elem = Itcl_DeleteListElem(elem);
    }
    return TCL_ERROR;
}


/*
 * ------------------------------------------------------------------------
 *  Itcl_ClassProtectionCmd()
 *
 *  Invoked by Tcl whenever the user issues a protection setting
 *  command like "public" or "private".  Creates commands and
 *  variables, and assigns a protection level to them.  Protection
 *  levels are defined as follows:
 *
 *    public    => accessible from any namespace
 *    protected => accessible from selected namespaces
 *    private   => accessible only in the namespace where it was defined
 *
 *  Handles the following syntax:
 *
 *    public <command> ?<arg> <arg>...?
 *
 *  Returns TCL_OK/TCL_ERROR to indicate success/failure.
 * ------------------------------------------------------------------------
 */
int
Itcl_ClassProtectionCmd(clientData, interp, objc, objv)
    ClientData clientData;   /* protection level (public/protected/private) */
    Tcl_Interp *interp;      /* current interpreter */
    int objc;                /* number of arguments */
    Tcl_Obj *CONST objv[];   /* argument objects */
{
    ProtectionCmdInfo *pInfo = (ProtectionCmdInfo*)clientData;

    int result;
    int oldLevel;

    if (objc < 2) {
        Tcl_WrongNumArgs(interp, 1, objv, "command ?arg arg...?");
        return TCL_ERROR;
    }

    oldLevel = Itcl_Protection(interp, pInfo->pLevel);

    if (objc == 2) {
        result = Tcl_EvalObj(interp, objv[1]);
    } else {
        result = Itcl_EvalArgs(interp, objc-1, objv+1);
    }

    if (result == TCL_BREAK) {
        Tcl_SetResult(interp, "invoked \"break\" outside of a loop",
            TCL_STATIC);
        result = TCL_ERROR;
    }
    else if (result == TCL_CONTINUE) {
        Tcl_SetResult(interp, "invoked \"continue\" outside of a loop",
            TCL_STATIC);
        result = TCL_ERROR;
    }
    else if (result != TCL_OK) {
        char mesg[256], *token;
        token = Tcl_GetStringFromObj(objv[0], (int*)NULL);
        sprintf(mesg, "\n    (%.100s body line %d)", token, interp->errorLine);
        Tcl_AddErrorInfo(interp, mesg);
    }

    Itcl_Protection(interp, oldLevel);
    return result;
}


/*
 * ------------------------------------------------------------------------
 *  Itcl_ClassConstructorCmd()
 *
 *  Invoked by Tcl during the parsing of a class definition whenever
 *  the "constructor" command is invoked to define the constructor
 *  for an object.  Handles the following syntax:
 *
 *      constructor <arglist> ?<init>? <body>
 *
 * ------------------------------------------------------------------------
 */
int
Itcl_ClassConstructorCmd(clientData, interp, objc, objv)
    ClientData clientData;   /* info for all known objects */
    Tcl_Interp *interp;      /* current interpreter */
    int objc;                /* number of arguments */
    Tcl_Obj *CONST objv[];   /* argument objects */
{
    ItclObjectInfo *info = (ItclObjectInfo*)clientData;
    ItclClass *cdefnPtr = (ItclClass*)Itcl_PeekStack(&info->cdefnStack);

    char *name, *arglist, *body;

    if (objc < 3 || objc > 4) {
        Tcl_WrongNumArgs(interp, 1, objv, "args ?init? body");
        return TCL_ERROR;
    }

    name = Tcl_GetStringFromObj(objv[0], (int*)NULL);
    if (Tcl_FindHashEntry(&cdefnPtr->functions, name)) {
        Tcl_AppendResult(interp,
            "\"", name, "\" already defined in class \"",
            cdefnPtr->fullname, "\"",
            (char*)NULL);
        return TCL_ERROR;
    }

    /*
     *  If there is an object initialization statement, pick this
     *  out and take the last argument as the constructor body.
     */
    arglist = Tcl_GetString(objv[1]);
    if (objc == 3) {
        body = Tcl_GetString(objv[2]);
    } else {
        cdefnPtr->initCode = objv[2];
        Tcl_IncrRefCount(cdefnPtr->initCode);
        body = Tcl_GetString(objv[3]);
    }

    if (Itcl_CreateMethod(interp, cdefnPtr, name, arglist, body) != TCL_OK) {
        return TCL_ERROR;
    }
    return TCL_OK;
}


/*
 * ------------------------------------------------------------------------
 *  Itcl_ClassDestructorCmd()
 *
 *  Invoked by Tcl during the parsing of a class definition whenever
 *  the "destructor" command is invoked to define the destructor
 *  for an object.  Handles the following syntax:
 *
 *      destructor <body>
 *
 * ------------------------------------------------------------------------
 */
int
Itcl_ClassDestructorCmd(clientData, interp, objc, objv)
    ClientData clientData;   /* info for all known objects */
    Tcl_Interp *interp;      /* current interpreter */
    int objc;                /* number of arguments */
    Tcl_Obj *CONST objv[];   /* argument objects */
{
    ItclObjectInfo *info = (ItclObjectInfo*)clientData;
    ItclClass *cdefnPtr = (ItclClass*)Itcl_PeekStack(&info->cdefnStack);

    char *name, *body;

    if (objc != 2) {
        Tcl_WrongNumArgs(interp, 1, objv, "body");
        return TCL_ERROR;
    }

    name = Tcl_GetStringFromObj(objv[0], (int*)NULL);
    body = Tcl_GetStringFromObj(objv[1], (int*)NULL);

    if (Tcl_FindHashEntry(&cdefnPtr->functions, name)) {
        Tcl_AppendResult(interp,
            "\"", name, "\" already defined in class \"",
            cdefnPtr->fullname, "\"",
            (char*)NULL);
        return TCL_ERROR;
    }

    if (Itcl_CreateMethod(interp, cdefnPtr, name, (char*)NULL, body)
        != TCL_OK) {
        return TCL_ERROR;
    }
    return TCL_OK;
}

/*
 * ------------------------------------------------------------------------
 *  Itcl_ClassMethodCmd()
 *
 *  Invoked by Tcl during the parsing of a class definition whenever
 *  the "method" command is invoked to define an object method.
 *  Handles the following syntax:
 *
 *      method <name> ?<arglist>? ?<body>?
 *
 * ------------------------------------------------------------------------
 */
int
Itcl_ClassMethodCmd(clientData, interp, objc, objv)
    ClientData clientData;   /* info for all known objects */
    Tcl_Interp *interp;      /* current interpreter */
    int objc;                /* number of arguments */
    Tcl_Obj *CONST objv[];   /* argument objects */
{
    ItclObjectInfo *info = (ItclObjectInfo*)clientData;
    ItclClass *cdefnPtr = (ItclClass*)Itcl_PeekStack(&info->cdefnStack);

    char *name, *arglist, *body;

    if (objc < 2 || objc > 4) {
        Tcl_WrongNumArgs(interp, 1, objv, "name ?args? ?body?");
        return TCL_ERROR;
    }

    name = Tcl_GetStringFromObj(objv[1], (int*)NULL);

    arglist = NULL;
    body = NULL;
    if (objc >= 3) {
        arglist = Tcl_GetStringFromObj(objv[2], (int*)NULL);
    }
    if (objc >= 4) {
        body = Tcl_GetStringFromObj(objv[3], (int*)NULL);
    }

    if (Itcl_CreateMethod(interp, cdefnPtr, name, arglist, body) != TCL_OK) {
        return TCL_ERROR;
    }
    return TCL_OK;
}


/*
 * ------------------------------------------------------------------------
 *  Itcl_ClassProcCmd()
 *
 *  Invoked by Tcl during the parsing of a class definition whenever
 *  the "proc" command is invoked to define a common class proc.
 *  A "proc" is like a "method", but only has access to "common"
 *  class variables.  Handles the following syntax:
 *
 *      proc <name> ?<arglist>? ?<body>?
 *
 * ------------------------------------------------------------------------
 */
int
Itcl_ClassProcCmd(clientData, interp, objc, objv)
    ClientData clientData;   /* info for all known objects */
    Tcl_Interp *interp;      /* current interpreter */
    int objc;                /* number of arguments */
    Tcl_Obj *CONST objv[];   /* argument objects */
{
    ItclObjectInfo *info = (ItclObjectInfo*)clientData;
    ItclClass *cdefnPtr = (ItclClass*)Itcl_PeekStack(&info->cdefnStack);
    char *name, *arglist, *body;

    if (objc < 2 || objc > 4) {
        Tcl_WrongNumArgs(interp, 1, objv, "name ?args? ?body?");
        return TCL_ERROR;
    }

    name = Tcl_GetStringFromObj(objv[1], (int*)NULL);

    arglist = NULL;
    body = NULL;
    if (objc >= 3) {
        arglist = Tcl_GetStringFromObj(objv[2], (int*)NULL);
    }
    if (objc >= 4) {
        body = Tcl_GetStringFromObj(objv[3], (int*)NULL);
    }

    if (Itcl_CreateProc(interp, cdefnPtr, name, arglist, body) != TCL_OK) {
        return TCL_ERROR;
    }
    return TCL_OK;
}


/*
 * ------------------------------------------------------------------------
 *  Itcl_ClassVariableCmd()
 *
 *  Invoked by Tcl during the parsing of a class definition whenever
 *  the "variable" command is invoked to define an instance variable.
 *  Handles the following syntax:
 *
 *      variable <varname> ?<init>? ?<config>?
 *
 * ------------------------------------------------------------------------
 */
int
Itcl_ClassVariableCmd(clientData, interp, objc, objv)
    ClientData clientData;   /* info for all known objects */
    Tcl_Interp *interp;      /* current interpreter */
    int objc;                /* number of arguments */
    Tcl_Obj *CONST objv[];   /* argument objects */
{
    ItclObjectInfo *info = (ItclObjectInfo*)clientData;
    ItclClass *cdefnPtr = (ItclClass*)Itcl_PeekStack(&info->cdefnStack);

    int pLevel;
    ItclVarDefn *vdefn;
    char *name, *init, *config;

    pLevel = Itcl_Protection(interp, 0);

    if (pLevel == ITCL_PUBLIC) {
        if (objc < 2 || objc > 4) {
            Tcl_WrongNumArgs(interp, 1, objv, "name ?init? ?config?");
            return TCL_ERROR;
        }
    }
    else if ((objc < 2) || (objc > 3)) {
        Tcl_WrongNumArgs(interp, 1, objv, "name ?init?");
        return TCL_ERROR;
    }

    /*
     *  Make sure that the variable name does not contain anything
     *  goofy like a "::" scope qualifier.
     */
    name = Tcl_GetStringFromObj(objv[1], (int*)NULL);
    if (strstr(name, "::")) {
        Tcl_AppendResult(interp,
            "bad variable name \"", name, "\"",
            (char*)NULL);
        return TCL_ERROR;
    }

    init   = NULL;
    config = NULL;
    if (objc >= 3) {
        init = Tcl_GetStringFromObj(objv[2], (int*)NULL);
    }
    if (objc >= 4) {
        config = Tcl_GetStringFromObj(objv[3], (int*)NULL);
    }

    if (Itcl_CreateVarDefn(interp, cdefnPtr, name, init, config,
        &vdefn) != TCL_OK) {

        return TCL_ERROR;
    }

    return TCL_OK;
}


/*
 * ------------------------------------------------------------------------
 *  Itcl_ClassCommonCmd()
 *
 *  Invoked by Tcl during the parsing of a class definition whenever
 *  the "common" command is invoked to define a variable that is
 *  common to all objects in the class.  Handles the following syntax:
 *
 *      common <varname> ?<init>?
 *
 * ------------------------------------------------------------------------
 */
int
Itcl_ClassCommonCmd(clientData, interp, objc, objv)
    ClientData clientData;   /* info for all known objects */
    Tcl_Interp *interp;      /* current interpreter */
    int objc;                /* number of arguments */
    Tcl_Obj *CONST objv[];   /* argument objects */
{
    ItclObjectInfo *info = (ItclObjectInfo*)clientData;
    ItclClass *cdefnPtr = (ItclClass*)Itcl_PeekStack(&info->cdefnStack);

    int newEntry;
    char *name, *init;
    ItclVarDefn *vdefn;
    Namespace *nsPtr;
    Var *varPtr;

    if ((objc < 2) || (objc > 3)) {
        Tcl_WrongNumArgs(interp, 1, objv, "varname ?init?");
        return TCL_ERROR;
    }

    /*
     *  Make sure that the variable name does not contain anything
     *  goofy like a "::" scope qualifier.
     */
    name = Tcl_GetStringFromObj(objv[1], (int*)NULL);
    if (strstr(name, "::")) {
        Tcl_AppendResult(interp,
            "bad variable name \"", name, "\"",
            (char*)NULL);
        return TCL_ERROR;
    }

    init = NULL;
    if (objc >= 3) {
        init = Tcl_GetStringFromObj(objv[2], (int*)NULL);
    }

    if (Itcl_CreateVarDefn(interp, cdefnPtr, name, init, (char*)NULL,
        &vdefn) != TCL_OK) {

        return TCL_ERROR;
    }
    vdefn->member->flags |= ITCL_COMMON;

    /*
     *  Create the variable in the namespace associated with the
     *  class.  Do this the hard way, to avoid the variable resolver
     *  procedures.  These procedures won't work until we rebuild
     *  the virtual tables below.
     */
    nsPtr = (Namespace*)cdefnPtr->namesp;
    varPtr = ItclVarHashCreateVar(&nsPtr->varTable,
        vdefn->member->name, &newEntry);

#if ITCL_TCL_PRE_8_5
    if (newEntry && itclOldRuntime) {
	varPtr->nsPtr = nsPtr;
    }
#endif
    TclSetVarNamespaceVar(varPtr);
    ItclVarRefCount(varPtr)++;    /* another use by class */


    /*
     *  TRICKY NOTE:  Make sure to rebuild the virtual tables for this
     *    class so that this variable is ready to access.  The variable
     *    resolver for the parser namespace needs this info to find the
     *    variable if the developer tries to set it within the class
     *    definition.
     *
     *  If an initialization value was specified, then initialize
     *  the variable now.
     */
    Itcl_BuildVirtualTables(cdefnPtr);

    if (init) {
        CONST char *val = Tcl_SetVar(interp, vdefn->member->name, init,
            TCL_NAMESPACE_ONLY);

        if (!val) {
            Tcl_AppendResult(interp,
                "cannot initialize common variable \"",
                vdefn->member->name, "\"",
                (char*)NULL);
            return TCL_ERROR;
        }
    }
    return TCL_OK;
}


/*
 * ------------------------------------------------------------------------
 *  Itcl_ParseVarResolver()
 *
 *  Used by the "parser" namespace to resolve variable accesses to
 *  common variables.  The runtime resolver procedure is consulted
 *  whenever a variable is accessed within the namespace.  It can
 *  deny access to certain variables, or perform special lookups itself.
 *
 *  This procedure allows access only to "common" class variables that
 *  have been declared within the class or inherited from another class.
 *  A "set" command can be used to initialized common data members within
 *  the body of the class definition itself:
 *
 *    itcl::class Foo {
 *        common colors
 *        set colors(red)   #ff0000
 *        set colors(green) #00ff00
 *        set colors(blue)  #0000ff
 *        ...
 *    }
 *
 *    itcl::class Bar {
 *        inherit Foo
 *        set colors(gray)  #a0a0a0
 *        set colors(white) #ffffff
 *
 *        common numbers
 *        set numbers(0) zero
 *        set numbers(1) one
 *    }
 *
 * ------------------------------------------------------------------------
 */
/* ARGSUSED */
int
Itcl_ParseVarResolver(interp, name, contextNs, flags, rPtr)
    Tcl_Interp *interp;        /* current interpreter */
    CONST char* name;                /* name of the variable being accessed */
    Tcl_Namespace *contextNs;  /* namespace context */
    int flags;                 /* TCL_GLOBAL_ONLY => global variable
                                * TCL_NAMESPACE_ONLY => namespace variable */
    Tcl_Var* rPtr;             /* returns: Tcl_Var for desired variable */
{
    ItclObjectInfo *info = (ItclObjectInfo*)contextNs->clientData;
    ItclClass *cdefnPtr = (ItclClass*)Itcl_PeekStack(&info->cdefnStack);

    Tcl_HashEntry *entry;
    ItclVarLookup *vlookup;

    /*
     *  See if the requested variable is a recognized "common" member.
     *  If it is, make sure that access is allowed.
     */
    entry = Tcl_FindHashEntry(&cdefnPtr->resolveVars, name);
    if (entry) {
        vlookup = (ItclVarLookup*)Tcl_GetHashValue(entry);

        if ((vlookup->vdefn->member->flags & ITCL_COMMON) != 0) {
            if (!vlookup->accessible) {
                Tcl_AppendResult(interp,
                    "can't access \"", name, "\": ",
                    Itcl_ProtectionStr(vlookup->vdefn->member->protection),
                    " variable",
                    (char*)NULL);
                return TCL_ERROR;
            }
            *rPtr = vlookup->var.common;
            return TCL_OK;
        }
    }

    /*
     *  If the variable is not recognized, return TCL_CONTINUE and
     *  let lookup continue via the normal name resolution rules.
     *  This is important for variables like "errorInfo"
     *  that might get set while the parser namespace is active.
     */
    return TCL_CONTINUE;
}



/*
 * ------------------------------------------------------------------------
 *  ItclFreeParserCommandData()
 *
 *  This callback will free() up memory dynamically allocated
 *  and passed as the ClientData argument to Tcl_CreateObjCommand.
 *  This callback is required because one can not simply pass
 *  a pointer to the free() or ckfree() to Tcl_CreateObjCommand.
 * ------------------------------------------------------------------------
 */
static void
ItclFreeParserCommandData(cdata)
    char* cdata;  /* client data to be destroyed */
{
    ckfree(cdata);
}
