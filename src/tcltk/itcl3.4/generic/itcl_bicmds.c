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
 *  These procedures handle built-in class methods, including the
 *  "isa" method (to query hierarchy info) and the "info" method
 *  (to query class/object data).
 *
 * ========================================================================
 *  AUTHOR:  Michael J. McLennan
 *           Bell Labs Innovations for Lucent Technologies
 *           mmclennan@lucent.com
 *           http://www.tcltk.com/itcl
 *
 *     RCS:  $Id: itcl_bicmds.c,v 1.11 2007/05/24 22:12:55 hobbs Exp $
 * ========================================================================
 *           Copyright (c) 1993-1998  Lucent Technologies, Inc.
 * ------------------------------------------------------------------------
 * See the file "license.terms" for information on usage and redistribution
 * of this file, and for a DISCLAIMER OF ALL WARRANTIES.
 */
#include "itclInt.h"

/*
 *  Standard list of built-in methods for all objects.
 */
typedef struct BiMethod {
    char* name;              /* method name */
    char* usage;             /* string describing usage */
    char* registration;      /* registration name for C proc */
    Tcl_ObjCmdProc *proc;    /* implementation C proc */
} BiMethod;

static BiMethod BiMethodList[] = {
    { "cget",      "-option",
                   "@itcl-builtin-cget",  Itcl_BiCgetCmd },
    { "configure", "?-option? ?value -option value...?",
                   "@itcl-builtin-configure",  Itcl_BiConfigureCmd },
    { "isa",       "className",
                   "@itcl-builtin-isa",  Itcl_BiIsaCmd },
};
static int BiMethodListLen = sizeof(BiMethodList)/sizeof(BiMethod);


/*
 *  FORWARD DECLARATIONS
 */
static Tcl_Obj* ItclReportPublicOpt _ANSI_ARGS_((Tcl_Interp *interp,
    ItclVarDefn *vdefn, ItclObject *contextObj));


/*
 * ------------------------------------------------------------------------
 *  Itcl_BiInit()
 *
 *  Creates a namespace full of built-in methods/procs for [incr Tcl]
 *  classes.  This includes things like the "isa" method and "info"
 *  for querying class info.  Usually invoked by Itcl_Init() when
 *  [incr Tcl] is first installed into an interpreter.
 *
 *  Returns TCL_OK/TCL_ERROR to indicate success/failure.
 * ------------------------------------------------------------------------
 */
int
Itcl_BiInit(interp)
    Tcl_Interp *interp;      /* current interpreter */
{
    int i;
    Tcl_Namespace *itclBiNs;

    /*
     *  Declare all of the built-in methods as C procedures.
     */
    for (i=0; i < BiMethodListLen; i++) {
        if (Itcl_RegisterObjC(interp,
                BiMethodList[i].registration+1, BiMethodList[i].proc,
                (ClientData)NULL, (Tcl_CmdDeleteProc*)NULL) != TCL_OK) {

            return TCL_ERROR;
        }
    }

    /*
     *  Create the "::itcl::builtin" namespace for built-in class
     *  commands.  These commands are imported into each class
     *  just before the class definition is parsed.
     */
    Tcl_CreateObjCommand(interp, "::itcl::builtin::chain", Itcl_BiChainCmd,
        (ClientData)NULL, (Tcl_CmdDeleteProc*)NULL);

    if (Itcl_CreateEnsemble(interp, "::itcl::builtin::info") != TCL_OK) {
        return TCL_ERROR;
    }

    if (Itcl_AddEnsemblePart(interp, "::itcl::builtin::info",
            "class", "",
            Itcl_BiInfoClassCmd, (ClientData)NULL, (Tcl_CmdDeleteProc*)NULL)
            != TCL_OK ||
        Itcl_AddEnsemblePart(interp, "::itcl::builtin::info",
            "inherit", "",
            Itcl_BiInfoInheritCmd, (ClientData)NULL, (Tcl_CmdDeleteProc*)NULL)
            != TCL_OK ||
        Itcl_AddEnsemblePart(interp, "::itcl::builtin::info",
            "heritage", "",
            Itcl_BiInfoHeritageCmd, (ClientData)NULL, (Tcl_CmdDeleteProc*)NULL)
            != TCL_OK ||
        Itcl_AddEnsemblePart(interp, "::itcl::builtin::info",
            "function", "?name? ?-protection? ?-type? ?-name? ?-args? ?-body?",
            Itcl_BiInfoFunctionCmd, (ClientData)NULL, (Tcl_CmdDeleteProc*)NULL)
            != TCL_OK ||
        Itcl_AddEnsemblePart(interp, "::itcl::builtin::info",
            "variable", "?name? ?-protection? ?-type? ?-name? ?-init? ?-value? ?-config?",
            Itcl_BiInfoVariableCmd, (ClientData)NULL, (Tcl_CmdDeleteProc*)NULL)
            != TCL_OK ||
        Itcl_AddEnsemblePart(interp, "::itcl::builtin::info",
            "args", "procname",
            Itcl_BiInfoArgsCmd, (ClientData)NULL, (Tcl_CmdDeleteProc*)NULL)
            != TCL_OK ||
        Itcl_AddEnsemblePart(interp, "::itcl::builtin::info",
            "body", "procname",
            Itcl_BiInfoBodyCmd, (ClientData)NULL, (Tcl_CmdDeleteProc*)NULL)
            != TCL_OK
    ) {
        return TCL_ERROR;
    }

    /*
     *  Add an error handler to support all of the usual inquiries
     *  for the "info" command in the global namespace.
     */
    if (Itcl_AddEnsemblePart(interp, "::itcl::builtin::info",
            "@error", "",
            Itcl_DefaultInfoCmd, (ClientData)NULL, (Tcl_CmdDeleteProc*)NULL)
            != TCL_OK
    ) {
        return TCL_ERROR;
    }

    /*
     *  Export all commands in the built-in namespace so we can
     *  import them later on.
     */
    itclBiNs = Tcl_FindNamespace(interp, "::itcl::builtin",
        (Tcl_Namespace*)NULL, TCL_LEAVE_ERR_MSG);

    if (!itclBiNs ||
        Tcl_Export(interp, itclBiNs, "*", /* resetListFirst */ 1) != TCL_OK) {
        return TCL_ERROR;
    }

    return TCL_OK;
}


/*
 * ------------------------------------------------------------------------
 *  Itcl_InstallBiMethods()
 *
 *  Invoked when a class is first created, just after the class
 *  definition has been parsed, to add definitions for built-in
 *  methods to the class.  If a method already exists in the class
 *  with the same name as the built-in, then the built-in is skipped.
 *  Otherwise, a method definition for the built-in method is added.
 *
 *  Returns TCL_OK if successful, or TCL_ERROR (along with an error
 *  message in the interpreter) if anything goes wrong.
 * ------------------------------------------------------------------------
 */
int
Itcl_InstallBiMethods(interp, cdefn)
    Tcl_Interp *interp;      /* current interpreter */
    ItclClass *cdefn;        /* class definition to be updated */
{
    int result = TCL_OK;
    Tcl_HashEntry *entry = NULL;

    int i;
    ItclHierIter hier;
    ItclClass *cdPtr;

    /*
     *  Scan through all of the built-in methods and see if
     *  that method already exists in the class.  If not, add
     *  it in.
     *
     *  TRICKY NOTE:  The virtual tables haven't been built yet,
     *    so look for existing methods the hard way--by scanning
     *    through all classes.
     */
    for (i=0; i < BiMethodListLen; i++) {
        Itcl_InitHierIter(&hier, cdefn);
        cdPtr = Itcl_AdvanceHierIter(&hier);
        while (cdPtr) {
            entry = Tcl_FindHashEntry(&cdPtr->functions, BiMethodList[i].name);
            if (entry) {
                break;
            }
            cdPtr = Itcl_AdvanceHierIter(&hier);
        }
        Itcl_DeleteHierIter(&hier);

        if (!entry) {
            result = Itcl_CreateMethod(interp, cdefn, BiMethodList[i].name,
                BiMethodList[i].usage, BiMethodList[i].registration);

            if (result != TCL_OK) {
                break;
            }
        }
    }
    return result;
}


/*
 * ------------------------------------------------------------------------
 *  Itcl_BiIsaCmd()
 *
 *  Invoked whenever the user issues the "isa" method for an object.
 *  Handles the following syntax:
 *
 *    <objName> isa <className>
 *
 *  Checks to see if the object has the given <className> anywhere
 *  in its heritage.  Returns 1 if so, and 0 otherwise.
 * ------------------------------------------------------------------------
 */
/* ARGSUSED */
int
Itcl_BiIsaCmd(clientData, interp, objc, objv)
    ClientData clientData;   /* class definition */
    Tcl_Interp *interp;      /* current interpreter */
    int objc;                /* number of arguments */
    Tcl_Obj *CONST objv[];   /* argument objects */
{
    ItclClass *contextClass, *cdefn;
    ItclObject *contextObj;
    char *token;

    /*
     *  Make sure that this command is being invoked in the proper
     *  context.
     */
    if (Itcl_GetContext(interp, &contextClass, &contextObj) != TCL_OK) {
        return TCL_ERROR;
    }

    if (!contextObj) {
        Tcl_AppendResult(interp,
            "improper usage: should be \"object isa className\"",
            (char*)NULL);
        return TCL_ERROR;
    }
    if (objc != 2) {
        token = Tcl_GetStringFromObj(objv[0], (int*)NULL);
        Tcl_AppendResult(interp,
            "wrong # args: should be \"object ", token, " className\"",
            (char*)NULL);
        return TCL_ERROR;
    }

    /*
     *  Look for the requested class.  If it is not found, then
     *  try to autoload it.  If it absolutely cannot be found,
     *  signal an error.
     */
    token = Tcl_GetStringFromObj(objv[1], (int*)NULL);
    cdefn = Itcl_FindClass(interp, token, /* autoload */ 1);
    if (cdefn == NULL) {
        return TCL_ERROR;
    }

    if (Itcl_ObjectIsa(contextObj, cdefn)) {
        Tcl_SetIntObj(Tcl_GetObjResult(interp), 1);
    } else {
        Tcl_SetIntObj(Tcl_GetObjResult(interp), 0);
    }
    return TCL_OK;
}


/*
 * ------------------------------------------------------------------------
 *  Itcl_BiConfigureCmd()
 *
 *  Invoked whenever the user issues the "configure" method for an object.
 *  Handles the following syntax:
 *
 *    <objName> configure ?-<option>? ?<value> -<option> <value>...?
 *
 *  Allows access to public variables as if they were configuration
 *  options.  With no arguments, this command returns the current
 *  list of public variable options.  If -<option> is specified,
 *  this returns the information for just one option:
 *
 *    -<optionName> <initVal> <currentVal>
 *
 *  Otherwise, the list of arguments is parsed, and values are
 *  assigned to the various public variable options.  When each
 *  option changes, a big of "config" code associated with the option
 *  is executed, to bring the object up to date.
 * ------------------------------------------------------------------------
 */
/* ARGSUSED */
int
Itcl_BiConfigureCmd(clientData, interp, objc, objv)
    ClientData clientData;   /* class definition */
    Tcl_Interp *interp;      /* current interpreter */
    int objc;                /* number of arguments */
    Tcl_Obj *CONST objv[];   /* argument objects */
{
    ItclClass *contextClass;
    ItclObject *contextObj;

    int i, result;
    CONST char *lastval;
    char *token;
    ItclClass *cdPtr;
    Tcl_HashSearch place;
    Tcl_HashEntry *entry;
    ItclVarDefn *vdefn;
    ItclVarLookup *vlookup;
    ItclMember *member;
    ItclMemberCode *mcode;
    ItclHierIter hier;
    Tcl_Obj *resultPtr, *objPtr;
    Tcl_DString buffer;
    ItclContext context;
    Itcl_CallFrame *oldFramePtr, *uplevelFramePtr;

    /*
     *  Make sure that this command is being invoked in the proper
     *  context.
     */
    if (Itcl_GetContext(interp, &contextClass, &contextObj) != TCL_OK) {
        return TCL_ERROR;
    }

    if (!contextObj) {
        Tcl_AppendResult(interp,
            "improper usage: should be ",
            "\"object configure ?-option? ?value -option value...?\"",
            (char*)NULL);
        return TCL_ERROR;
    }

    /*
     *  BE CAREFUL:  work in the virtual scope!
     */
    contextClass = contextObj->classDefn;

    /*
     *  HANDLE:  configure
     */
    if (objc == 1) {
        resultPtr = Tcl_NewListObj(0, (Tcl_Obj**)NULL);

        Itcl_InitHierIter(&hier, contextClass);
        while ((cdPtr=Itcl_AdvanceHierIter(&hier)) != NULL) {
            entry = Tcl_FirstHashEntry(&cdPtr->variables, &place);
            while (entry) {
                vdefn = (ItclVarDefn*)Tcl_GetHashValue(entry);
                if (vdefn->member->protection == ITCL_PUBLIC) {
                    objPtr = ItclReportPublicOpt(interp, vdefn, contextObj);

                    Tcl_ListObjAppendElement((Tcl_Interp*)NULL, resultPtr,
                        objPtr);
                }
                entry = Tcl_NextHashEntry(&place);
            }
        }
        Itcl_DeleteHierIter(&hier);

        Tcl_SetObjResult(interp, resultPtr);
        return TCL_OK;
    }

    /*
     *  HANDLE:  configure -option
     */
    else if (objc == 2) {
        token = Tcl_GetStringFromObj(objv[1], (int*)NULL);
        if (*token != '-') {
            Tcl_AppendResult(interp,
                "improper usage: should be ",
                "\"object configure ?-option? ?value -option value...?\"",
                (char*)NULL);
            return TCL_ERROR;
        }

        vlookup = NULL;
        entry = Tcl_FindHashEntry(&contextClass->resolveVars, token+1);
        if (entry) {
            vlookup = (ItclVarLookup*)Tcl_GetHashValue(entry);

            if (vlookup->vdefn->member->protection != ITCL_PUBLIC) {
                vlookup = NULL;
            }
        }

        if (!vlookup) {
            Tcl_AppendResult(interp,
                "unknown option \"", token, "\"",
                (char*)NULL);
            return TCL_ERROR;
        }

        resultPtr = ItclReportPublicOpt(interp, vlookup->vdefn, contextObj);
        Tcl_SetObjResult(interp, resultPtr);
        return TCL_OK;
    }

    /*
     *  HANDLE:  configure -option value -option value...
     *
     *  Be careful to work in the virtual scope.  If this "configure"
     *  method was defined in a base class, the current namespace
     *  (from Itcl_ExecMethod()) will be that base class.  Activate
     *  the derived class namespace here, so that instance variables
     *  are accessed properly.
     */
    result = TCL_OK;

    if (Itcl_PushContext(interp, (ItclMember*)NULL, contextObj->classDefn,
        contextObj, &context) != TCL_OK) {
        return TCL_ERROR;
    }
    Tcl_DStringInit(&buffer);

    for (i=1; i < objc; i+=2) {
        vlookup = NULL;
        token = Tcl_GetStringFromObj(objv[i], (int*)NULL);
        if (*token == '-') {
            entry = Tcl_FindHashEntry(&contextClass->resolveVars, token+1);
            if (entry) {
                vlookup = (ItclVarLookup*)Tcl_GetHashValue(entry);
            }
        }

        if (!vlookup || vlookup->vdefn->member->protection != ITCL_PUBLIC) {
            Tcl_AppendResult(interp,
                "unknown option \"", token, "\"",
                (char*)NULL);
            result = TCL_ERROR;
            goto configureDone;
        }
        if (i == objc-1) {
            Tcl_AppendResult(interp,
                "value for \"", token, "\" missing",
                (char*)NULL);
            result = TCL_ERROR;
            goto configureDone;
        }

        member = vlookup->vdefn->member;
        lastval = Tcl_GetVar2(interp, member->fullname, (char*)NULL, 0);
        Tcl_DStringSetLength(&buffer, 0);
        Tcl_DStringAppend(&buffer, (lastval) ? lastval : "", -1);

        token = Tcl_GetStringFromObj(objv[i+1], (int*)NULL);

        if (Tcl_SetVar2(interp, member->fullname, (char*)NULL, token,
            TCL_LEAVE_ERR_MSG) == NULL) {

            char msg[256];
            sprintf(msg, "\n    (error in configuration of public variable \"%.100s\")", member->fullname);
            Tcl_AddErrorInfo(interp, msg);
            result = TCL_ERROR;
            goto configureDone;
        }

        /*
         *  If this variable has some "config" code, invoke it now.
         *
         *  TRICKY NOTE:  Be careful to evaluate the code one level
         *    up in the call stack, so that it's executed in the
         *    calling context, and not in the context that we've
         *    set up for public variable access.
         */
        mcode = member->code;
        if (mcode && Itcl_IsMemberCodeImplemented(mcode)) {

            uplevelFramePtr = _Tcl_GetCallFrame(interp, 1);
            oldFramePtr = _Tcl_ActivateCallFrame(interp, uplevelFramePtr);

            result = Itcl_EvalMemberCode(interp, (ItclMemberFunc*)NULL,
                member, contextObj, 0, (Tcl_Obj**)NULL);

            (void) _Tcl_ActivateCallFrame(interp, oldFramePtr);

            if (result == TCL_OK) {
                Tcl_ResetResult(interp);
            } else {
                char msg[256];
                sprintf(msg, "\n    (error in configuration of public variable \"%.100s\")", member->fullname);
                Tcl_AddErrorInfo(interp, msg);

                Tcl_SetVar2(interp, member->fullname,(char*)NULL,
                    Tcl_DStringValue(&buffer), 0);

                goto configureDone;
            }
        }
    }

configureDone:
    Itcl_PopContext(interp, &context);
    Tcl_DStringFree(&buffer);

    return result;
}


/*
 * ------------------------------------------------------------------------
 *  Itcl_BiCgetCmd()
 *
 *  Invoked whenever the user issues the "cget" method for an object.
 *  Handles the following syntax:
 *
 *    <objName> cget -<option>
 *
 *  Allows access to public variables as if they were configuration
 *  options.  Mimics the behavior of the usual "cget" method for
 *  Tk widgets.  Returns the current value of the public variable
 *  with name <option>.
 * ------------------------------------------------------------------------
 */
/* ARGSUSED */
int
Itcl_BiCgetCmd(clientData, interp, objc, objv)
    ClientData clientData;   /* class definition */
    Tcl_Interp *interp;      /* current interpreter */
    int objc;                /* number of arguments */
    Tcl_Obj *CONST objv[];   /* argument objects */
{
    ItclClass *contextClass;
    ItclObject *contextObj;

    CONST char *name, *val;
    ItclVarLookup *vlookup;
    Tcl_HashEntry *entry;

    /*
     *  Make sure that this command is being invoked in the proper
     *  context.
     */
    if (Itcl_GetContext(interp, &contextClass, &contextObj) != TCL_OK) {
        return TCL_ERROR;
    }
    if (!contextObj || objc != 2) {
        Tcl_AppendResult(interp,
            "improper usage: should be \"object cget -option\"",
            (char*)NULL);
        return TCL_ERROR;
    }

    /*
     *  BE CAREFUL:  work in the virtual scope!
     */
    contextClass = contextObj->classDefn;

    name = Tcl_GetStringFromObj(objv[1], (int*)NULL);

    vlookup = NULL;
    entry = Tcl_FindHashEntry(&contextClass->resolveVars, name+1);
    if (entry) {
        vlookup = (ItclVarLookup*)Tcl_GetHashValue(entry);
    }

    if (!vlookup || vlookup->vdefn->member->protection != ITCL_PUBLIC) {
        Tcl_AppendResult(interp,
            "unknown option \"", name, "\"",
            (char*)NULL);
        return TCL_ERROR;
    }

    val = Itcl_GetInstanceVar(interp, vlookup->vdefn->member->fullname,
        contextObj, contextObj->classDefn);

    if (val) {
        Tcl_SetObjResult(interp, Tcl_NewStringObj(val, -1));
    } else {
        Tcl_SetObjResult(interp, Tcl_NewStringObj("<undefined>", -1));
    }
    return TCL_OK;
}


/*
 * ------------------------------------------------------------------------
 *  ItclReportPublicOpt()
 *
 *  Returns information about a public variable formatted as a
 *  configuration option:
 *
 *    -<varName> <initVal> <currentVal>
 *
 *  Used by Itcl_BiConfigureCmd() to report configuration options.
 *  Returns a Tcl_Obj containing the information.
 * ------------------------------------------------------------------------
 */
static Tcl_Obj*
ItclReportPublicOpt(interp, vdefn, contextObj)
    Tcl_Interp *interp;      /* interpreter containing the object */
    ItclVarDefn *vdefn;      /* public variable to be reported */
    ItclObject *contextObj;  /* object containing this variable */
{
    CONST char *val;
    ItclClass *cdefnPtr;
    Tcl_HashEntry *entry;
    ItclVarLookup *vlookup;
    Tcl_DString optName;
    Tcl_Obj *listPtr, *objPtr;

    listPtr = Tcl_NewListObj(0, (Tcl_Obj**)NULL);

    /*
     *  Determine how the option name should be reported.
     *  If the simple name can be used to find it in the virtual
     *  data table, then use the simple name.  Otherwise, this
     *  is a shadowed variable; use the full name.
     */
    Tcl_DStringInit(&optName);
    Tcl_DStringAppend(&optName, "-", -1);

    cdefnPtr = (ItclClass*)contextObj->classDefn;
    entry = Tcl_FindHashEntry(&cdefnPtr->resolveVars, vdefn->member->fullname);
    assert(entry != NULL);
    vlookup = (ItclVarLookup*)Tcl_GetHashValue(entry);
    Tcl_DStringAppend(&optName, vlookup->leastQualName, -1);

    objPtr = Tcl_NewStringObj(Tcl_DStringValue(&optName), -1);
    Tcl_ListObjAppendElement((Tcl_Interp*)NULL, listPtr, objPtr);
    Tcl_DStringFree(&optName);


    if (vdefn->init) {
        objPtr = Tcl_NewStringObj(vdefn->init, -1);
    } else {
        objPtr = Tcl_NewStringObj("<undefined>", -1);
    }
    Tcl_ListObjAppendElement((Tcl_Interp*)NULL, listPtr, objPtr);

    val = Itcl_GetInstanceVar(interp, vdefn->member->fullname, contextObj,
        contextObj->classDefn);

    if (val) {
        objPtr = Tcl_NewStringObj((CONST84 char *)val, -1);
    } else {
        objPtr = Tcl_NewStringObj("<undefined>", -1);
    }
    Tcl_ListObjAppendElement((Tcl_Interp*)NULL, listPtr, objPtr);

    return listPtr;
}


/*
 * ------------------------------------------------------------------------
 *  Itcl_BiChainCmd()
 *
 *  Invoked to handle the "chain" command, to access the version of
 *  a method or proc that exists in a base class.  Handles the
 *  following syntax:
 *
 *    chain ?<arg> <arg>...?
 *
 *  Looks up the inheritance hierarchy for another implementation
 *  of the method/proc that is currently executing.  If another
 *  implementation is found, it is invoked with the specified
 *  <arg> arguments.  If it is not found, this command does nothing.
 *  This allows a base class method to be called out in a generic way,
 *  so the code will not have to change if the base class changes.
 * ------------------------------------------------------------------------
 */
/* ARGSUSED */
int
Itcl_BiChainCmd(dummy, interp, objc, objv)
    ClientData dummy;        /* not used */
    Tcl_Interp *interp;      /* current interpreter */
    int objc;                /* number of arguments */
    Tcl_Obj *CONST objv[];   /* argument objects */
{
    int result = TCL_OK;

    ItclClass *contextClass;
    ItclObject *contextObj;

    char *cmd, *head;
    ItclClass *cdefn;
    ItclHierIter hier;
    Tcl_HashEntry *entry;
    ItclMemberFunc *mfunc;
    Tcl_DString buffer;
    ItclCallFrame *framePtr;
    Tcl_Obj *cmdlinePtr, **newobjv;

    /*
     *  If this command is not invoked within a class namespace,
     *  signal an error.
     */
    if (Itcl_GetContext(interp, &contextClass, &contextObj) != TCL_OK) {
        Tcl_ResetResult(interp);
        Tcl_AppendResult(interp,
            "cannot chain functions outside of a class context",
            (char*)NULL);
        return TCL_ERROR;
    }

    /*
     *  Try to get the command name from the current call frame.
     *  If it cannot be determined, do nothing.  Otherwise, trim
     *  off any leading path names.
     */
    framePtr = (ItclCallFrame*) _Tcl_GetCallFrame(interp, 0);
    if (!framePtr || !framePtr->objv) {
        return TCL_OK;
    }
    cmd = Tcl_GetStringFromObj(framePtr->objv[0], (int*)NULL);
    Itcl_ParseNamespPath(cmd, &buffer, &head, &cmd);

    /*
     *  Look for the specified command in one of the base classes.
     *  If we have an object context, then start from the most-specific
     *  class and walk up the hierarchy to the current context.  If
     *  there is multiple inheritance, having the entire inheritance
     *  hierarchy will allow us to jump over to another branch of
     *  the inheritance tree.
     *
     *  If there is no object context, just start with the current
     *  class context.
     */
    if (contextObj) {
        Itcl_InitHierIter(&hier, contextObj->classDefn);
        while ((cdefn=Itcl_AdvanceHierIter(&hier)) != NULL) {
            if (cdefn == contextClass) {
                break;
            }
        }
    }
    else {
        Itcl_InitHierIter(&hier, contextClass);
        Itcl_AdvanceHierIter(&hier);    /* skip the current class */
    }

    /*
     *  Now search up the class hierarchy for the next implementation.
     *  If found, execute it.  Otherwise, do nothing.
     */
    while ((cdefn=Itcl_AdvanceHierIter(&hier)) != NULL) {
        entry = Tcl_FindHashEntry(&cdefn->functions, cmd);
        if (entry) {
            mfunc = (ItclMemberFunc*)Tcl_GetHashValue(entry);

            /*
             *  NOTE:  Avoid the usual "virtual" behavior of
             *         methods by passing the full name as
             *         the command argument.
             */
            cmdlinePtr = Itcl_CreateArgs(interp, mfunc->member->fullname,
                objc-1, objv+1);

            (void) Tcl_ListObjGetElements((Tcl_Interp*)NULL, cmdlinePtr,
                &objc, &newobjv);

            result = Itcl_EvalArgs(interp, objc, newobjv);

            Tcl_DecrRefCount(cmdlinePtr);
            break;
        }
    }

    Tcl_DStringFree(&buffer);
    Itcl_DeleteHierIter(&hier);
    return result;
}


/*
 * ------------------------------------------------------------------------
 *  Itcl_BiInfoClassCmd()
 *
 *  Returns information regarding the class for an object.  This command
 *  can be invoked with or without an object context:
 *
 *    <objName> info class   <= returns most-specific class name
 *    info class             <= returns active namespace name
 *
 *  Returns a status TCL_OK/TCL_ERROR to indicate success/failure.
 * ------------------------------------------------------------------------
 */
/* ARGSUSED */
int
Itcl_BiInfoClassCmd(dummy, interp, objc, objv)
    ClientData dummy;     /* not used */
    Tcl_Interp *interp;   /* current interpreter */
    int objc;                /* number of arguments */
    Tcl_Obj *CONST objv[];   /* argument objects */
{
    Tcl_Namespace *activeNs = Tcl_GetCurrentNamespace(interp);
    Tcl_Namespace *contextNs = NULL;

    ItclClass *contextClass;
    ItclObject *contextObj;

    char *name;

    if (objc != 1) {
        Tcl_WrongNumArgs(interp, 1, objv, NULL);
        return TCL_ERROR;
    }

    /*
     *  If this command is not invoked within a class namespace,
     *  signal an error.
     */
    if (Itcl_GetContext(interp, &contextClass, &contextObj) != TCL_OK) {
	Tcl_Obj *msg = Tcl_NewStringObj("\nget info like this instead: " \
		"\n  namespace eval className { info ", -1);
	Tcl_AppendStringsToObj(msg, Tcl_GetString(objv[0]), "... }", NULL);
        Tcl_SetObjResult(interp, msg);
        return TCL_ERROR;
    }

    /*
     *  If there is an object context, then return the most-specific
     *  class for the object.  Otherwise, return the class namespace
     *  name.  Use normal class names when possible.
     */
    if (contextObj) {
        contextNs = contextObj->classDefn->namesp;
    } else {
      assert(contextClass != NULL);
      assert(contextClass->namesp != NULL);
      contextNs = contextClass->namesp;
    }

    if (!contextNs) {
        name = activeNs->fullName;
    } else if (contextNs->parentPtr == activeNs) {
        name = contextNs->name;
    } else {
        name = contextNs->fullName;
    }

    Tcl_SetObjResult(interp, Tcl_NewStringObj(name, -1));
    return TCL_OK;
}


/*
 * ------------------------------------------------------------------------
 *  Itcl_BiInfoInheritCmd()
 *
 *  Returns the list of base classes for the current class context.
 *  Returns a status TCL_OK/TCL_ERROR to indicate success/failure.
 * ------------------------------------------------------------------------
 */
/* ARGSUSED */
int
Itcl_BiInfoInheritCmd(dummy, interp, objc, objv)
    ClientData dummy;     /* not used */
    Tcl_Interp *interp;   /* current interpreter */
    int objc;                /* number of arguments */
    Tcl_Obj *CONST objv[];   /* argument objects */
{
    Tcl_Namespace *activeNs = Tcl_GetCurrentNamespace(interp);

    ItclClass *contextClass;
    ItclObject *contextObj;

    ItclClass *cdefn;
    Itcl_ListElem *elem;
    Tcl_Obj *listPtr, *objPtr;

    if (objc != 1) {
        Tcl_WrongNumArgs(interp, 1, objv, NULL);
        return TCL_ERROR;
    }

    /*
     *  If this command is not invoked within a class namespace,
     *  signal an error.
     */
    if (Itcl_GetContext(interp, &contextClass, &contextObj) != TCL_OK) {
        char *name = Tcl_GetStringFromObj(objv[0], (int*)NULL);
        Tcl_ResetResult(interp);
        Tcl_AppendResult(interp,
            "\nget info like this instead: ",
            "\n  namespace eval className { info ", name, "... }",
            (char*)NULL);
        return TCL_ERROR;
    }

    /*
     *  Return the list of base classes.
     */
    listPtr = Tcl_NewListObj(0, (Tcl_Obj**)NULL);

    elem = Itcl_FirstListElem(&contextClass->bases);
    while (elem) {
        cdefn = (ItclClass*)Itcl_GetListValue(elem);
        if (cdefn->namesp->parentPtr == activeNs) {
            objPtr = Tcl_NewStringObj(cdefn->namesp->name, -1);
        } else {
            objPtr = Tcl_NewStringObj(cdefn->namesp->fullName, -1);
        }
        Tcl_ListObjAppendElement((Tcl_Interp*)NULL, listPtr, objPtr);
        elem = Itcl_NextListElem(elem);
    }

    Tcl_SetObjResult(interp, listPtr);
    return TCL_OK;
}

/*
 * ------------------------------------------------------------------------
 *  Itcl_BiInfoHeritageCmd()
 *
 *  Returns the entire derivation hierarchy for this class, presented
 *  in the order that classes are traversed for finding data members
 *  and member functions.
 *
 *  Returns a status TCL_OK/TCL_ERROR to indicate success/failure.
 * ------------------------------------------------------------------------
 */
/* ARGSUSED */
int
Itcl_BiInfoHeritageCmd(dummy, interp, objc, objv)
    ClientData dummy;     /* not used */
    Tcl_Interp *interp;   /* current interpreter */
    int objc;                /* number of arguments */
    Tcl_Obj *CONST objv[];   /* argument objects */
{
    Tcl_Namespace *activeNs = Tcl_GetCurrentNamespace(interp);

    ItclClass *contextClass;
    ItclObject *contextObj;

    char *name;
    ItclHierIter hier;
    Tcl_Obj *listPtr, *objPtr;
    ItclClass *cdefn;

    if (objc != 1) {
        Tcl_WrongNumArgs(interp, 1, objv, NULL);
        return TCL_ERROR;
    }

    /*
     *  If this command is not invoked within a class namespace,
     *  signal an error.
     */
    if (Itcl_GetContext(interp, &contextClass, &contextObj) != TCL_OK) {
        name = Tcl_GetStringFromObj(objv[0], (int*)NULL);
        Tcl_ResetResult(interp);
        Tcl_AppendResult(interp,
            "\nget info like this instead: ",
            "\n  namespace eval className { info ", name, "... }",
            (char*)NULL);
        return TCL_ERROR;
    }

    /*
     *  Traverse through the derivation hierarchy and return
     *  base class names.
     */
    listPtr = Tcl_NewListObj(0, (Tcl_Obj**)NULL);

    Itcl_InitHierIter(&hier, contextClass);
    while ((cdefn=Itcl_AdvanceHierIter(&hier)) != NULL) {
        if (cdefn->namesp->parentPtr == activeNs) {
            objPtr = Tcl_NewStringObj(cdefn->namesp->name, -1);
        } else {
            objPtr = Tcl_NewStringObj(cdefn->namesp->fullName, -1);
        }
        Tcl_ListObjAppendElement((Tcl_Interp*)NULL, listPtr, objPtr);
    }
    Itcl_DeleteHierIter(&hier);

    Tcl_SetObjResult(interp, listPtr);
    return TCL_OK;
}


/*
 * ------------------------------------------------------------------------
 *  Itcl_BiInfoFunctionCmd()
 *
 *  Returns information regarding class member functions (methods/procs).
 *  Handles the following syntax:
 *
 *    info function ?cmdName? ?-protection? ?-type? ?-name? ?-args? ?-body?
 *
 *  If the ?cmdName? is not specified, then a list of all known
 *  command members is returned.  Otherwise, the information for
 *  a specific command is returned.  Returns a status TCL_OK/TCL_ERROR
 *  to indicate success/failure.
 * ------------------------------------------------------------------------
 */
/* ARGSUSED */
int
Itcl_BiInfoFunctionCmd(dummy, interp, objc, objv)
    ClientData dummy;     /* not used */
    Tcl_Interp *interp;   /* current interpreter */
    int objc;                /* number of arguments */
    Tcl_Obj *CONST objv[];   /* argument objects */
{
    char *cmdName = NULL;
    Tcl_Obj *resultPtr = NULL;
    Tcl_Obj *objPtr = NULL;

    static char *options[] = {
        "-args", "-body", "-name", "-protection", "-type",
        (char*)NULL
    };
    enum BIfIdx {
        BIfArgsIdx, BIfBodyIdx, BIfNameIdx, BIfProtectIdx, BIfTypeIdx
    } *iflist, iflistStorage[5];

    static enum BIfIdx DefInfoFunction[5] = {
        BIfProtectIdx,
        BIfTypeIdx,
        BIfNameIdx,
        BIfArgsIdx,
        BIfBodyIdx
    };

    ItclClass *contextClass, *cdefn;
    ItclObject *contextObj;

    int i, result;
    char *name, *val;
    Tcl_HashSearch place;
    Tcl_HashEntry *entry;
    ItclMemberFunc *mfunc;
    ItclMemberCode *mcode;
    ItclHierIter hier;

    /*
     *  If this command is not invoked within a class namespace,
     *  signal an error.
     */
    if (Itcl_GetContext(interp, &contextClass, &contextObj) != TCL_OK) {
        name = Tcl_GetStringFromObj(objv[0], (int*)NULL);
        Tcl_ResetResult(interp);
        Tcl_AppendResult(interp,
            "\nget info like this instead: ",
            "\n  namespace eval className { info ", name, "... }",
            (char*)NULL);
        return TCL_ERROR;
    }

    /*
     *  Process args:
     *  ?cmdName? ?-protection? ?-type? ?-name? ?-args? ?-body?
     */
    objv++;  /* skip over command name */
    objc--;

    if (objc > 0) {
        cmdName = Tcl_GetStringFromObj(*objv, (int*)NULL);
        objc--; objv++;
    }

    /*
     *  Return info for a specific command.
     */
    if (cmdName) {
        entry = Tcl_FindHashEntry(&contextClass->resolveCmds, cmdName);
        if (entry == NULL) {
            Tcl_AppendResult(interp,
                "\"", cmdName, "\" isn't a member function in class \"",
                contextClass->namesp->fullName, "\"",
                (char*)NULL);
            return TCL_ERROR;
        }

        mfunc = (ItclMemberFunc*)Tcl_GetHashValue(entry);
        mcode = mfunc->member->code;

        /*
         *  By default, return everything.
         */
        if (objc == 0) {
            objc = 5;
            iflist = DefInfoFunction;
        }

        /*
         *  Otherwise, scan through all remaining flags and
         *  figure out what to return.
         */
        else {
            iflist = &iflistStorage[0];
            for (i=0 ; i < objc; i++) {
                result = Tcl_GetIndexFromObj(interp, objv[i],
                    options, "option", 0, (int*)(&iflist[i]));
                if (result != TCL_OK) {
                    return TCL_ERROR;
                }
            }
        }

        if (objc > 1) {
            resultPtr = Tcl_NewListObj(0, (Tcl_Obj**)NULL);
        }

        for (i=0 ; i < objc; i++) {
            switch (iflist[i]) {
                case BIfArgsIdx:
                    if (mcode && mcode->arglist) {
                        objPtr = Itcl_ArgList(mcode->argcount, mcode->arglist);
                    }
                    else if ((mfunc->member->flags & ITCL_ARG_SPEC) != 0) {
                        objPtr = Itcl_ArgList(mfunc->argcount, mfunc->arglist);
                    }
                    else {
                        objPtr = Tcl_NewStringObj("<undefined>", -1);
                    }
                    break;

                case BIfBodyIdx:
                    if (mcode && Itcl_IsMemberCodeImplemented(mcode)) {
                        objPtr = mcode->procPtr->bodyPtr;
                    } else {
                        objPtr = Tcl_NewStringObj("<undefined>", -1);
                    }
                    break;

                case BIfNameIdx:
                    objPtr = Tcl_NewStringObj(mfunc->member->fullname, -1);
                    break;

                case BIfProtectIdx:
                    val = Itcl_ProtectionStr(mfunc->member->protection);
                    objPtr = Tcl_NewStringObj(val, -1);
                    break;

                case BIfTypeIdx:
                    val = ((mfunc->member->flags & ITCL_COMMON) != 0)
                        ? "proc" : "method";
                    objPtr = Tcl_NewStringObj(val, -1);
                    break;
            }

            if (objc == 1) {
                resultPtr = objPtr;
            } else {
                Tcl_ListObjAppendElement((Tcl_Interp*)NULL, resultPtr, objPtr);
            }
        }
        Tcl_SetObjResult(interp, resultPtr);
    }

    /*
     *  Return the list of available commands.
     */
    else {
        resultPtr = Tcl_NewListObj(0, (Tcl_Obj**)NULL);

        Itcl_InitHierIter(&hier, contextClass);
        while ((cdefn=Itcl_AdvanceHierIter(&hier)) != NULL) {
            entry = Tcl_FirstHashEntry(&cdefn->functions, &place);
            while (entry) {
                mfunc = (ItclMemberFunc*)Tcl_GetHashValue(entry);
                objPtr = Tcl_NewStringObj(mfunc->member->fullname, -1);
                Tcl_ListObjAppendElement((Tcl_Interp*)NULL, resultPtr, objPtr);

                entry = Tcl_NextHashEntry(&place);
            }
        }
        Itcl_DeleteHierIter(&hier);

        Tcl_SetObjResult(interp, resultPtr);
    }
    return TCL_OK;
}

/*
 * ------------------------------------------------------------------------
 *  Itcl_BiInfoVariableCmd()
 *
 *  Returns information regarding class data members (variables and
 *  commons).  Handles the following syntax:
 *
 *    info variable ?varName? ?-protection? ?-type? ?-name?
 *        ?-init? ?-config? ?-value?
 *
 *  If the ?varName? is not specified, then a list of all known
 *  data members is returned.  Otherwise, the information for a
 *  specific member is returned.  Returns a status TCL_OK/TCL_ERROR
 *  to indicate success/failure.
 * ------------------------------------------------------------------------
 */
/* ARGSUSED */
int
Itcl_BiInfoVariableCmd(dummy, interp, objc, objv)
    ClientData dummy;        /* not used */
    Tcl_Interp *interp;      /* current interpreter */
    int objc;                /* number of arguments */
    Tcl_Obj *CONST objv[];   /* argument objects */
{
    char *varName = NULL;
    Tcl_Obj *resultPtr = NULL;
    Tcl_Obj *objPtr = NULL;

    static char *options[] = {
        "-config", "-init", "-name", "-protection", "-type",
        "-value", (char*)NULL
    };
    enum BIvIdx {
        BIvConfigIdx, BIvInitIdx, BIvNameIdx, BIvProtectIdx,
        BIvTypeIdx, BIvValueIdx
    } *ivlist, ivlistStorage[6];

    static enum BIvIdx DefInfoVariable[5] = {
        BIvProtectIdx,
        BIvTypeIdx,
        BIvNameIdx,
        BIvInitIdx,
        BIvValueIdx
    };

    static enum BIvIdx DefInfoPubVariable[6] = {
        BIvProtectIdx,
        BIvTypeIdx,
        BIvNameIdx,
        BIvInitIdx,
        BIvConfigIdx,
        BIvValueIdx
    };

    ItclClass *contextClass;
    ItclObject *contextObj;

    int i, result;
    CONST char *val, *name;
    ItclClass *cdefn;
    Tcl_HashSearch place;
    Tcl_HashEntry *entry;
    ItclVarDefn *vdefn;
    ItclVarLookup *vlookup;
    ItclMember *member;
    ItclHierIter hier;

    /*
     *  If this command is not invoked within a class namespace,
     *  signal an error.
     */
    if (Itcl_GetContext(interp, &contextClass, &contextObj) != TCL_OK) {
        name = Tcl_GetStringFromObj(objv[0], (int*)NULL);
        Tcl_ResetResult(interp);
        Tcl_AppendResult(interp,
            "\nget info like this instead: ",
            "\n  namespace eval className { info ", name, "... }",
            (char*)NULL);
        return TCL_ERROR;
    }

    /*
     *  Process args:
     *  ?varName? ?-protection? ?-type? ?-name? ?-init? ?-config? ?-value?
     */
    objv++;  /* skip over command name */
    objc--;

    if (objc > 0) {
        varName = Tcl_GetStringFromObj(*objv, (int*)NULL);
        objc--; objv++;
    }

    /*
     *  Return info for a specific variable.
     */
    if (varName) {
        entry = Tcl_FindHashEntry(&contextClass->resolveVars, varName);
        if (entry == NULL) {
            Tcl_AppendResult(interp,
                "\"", varName, "\" isn't a variable in class \"",
                contextClass->namesp->fullName, "\"",
                (char*)NULL);
            return TCL_ERROR;
        }

        vlookup = (ItclVarLookup*)Tcl_GetHashValue(entry);
        member = vlookup->vdefn->member;

        /*
         *  By default, return everything.
         */
        if (objc == 0) {
            if (member->protection == ITCL_PUBLIC &&
                ((member->flags & ITCL_COMMON) == 0)) {
                ivlist = DefInfoPubVariable;
                objc = 6;
            } else {
                ivlist = DefInfoVariable;
                objc = 5;
            }
        }

        /*
         *  Otherwise, scan through all remaining flags and
         *  figure out what to return.
         */
        else {
            ivlist = &ivlistStorage[0];
            for (i=0 ; i < objc; i++) {
                result = Tcl_GetIndexFromObj(interp, objv[i],
                    options, "option", 0, (int*)(&ivlist[i]));
                if (result != TCL_OK) {
                    return TCL_ERROR;
                }
            }
        }

        if (objc > 1) {
            resultPtr = Tcl_NewListObj(0, (Tcl_Obj**)NULL);
        }

        for (i=0 ; i < objc; i++) {
            switch (ivlist[i]) {
                case BIvConfigIdx:
                    if (member->code && Itcl_IsMemberCodeImplemented(member->code)) {
                        objPtr = member->code->procPtr->bodyPtr;
                    } else {
                        objPtr = Tcl_NewStringObj("", -1);
                    }
                    break;

                case BIvInitIdx:
                    /*
                     *  If this is the built-in "this" variable, then
                     *  report the object name as its initialization string.
                     */
                    if ((member->flags & ITCL_THIS_VAR) != 0) {
                        if (contextObj && contextObj->accessCmd) {
                            objPtr = Tcl_NewStringObj((char*)NULL, 0);
                            Tcl_GetCommandFullName(
                                contextObj->classDefn->interp,
                                contextObj->accessCmd, objPtr);
                        } else {
                            objPtr = Tcl_NewStringObj("<objectName>", -1);
                        }
                    }
                    else if (vlookup->vdefn->init) {
                        objPtr = Tcl_NewStringObj(vlookup->vdefn->init, -1);
                    }
                    else {
                        objPtr = Tcl_NewStringObj("<undefined>", -1);
                    }
                    break;

                case BIvNameIdx:
                    objPtr = Tcl_NewStringObj(member->fullname, -1);
                    break;

                case BIvProtectIdx:
                    val = Itcl_ProtectionStr(member->protection);
                    objPtr = Tcl_NewStringObj((CONST84 char *)val, -1);
                    break;

                case BIvTypeIdx:
                    val = ((member->flags & ITCL_COMMON) != 0)
                        ? "common" : "variable";
                    objPtr = Tcl_NewStringObj((CONST84 char *)val, -1);
                    break;

                case BIvValueIdx:
                    if ((member->flags & ITCL_COMMON) != 0) {
                        val = Itcl_GetCommonVar(interp, member->fullname,
                            member->classDefn);
                    }
                    else if (contextObj == NULL) {
                        Tcl_ResetResult(interp);
                        Tcl_AppendResult(interp,
                            "cannot access object-specific info ",
                            "without an object context",
                            (char*)NULL);
                        return TCL_ERROR;
                    }
                    else {
                        val = Itcl_GetInstanceVar(interp, member->fullname,
                            contextObj, member->classDefn);
                    }

                    if (val == NULL) {
                        val = "<undefined>";
                    }
                    objPtr = Tcl_NewStringObj((CONST84 char *)val, -1);
                    break;
            }

            if (objc == 1) {
                resultPtr = objPtr;
            } else {
                Tcl_ListObjAppendElement((Tcl_Interp*)NULL, resultPtr,
                    objPtr);
            }
        }
        Tcl_SetObjResult(interp, resultPtr);
    }

    /*
     *  Return the list of available variables.  Report the built-in
     *  "this" variable only once, for the most-specific class.
     */
    else {
        resultPtr = Tcl_NewListObj(0, (Tcl_Obj**)NULL);

        Itcl_InitHierIter(&hier, contextClass);
        while ((cdefn=Itcl_AdvanceHierIter(&hier)) != NULL) {
            entry = Tcl_FirstHashEntry(&cdefn->variables, &place);
            while (entry) {
                vdefn = (ItclVarDefn*)Tcl_GetHashValue(entry);
                if ((vdefn->member->flags & ITCL_THIS_VAR) != 0) {
                    if (cdefn == contextClass) {
                        objPtr = Tcl_NewStringObj(vdefn->member->fullname, -1);
                        Tcl_ListObjAppendElement((Tcl_Interp*)NULL,
                            resultPtr, objPtr);
                    }
                }
                else {
                    objPtr = Tcl_NewStringObj(vdefn->member->fullname, -1);
                    Tcl_ListObjAppendElement((Tcl_Interp*)NULL,
                        resultPtr, objPtr);
                }
                entry = Tcl_NextHashEntry(&place);
            }
        }
        Itcl_DeleteHierIter(&hier);

        Tcl_SetObjResult(interp, resultPtr);
    }
    return TCL_OK;
}


/*
 * ------------------------------------------------------------------------
 *  Itcl_BiInfoBodyCmd()
 *
 *  Handles the usual "info body" request, returning the body for a
 *  specific proc.  Included here for backward compatibility, since
 *  otherwise Tcl would complain that class procs are not real "procs".
 *  Returns a status TCL_OK/TCL_ERROR to indicate success/failure.
 * ------------------------------------------------------------------------
 */
/* ARGSUSED */
int
Itcl_BiInfoBodyCmd(dummy, interp, objc, objv)
    ClientData dummy;     /* not used */
    Tcl_Interp *interp;   /* current interpreter */
    int objc;                /* number of arguments */
    Tcl_Obj *CONST objv[];   /* argument objects */
{
    char *name;
    ItclClass *contextClass;
    ItclObject *contextObj;
    ItclMemberFunc *mfunc;
    ItclMemberCode *mcode;
    Tcl_HashEntry *entry;
    Tcl_Obj *objPtr;

    if (objc != 2) {
        Tcl_WrongNumArgs(interp, 1, objv, "function");
        return TCL_ERROR;
    }

    /*
     *  If this command is not invoked within a class namespace,
     *  then treat the procedure name as a normal Tcl procedure.
     */
    if (!Itcl_IsClassNamespace(Tcl_GetCurrentNamespace(interp))) {
        Proc *procPtr;

        name = Tcl_GetStringFromObj(objv[1], (int*)NULL);
        procPtr = TclFindProc((Interp*)interp, name);
        if (procPtr == NULL) {
            Tcl_AppendResult(interp,
                "\"", name, "\" isn't a procedure",
                (char*)NULL);
            return TCL_ERROR;
        }
        Tcl_SetObjResult(interp, procPtr->bodyPtr);
    }

    /*
     *  Otherwise, treat the name as a class method/proc.
     */
    if (Itcl_GetContext(interp, &contextClass, &contextObj) != TCL_OK) {
        name = Tcl_GetStringFromObj(objv[0], (int*)NULL);
        Tcl_ResetResult(interp);
        Tcl_AppendResult(interp,
            "\nget info like this instead: ",
            "\n  namespace eval className { info ", name, "... }",
            (char*)NULL);
        return TCL_ERROR;
    }

    name = Tcl_GetStringFromObj(objv[1], (int*)NULL);
    entry = Tcl_FindHashEntry(&contextClass->resolveCmds, name);
    if (entry == NULL) {
        Tcl_AppendResult(interp,
            "\"", name, "\" isn't a procedure",
            (char*)NULL);
        return TCL_ERROR;
    }

    mfunc = (ItclMemberFunc*)Tcl_GetHashValue(entry);
    mcode = mfunc->member->code;

    /*
     *  Return a string describing the implementation.
     */
    if (mcode && Itcl_IsMemberCodeImplemented(mcode)) {
        objPtr = mcode->procPtr->bodyPtr;
    } else {
        objPtr = Tcl_NewStringObj("<undefined>", -1);
    }
    Tcl_SetObjResult(interp, objPtr);
    return TCL_OK;
}


/*
 * ------------------------------------------------------------------------
 *  Itcl_BiInfoArgsCmd()
 *
 *  Handles the usual "info args" request, returning the argument list
 *  for a specific proc.  Included here for backward compatibility, since
 *  otherwise Tcl would complain that class procs are not real "procs".
 *  Returns a status TCL_OK/TCL_ERROR to indicate success/failure.
 * ------------------------------------------------------------------------
 */
/* ARGSUSED */
int
Itcl_BiInfoArgsCmd(dummy, interp, objc, objv)
    ClientData dummy;     /* not used */
    Tcl_Interp *interp;   /* current interpreter */
    int objc;                /* number of arguments */
    Tcl_Obj *CONST objv[];   /* argument objects */
{
    char *name;
    ItclClass *contextClass;
    ItclObject *contextObj;
    ItclMemberFunc *mfunc;
    ItclMemberCode *mcode;
    Tcl_HashEntry *entry;
    Tcl_Obj *objPtr;

    if (objc != 2) {
        Tcl_WrongNumArgs(interp, 1, objv, "function");
        return TCL_ERROR;
    }

    name = Tcl_GetStringFromObj(objv[1], (int*)NULL);

    /*
     *  If this command is not invoked within a class namespace,
     *  then treat the procedure name as a normal Tcl procedure.
     */
    if (!Itcl_IsClassNamespace(Tcl_GetCurrentNamespace(interp))) {
        Proc *procPtr;
        CompiledLocal *localPtr;

        procPtr = TclFindProc((Interp*)interp, name);
        if (procPtr == NULL) {
            Tcl_AppendResult(interp,
                "\"", name, "\" isn't a procedure",
                (char*)NULL);
            return TCL_ERROR;
        }

        objPtr = Tcl_NewListObj(0, (Tcl_Obj**)NULL);
        for (localPtr = procPtr->firstLocalPtr;
             localPtr != NULL;
             localPtr = localPtr->nextPtr) {
            if (TclIsVarArgument(localPtr)) {
                Tcl_ListObjAppendElement(interp, objPtr,
                    Tcl_NewStringObj(localPtr->name, -1));
            }
        }

        Tcl_SetObjResult(interp, objPtr);
    }

    /*
     *  Otherwise, treat the name as a class method/proc.
     */
    if (Itcl_GetContext(interp, &contextClass, &contextObj) != TCL_OK) {
        name = Tcl_GetStringFromObj(objv[0], (int*)NULL);
        Tcl_ResetResult(interp);
        Tcl_AppendResult(interp,
            "\nget info like this instead: ",
            "\n  namespace eval className { info ", name, "... }",
            (char*)NULL);
        return TCL_ERROR;
    }

    entry = Tcl_FindHashEntry(&contextClass->resolveCmds, name);
    if (entry == NULL) {
        Tcl_AppendResult(interp,
            "\"", name, "\" isn't a procedure",
            (char*)NULL);
        return TCL_ERROR;
    }

    mfunc = (ItclMemberFunc*)Tcl_GetHashValue(entry);
    mcode = mfunc->member->code;

    /*
     *  Return a string describing the argument list.
     */
    if (mcode && mcode->arglist != NULL) {
        objPtr = Itcl_ArgList(mcode->argcount, mcode->arglist);
    }
    else if ((mfunc->member->flags & ITCL_ARG_SPEC) != 0) {
        objPtr = Itcl_ArgList(mfunc->argcount, mfunc->arglist);
    }
    else {
        objPtr = Tcl_NewStringObj("<undefined>", -1);
    }
    Tcl_SetObjResult(interp, objPtr);
    return TCL_OK;
}


/*
 * ------------------------------------------------------------------------
 *  Itcl_DefaultInfoCmd()
 *
 *  Handles any unknown options for the "itcl::builtin::info" command
 *  by passing requests on to the usual "::info" command.  If the
 *  option is recognized, then it is handled.  Otherwise, if it is
 *  still unknown, then an error message is returned with the list
 *  of possible options.
 *
 *  Returns TCL_OK/TCL_ERROR to indicate success/failure.
 * ------------------------------------------------------------------------
 */
/* ARGSUSED */
int
Itcl_DefaultInfoCmd(dummy, interp, objc, objv)
    ClientData dummy;     /* not used */
    Tcl_Interp *interp;   /* current interpreter */
    int objc;                /* number of arguments */
    Tcl_Obj *CONST objv[];   /* argument objects */
{
    int result;
    char *name;
    Tcl_Command cmd;
    Command *cmdPtr;
    Tcl_Obj *resultPtr;

    /*
     *  Look for the usual "::info" command, and use it to
     *  evaluate the unknown option.
     */
    cmd = Tcl_FindCommand(interp, "::info", (Tcl_Namespace*)NULL, 0);
    if (cmd == NULL) {
        name = Tcl_GetStringFromObj(objv[0], (int*)NULL);
        Tcl_ResetResult(interp);

        resultPtr = Tcl_NewObj();
        Tcl_AppendStringsToObj(resultPtr,
            "bad option \"", name, "\" should be one of...\n",
            (char*)NULL);
        Itcl_GetEnsembleUsageForObj(interp, objv[0], resultPtr);
	Tcl_SetObjResult(interp, resultPtr);

        return TCL_ERROR;
    }

    cmdPtr = (Command*)cmd;
    result = (*cmdPtr->objProc)(cmdPtr->objClientData, interp, objc, objv);

    /*
     *  If the option was not recognized by the usual "info" command,
     *  then we got a "bad option" error message.  Add the options
     *  for the current ensemble to the error message.
     */
    if (result != TCL_OK && strncmp(interp->result,"bad option",10) == 0) {
        resultPtr = Tcl_NewObj();
        Tcl_AppendToObj(resultPtr, "\nor", -1);
        Itcl_GetEnsembleUsageForObj(interp, objv[0], resultPtr);
	Tcl_SetObjResult(interp, resultPtr);
    }
    return result;
}
