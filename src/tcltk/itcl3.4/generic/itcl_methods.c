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
 *  These procedures handle commands available within a class scope.
 *  In [incr Tcl], the term "method" is used for a procedure that has
 *  access to object-specific data, while the term "proc" is used for
 *  a procedure that has access only to common class data.
 *
 * ========================================================================
 *  AUTHOR:  Michael J. McLennan
 *           Bell Labs Innovations for Lucent Technologies
 *           mmclennan@lucent.com
 *           http://www.tcltk.com/itcl
 *
 *     RCS:  $Id: itcl_methods.c,v 1.23 2008/06/13 22:14:44 hobbs Exp $
 * ========================================================================
 *           Copyright (c) 1993-1998  Lucent Technologies, Inc.
 * ------------------------------------------------------------------------
 * See the file "license.terms" for information on usage and redistribution
 * of this file, and for a DISCLAIMER OF ALL WARRANTIES.
 */
#include "itclInt.h"

/*
 *  FORWARD DECLARATIONS
 */
static int ItclParseConfig _ANSI_ARGS_((Tcl_Interp *interp,
    int objc, Tcl_Obj *CONST objv[], ItclObject *contextObj,
    int *rargc, ItclVarDefn ***rvars, char ***rvals));

static int ItclHandleConfig _ANSI_ARGS_((Tcl_Interp *interp,
    int argc, ItclVarDefn **vars, char **vals, ItclObject *contextObj));


/*
 * ------------------------------------------------------------------------
 *  Itcl_BodyCmd()
 *
 *  Invoked by Tcl whenever the user issues an "itcl::body" command to
 *  define or redefine the implementation for a class method/proc.
 *  Handles the following syntax:
 *
 *    itcl::body <class>::<func> <arglist> <body>
 *
 *  Looks for an existing class member function with the name <func>,
 *  and if found, tries to assign the implementation.  If an argument
 *  list was specified in the original declaration, it must match
 *  <arglist> or an error is flagged.  If <body> has the form "@name"
 *  then it is treated as a reference to a C handling procedure;
 *  otherwise, it is taken as a body of Tcl statements.
 *
 *  Returns TCL_OK/TCL_ERROR to indicate success/failure.
 * ------------------------------------------------------------------------
 */
/* ARGSUSED */
int
Itcl_BodyCmd(dummy, interp, objc, objv)
    ClientData dummy;        /* unused */
    Tcl_Interp *interp;      /* current interpreter */
    int objc;                /* number of arguments */
    Tcl_Obj *CONST objv[];   /* argument objects */
{
    int status = TCL_OK;

    char *head, *tail, *token, *arglist, *body;
    ItclClass *cdefn;
    ItclMemberFunc *mfunc;
    Tcl_HashEntry *entry;
    Tcl_DString buffer;

    if (objc != 4) {
        token = Tcl_GetStringFromObj(objv[0], (int*)NULL);
        Tcl_AppendResult(interp,
            "wrong # args: should be \"",
            token, " class::func arglist body\"",
            (char*)NULL);
        return TCL_ERROR;
    }

    /*
     *  Parse the member name "namesp::namesp::class::func".
     *  Make sure that a class name was specified, and that the
     *  class exists.
     */
    token = Tcl_GetStringFromObj(objv[1], (int*)NULL);
    Itcl_ParseNamespPath(token, &buffer, &head, &tail);

    if (!head || *head == '\0') {
        Tcl_AppendResult(interp,
            "missing class specifier for body declaration \"", token, "\"",
            (char*)NULL);
        status = TCL_ERROR;
        goto bodyCmdDone;
    }

    cdefn = Itcl_FindClass(interp, head, /* autoload */ 1);
    if (cdefn == NULL) {
        status = TCL_ERROR;
        goto bodyCmdDone;
    }

    /*
     *  Find the function and try to change its implementation.
     *  Note that command resolution table contains *all* functions,
     *  even those in a base class.  Make sure that the class
     *  containing the method definition is the requested class.
     */

    mfunc = NULL;
    entry = Tcl_FindHashEntry(&cdefn->resolveCmds, tail);
    if (entry) {
        mfunc = (ItclMemberFunc*)Tcl_GetHashValue(entry);
        if (mfunc->member->classDefn != cdefn) {
            mfunc = NULL;
        }
    }

    if (mfunc == NULL) {
        Tcl_AppendResult(interp,
            "function \"", tail, "\" is not defined in class \"",
            cdefn->fullname, "\"",
            (char*)NULL);
        status = TCL_ERROR;
        goto bodyCmdDone;
    }

    arglist = Tcl_GetStringFromObj(objv[2], (int*)NULL);
    body    = Tcl_GetStringFromObj(objv[3], (int*)NULL);

    if (Itcl_ChangeMemberFunc(interp, mfunc, arglist, body) != TCL_OK) {
        status = TCL_ERROR;
        goto bodyCmdDone;
    }

bodyCmdDone:
    Tcl_DStringFree(&buffer);
    return status;
}


/*
 * ------------------------------------------------------------------------
 *  Itcl_ConfigBodyCmd()
 *
 *  Invoked by Tcl whenever the user issues an "itcl::configbody" command
 *  to define or redefine the configuration code associated with a
 *  public variable.  Handles the following syntax:
 *
 *    itcl::configbody <class>::<publicVar> <body>
 *
 *  Looks for an existing public variable with the name <publicVar>,
 *  and if found, tries to assign the implementation.  If <body> has
 *  the form "@name" then it is treated as a reference to a C handling
 *  procedure; otherwise, it is taken as a body of Tcl statements.
 *
 *  Returns TCL_OK/TCL_ERROR to indicate success/failure.
 * ------------------------------------------------------------------------
 */
/* ARGSUSED */
int
Itcl_ConfigBodyCmd(dummy, interp, objc, objv)
    ClientData dummy;        /* unused */
    Tcl_Interp *interp;      /* current interpreter */
    int objc;                /* number of arguments */
    Tcl_Obj *CONST objv[];   /* argument objects */
{
    int status = TCL_OK;

    char *head, *tail, *token;
    Tcl_DString buffer;
    ItclClass *cdefn;
    ItclVarLookup *vlookup;
    ItclMember *member;
    ItclMemberCode *mcode;
    Tcl_HashEntry *entry;

    if (objc != 3) {
        Tcl_WrongNumArgs(interp, 1, objv, "class::option body");
        return TCL_ERROR;
    }

    /*
     *  Parse the member name "namesp::namesp::class::option".
     *  Make sure that a class name was specified, and that the
     *  class exists.
     */
    token = Tcl_GetStringFromObj(objv[1], (int*)NULL);
    Itcl_ParseNamespPath(token, &buffer, &head, &tail);

    if (!head || *head == '\0') {
        Tcl_AppendResult(interp,
            "missing class specifier for body declaration \"", token, "\"",
            (char*)NULL);
        status = TCL_ERROR;
        goto configBodyCmdDone;
    }

    cdefn = Itcl_FindClass(interp, head, /* autoload */ 1);
    if (cdefn == NULL) {
        status = TCL_ERROR;
        goto configBodyCmdDone;
    }

    /*
     *  Find the variable and change its implementation.
     *  Note that variable resolution table has *all* variables,
     *  even those in a base class.  Make sure that the class
     *  containing the variable definition is the requested class.
     */
    vlookup = NULL;
    entry = Tcl_FindHashEntry(&cdefn->resolveVars, tail);
    if (entry) {
        vlookup = (ItclVarLookup*)Tcl_GetHashValue(entry);
        if (vlookup->vdefn->member->classDefn != cdefn) {
            vlookup = NULL;
        }
    }

    if (vlookup == NULL) {
        Tcl_AppendResult(interp,
            "option \"", tail, "\" is not defined in class \"",
            cdefn->fullname, "\"",
            (char*)NULL);
        status = TCL_ERROR;
        goto configBodyCmdDone;
    }
    member = vlookup->vdefn->member;

    if (member->protection != ITCL_PUBLIC) {
        Tcl_AppendResult(interp,
            "option \"", member->fullname,
            "\" is not a public configuration option",
            (char*)NULL);
        status = TCL_ERROR;
        goto configBodyCmdDone;
    }

    token = Tcl_GetStringFromObj(objv[2], (int*)NULL);

    if (Itcl_CreateMemberCode(interp, cdefn, (char*)NULL, token,
        &mcode) != TCL_OK) {

        status = TCL_ERROR;
        goto configBodyCmdDone;
    }

    Itcl_PreserveData((ClientData)mcode);
    Itcl_EventuallyFree((ClientData)mcode, (Tcl_FreeProc*) Itcl_DeleteMemberCode);

    if (member->code) {
        Itcl_ReleaseData((ClientData)member->code);
    }
    member->code = mcode;

configBodyCmdDone:
    Tcl_DStringFree(&buffer);
    return status;
}


/*
 * ------------------------------------------------------------------------
 *  Itcl_CreateMethod()
 *
 *  Installs a method into the namespace associated with a class.
 *  If another command with the same name is already installed, then
 *  it is overwritten.
 *
 *  Returns TCL_OK on success, or TCL_ERROR (along with an error message
 *  in the specified interp) if anything goes wrong.
 * ------------------------------------------------------------------------
 */
int
Itcl_CreateMethod(interp, cdefn, name, arglist, body)
    Tcl_Interp* interp;  /* interpreter managing this action */
    ItclClass *cdefn;    /* class definition */
    CONST char* name;    /* name of new method */
    CONST char* arglist; /* space-separated list of arg names */
    CONST char* body;    /* body of commands for the method */
{
    ItclMemberFunc *mfunc;
    Tcl_DString buffer;

    /*
     *  Make sure that the method name does not contain anything
     *  goofy like a "::" scope qualifier.
     */
    if (strstr(name,"::")) {
        Tcl_AppendResult(interp,
            "bad method name \"", name, "\"",
            (char*)NULL);
        return TCL_ERROR;
    }

    /*
     *  Create the method definition.
     */
    if (Itcl_CreateMemberFunc(interp, cdefn, name, arglist, body, &mfunc)
        != TCL_OK) {
        return TCL_ERROR;
    }

    /*
     *  Build a fully-qualified name for the method, and install
     *  the command handler.
     */
    Tcl_DStringInit(&buffer);
    Tcl_DStringAppend(&buffer, cdefn->namesp->fullName, -1);
    Tcl_DStringAppend(&buffer, "::", 2);
    Tcl_DStringAppend(&buffer, name, -1);
    name = Tcl_DStringValue(&buffer);

    Itcl_PreserveData((ClientData)mfunc);
    mfunc->accessCmd = Tcl_CreateObjCommand(interp, (CONST84 char *)name,
	Itcl_ExecMethod, (ClientData)mfunc, Itcl_ReleaseData);

    Tcl_DStringFree(&buffer);
    return TCL_OK;
}


/*
 * ------------------------------------------------------------------------
 *  Itcl_CreateProc()
 *
 *  Installs a class proc into the namespace associated with a class.
 *  If another command with the same name is already installed, then
 *  it is overwritten.  Returns TCL_OK on success, or TCL_ERROR  (along
 *  with an error message in the specified interp) if anything goes
 *  wrong.
 * ------------------------------------------------------------------------
 */
int
Itcl_CreateProc(interp, cdefn, name, arglist, body)
    Tcl_Interp* interp;  /* interpreter managing this action */
    ItclClass *cdefn;    /* class definition */
    CONST char* name;    /* name of new proc */
    CONST char* arglist; /* space-separated list of arg names */
    CONST char* body;    /* body of commands for the proc */
{
    ItclMemberFunc *mfunc;
    Tcl_DString buffer;

    /*
     *  Make sure that the proc name does not contain anything
     *  goofy like a "::" scope qualifier.
     */
    if (strstr(name,"::")) {
        Tcl_AppendResult(interp,
            "bad proc name \"", name, "\"",
            (char*)NULL);
        return TCL_ERROR;
    }

    /*
     *  Create the proc definition.
     */
    if (Itcl_CreateMemberFunc(interp, cdefn, name, arglist, body, &mfunc)
        != TCL_OK) {
        return TCL_ERROR;
    }

    /*
     *  Mark procs as "common".  This distinguishes them from methods.
     */
    mfunc->member->flags |= ITCL_COMMON;

    /*
     *  Build a fully-qualified name for the proc, and install
     *  the command handler.
     */
    Tcl_DStringInit(&buffer);
    Tcl_DStringAppend(&buffer, cdefn->namesp->fullName, -1);
    Tcl_DStringAppend(&buffer, "::", 2);
    Tcl_DStringAppend(&buffer, name, -1);
    name = Tcl_DStringValue(&buffer);

    Itcl_PreserveData((ClientData)mfunc);
    mfunc->accessCmd = Tcl_CreateObjCommand(interp, (CONST84 char *)name,
	Itcl_ExecProc, (ClientData)mfunc, Itcl_ReleaseData);

    Tcl_DStringFree(&buffer);
    return TCL_OK;
}


/*
 * ------------------------------------------------------------------------
 *  Itcl_CreateMemberFunc()
 *
 *  Creates the data record representing a member function.  This
 *  includes the argument list and the body of the function.  If the
 *  body is of the form "@name", then it is treated as a label for
 *  a C procedure registered by Itcl_RegisterC().
 *
 *  If any errors are encountered, this procedure returns TCL_ERROR
 *  along with an error message in the interpreter.  Otherwise, it
 *  returns TCL_OK, and "mfuncPtr" returns a pointer to the new
 *  member function.
 * ------------------------------------------------------------------------
 */
int
Itcl_CreateMemberFunc(interp, cdefn, name, arglist, body, mfuncPtr)
    Tcl_Interp* interp;            /* interpreter managing this action */
    ItclClass *cdefn;              /* class definition */
    CONST char* name;              /* name of new member */
    CONST char* arglist;           /* space-separated list of arg names */
    CONST char* body;              /* body of commands for the method */
    ItclMemberFunc** mfuncPtr;     /* returns: pointer to new method defn */
{
    int newEntry;
    ItclMemberFunc *mfunc;
    ItclMemberCode *mcode;
    Tcl_HashEntry *entry;

    /*
     *  Add the member function to the list of functions for
     *  the class.  Make sure that a member function with the
     *  same name doesn't already exist.
     */
    entry = Tcl_CreateHashEntry(&cdefn->functions, name, &newEntry);

    if (!newEntry) {
        Tcl_AppendResult(interp,
            "\"", name, "\" already defined in class \"",
            cdefn->fullname, "\"",
            (char*)NULL);
        return TCL_ERROR;
    }

    /*
     *  Try to create the implementation for this command member.
     */
    if (Itcl_CreateMemberCode(interp, cdefn, arglist, body,
        &mcode) != TCL_OK) {

        Tcl_DeleteHashEntry(entry);
        return TCL_ERROR;
    }
    Itcl_PreserveData((ClientData)mcode);
    Itcl_EventuallyFree((ClientData)mcode, (Tcl_FreeProc*) Itcl_DeleteMemberCode);

    /*
     *  Allocate a member function definition and return.
     */
    mfunc = (ItclMemberFunc*)ckalloc(sizeof(ItclMemberFunc));
    mfunc->member = Itcl_CreateMember(interp, cdefn, name);
    mfunc->member->code = mcode;

    if (mfunc->member->protection == ITCL_DEFAULT_PROTECT) {
        mfunc->member->protection = ITCL_PUBLIC;
    }

    mfunc->arglist   = NULL;
    mfunc->argcount  = 0;
    mfunc->accessCmd = NULL;

    if (arglist) {
        mfunc->member->flags |= ITCL_ARG_SPEC;
    }
    if (mcode->arglist) {
        Itcl_CreateArgList(interp, arglist, &mfunc->argcount, &mfunc->arglist);
    }

    if (strcmp(name,"constructor") == 0) {
        mfunc->member->flags |= ITCL_CONSTRUCTOR;
    }
    if (strcmp(name,"destructor") == 0) {
        mfunc->member->flags |= ITCL_DESTRUCTOR;
    }

    Tcl_SetHashValue(entry, (ClientData)mfunc);
    Itcl_PreserveData((ClientData)mfunc);
    Itcl_EventuallyFree((ClientData)mfunc, (Tcl_FreeProc*) Itcl_DeleteMemberFunc);

    *mfuncPtr = mfunc;
    return TCL_OK;
}


/*
 * ------------------------------------------------------------------------
 *  Itcl_ChangeMemberFunc()
 *
 *  Modifies the data record representing a member function.  This
 *  is usually the body of the function, but can include the argument
 *  list if it was not defined when the member was first created.
 *  If the body is of the form "@name", then it is treated as a label
 *  for a C procedure registered by Itcl_RegisterC().
 *
 *  If any errors are encountered, this procedure returns TCL_ERROR
 *  along with an error message in the interpreter.  Otherwise, it
 *  returns TCL_OK, and "mfuncPtr" returns a pointer to the new
 *  member function.
 * ------------------------------------------------------------------------
 */
int
Itcl_ChangeMemberFunc(interp, mfunc, arglist, body)
    Tcl_Interp* interp;            /* interpreter managing this action */
    ItclMemberFunc* mfunc;         /* command member being changed */
    CONST char* arglist;           /* space-separated list of arg names */
    CONST char* body;              /* body of commands for the method */
{
    ItclMemberCode *mcode = NULL;
    Tcl_Obj *objPtr;

    /*
     *  Try to create the implementation for this command member.
     */
    if (Itcl_CreateMemberCode(interp, mfunc->member->classDefn,
        arglist, body, &mcode) != TCL_OK) {

        return TCL_ERROR;
    }

    /*
     *  If the argument list was defined when the function was
     *  created, compare the arg lists or usage strings to make sure
     *  that the interface is not being redefined.
     */
    if ((mfunc->member->flags & ITCL_ARG_SPEC) != 0 &&
        !Itcl_EquivArgLists(mfunc->arglist, mfunc->argcount,
            mcode->arglist, mcode->argcount)) {

        objPtr = Itcl_ArgList(mfunc->argcount, mfunc->arglist);
        Tcl_IncrRefCount(objPtr);

        Tcl_AppendResult(interp,
            "argument list changed for function \"",
            mfunc->member->fullname, "\": should be \"",
            Tcl_GetStringFromObj(objPtr, (int*)NULL), "\"",
            (char*)NULL);
        Tcl_DecrRefCount(objPtr);

        Itcl_DeleteMemberCode((char*)mcode);
        return TCL_ERROR;
    }

    /*
     *  Free up the old implementation and install the new one.
     */
    Itcl_PreserveData((ClientData)mcode);
    Itcl_EventuallyFree((ClientData)mcode, (Tcl_FreeProc*) Itcl_DeleteMemberCode);

    Itcl_ReleaseData((ClientData)mfunc->member->code);
    mfunc->member->code = mcode;

    return TCL_OK;
}


/*
 * ------------------------------------------------------------------------
 *  Itcl_DeleteMemberFunc()
 *
 *  Destroys all data associated with the given member function definition.
 *  Usually invoked by the interpreter when a member function is deleted.
 * ------------------------------------------------------------------------
 */
void
Itcl_DeleteMemberFunc(cdata)
    CONST char* cdata;  /* pointer to member function definition */
{
    ItclMemberFunc* mfunc = (ItclMemberFunc*)cdata;

    if (mfunc) {
        Itcl_DeleteMember(mfunc->member);

        if (mfunc->arglist) {
            Itcl_DeleteArgList(mfunc->arglist);
        }
        ckfree((char*)mfunc);
    }
}


/*
 * ------------------------------------------------------------------------
 *  Itcl_CreateMemberCode()
 *
 *  Creates the data record representing the implementation behind a
 *  class member function.  This includes the argument list and the body
 *  of the function.  If the body is of the form "@name", then it is
 *  treated as a label for a C procedure registered by Itcl_RegisterC().
 *
 *  The implementation is kept by the member function definition, and
 *  controlled by a preserve/release paradigm.  That way, if it is in
 *  use while it is being redefined, it will stay around long enough
 *  to avoid a core dump.
 *
 *  If any errors are encountered, this procedure returns TCL_ERROR
 *  along with an error message in the interpreter.  Otherwise, it
 *  returns TCL_OK, and "mcodePtr" returns a pointer to the new
 *  implementation.
 * ------------------------------------------------------------------------
 */
int
Itcl_CreateMemberCode(interp, cdefn, arglist, body, mcodePtr)
    Tcl_Interp* interp;            /* interpreter managing this action */
    ItclClass *cdefn;              /* class containing this member */
    CONST char* arglist;           /* space-separated list of arg names */
    CONST char* body;              /* body of commands for the method */
    ItclMemberCode** mcodePtr;     /* returns: pointer to new implementation */
{
    int argc;
    CompiledLocal *args, *localPtr;
    ItclMemberCode *mcode;
    Proc *procPtr;

    /*
     *  Allocate some space to hold the implementation.
     */
    mcode = (ItclMemberCode*)ckalloc(sizeof(ItclMemberCode));
    memset(mcode, 0, sizeof(ItclMemberCode));

    if (arglist) {
        if (Itcl_CreateArgList(interp, arglist, &argc, &args)
            != TCL_OK) {

            Itcl_DeleteMemberCode((char*)mcode);
            return TCL_ERROR;
        }
        mcode->argcount = argc;
        mcode->arglist  = args;
        mcode->flags   |= ITCL_ARG_SPEC;
    } else {
        argc = 0;
        args = NULL;
    }

    /*
     *  Create a standard Tcl Proc representation for this code body.
     *  This is required, since the Tcl compiler looks for a proc
     *  when handling things such as the call frame context and
     *  compiled locals.
     */
    procPtr = (Proc*)ckalloc(sizeof(Proc));
    mcode->procPtr = procPtr;

    procPtr->iPtr = (Interp*)interp;
    procPtr->refCount = 1;
    procPtr->cmdPtr = (Command*)ckalloc(sizeof(Command));
    memset(procPtr->cmdPtr, 0, sizeof(Command));
    procPtr->cmdPtr->nsPtr = (Namespace*)cdefn->namesp;

    if (body) {
        procPtr->bodyPtr = Tcl_NewStringObj((CONST84 char *)body, -1);
    } else {
        procPtr->bodyPtr = Tcl_NewStringObj((CONST84 char *)"", -1);
        mcode->flags |= ITCL_IMPLEMENT_NONE;
    }
    Tcl_IncrRefCount(procPtr->bodyPtr);

    /*
     *  Plug the argument list into the "compiled locals" list.
     *
     *  NOTE:  The storage for this argument list is owned by
     *    the caller, so although we plug it in here, it is not
     *    our responsibility to free it.
     */
    procPtr->firstLocalPtr = args;
    procPtr->lastLocalPtr = NULL;

    for (localPtr=mcode->arglist; localPtr; localPtr=localPtr->nextPtr) {
        procPtr->lastLocalPtr = localPtr;
    }
    procPtr->numArgs = argc;
    procPtr->numCompiledLocals = argc;

    /*
     *  If the body definition starts with '@', then treat the value
     *  as a symbolic name for a C procedure.
     */
    if (body == NULL) {
        /* No-op */
    }
    else if (*body == '@') {
        Tcl_CmdProc *argCmdProc;
        Tcl_ObjCmdProc *objCmdProc;
        ClientData cdata;

        if (!Itcl_FindC(interp, body+1, &argCmdProc, &objCmdProc, &cdata)) {
            Tcl_AppendResult(interp,
                "no registered C procedure with name \"", body+1, "\"",
                (char*)NULL);
            Itcl_DeleteMemberCode((char*)mcode);
            return TCL_ERROR;
        }

        if (objCmdProc != NULL) {
            mcode->flags |= ITCL_IMPLEMENT_OBJCMD;
            mcode->cfunc.objCmd = objCmdProc;
            mcode->clientData = cdata;
        }
        else if (argCmdProc != NULL) {
            mcode->flags |= ITCL_IMPLEMENT_ARGCMD;
            mcode->cfunc.argCmd = argCmdProc;
            mcode->clientData = cdata;
        }
    }

    /*
     *  Otherwise, treat the body as a chunk of Tcl code.
     */
    else {
        mcode->flags |= ITCL_IMPLEMENT_TCL;
    }

    *mcodePtr = mcode;
    return TCL_OK;
}


/*
 * ------------------------------------------------------------------------
 *  Itcl_DeleteMemberCode()
 *
 *  Destroys all data associated with the given command implementation.
 *  Invoked automatically by Itcl_ReleaseData() when the implementation
 *  is no longer being used.
 * ------------------------------------------------------------------------
 */
void
Itcl_DeleteMemberCode(cdata)
    CONST char* cdata;  /* pointer to member function definition */
{
    ItclMemberCode* mcode = (ItclMemberCode*)cdata;

    /*
     * Free the argument list.  If empty, free the compiled locals, if any.
     */
    if (mcode->arglist) {
        Itcl_DeleteArgList(mcode->arglist);
    } else if (mcode->procPtr && mcode->procPtr->firstLocalPtr) {
	Itcl_DeleteArgList(mcode->procPtr->firstLocalPtr);
    }

    if (mcode->procPtr) {
        ckfree((char*) mcode->procPtr->cmdPtr);

        if (mcode->procPtr->bodyPtr) {
            Tcl_DecrRefCount(mcode->procPtr->bodyPtr);
        }
        ckfree((char*)mcode->procPtr);
    }
    ckfree((char*)mcode);
}


/*
 * ------------------------------------------------------------------------
 *  Itcl_GetMemberCode()
 *
 *  Makes sure that the implementation for an [incr Tcl] code body is
 *  ready to run.  Note that a member function can be declared without
 *  being defined.  The class definition may contain a declaration of
 *  the member function, but its body may be defined in a separate file.
 *  If an undefined function is encountered, this routine automatically
 *  attempts to autoload it.  If the body is implemented via Tcl code,
 *  then it is compiled here as well.
 *
 *  Returns TCL_ERROR (along with an error message in the interpreter)
 *  if an error is encountered, or if the implementation is not defined
 *  and cannot be autoloaded.  Returns TCL_OK if implementation is
 *  ready to use.
 * ------------------------------------------------------------------------
 */
int
Itcl_GetMemberCode(interp, member)
    Tcl_Interp* interp;        /* interpreter managing this action */
    ItclMember* member;        /* member containing code body */
{
    int result;
    ItclMemberCode *mcode = member->code;
    assert(mcode != NULL);

    /*
     *  If the implementation has not yet been defined, try to
     *  autoload it now.
     */

    if (!Itcl_IsMemberCodeImplemented(mcode)) {
        result = Tcl_VarEval(interp, "::auto_load ", member->fullname,
            (char*)NULL);
        if (result != TCL_OK) {
            char msg[256];
            sprintf(msg, "\n    (while autoloading code for \"%.100s\")",
                member->fullname);
            Tcl_AddErrorInfo(interp, msg);
            return result;
        }
        Tcl_ResetResult(interp);  /* get rid of 1/0 status */
    }

    /*
     *  If the implementation is still not available, then
     *  autoloading must have failed.
     *
     *  TRICKY NOTE:  If code has been autoloaded, then the
     *    old mcode pointer is probably invalid.  Go back to
     *    the member and look at the current code pointer again.
     */
    mcode = member->code;
    assert(mcode != NULL);

    if (!Itcl_IsMemberCodeImplemented(mcode)) {
        Tcl_AppendResult(interp,
            "member function \"", member->fullname,
            "\" is not defined and cannot be autoloaded",
            (char*)NULL);
        return TCL_ERROR;
    }

    /*
     *  If the member is a constructor and the class has an
     *  initialization command, compile it here.
     */
    if ((member->flags & ITCL_CONSTRUCTOR) != 0 &&
        (member->classDefn->initCode != NULL)) {
        result = TclProcCompileProc(interp, mcode->procPtr,
            member->classDefn->initCode, (Namespace*)member->classDefn->namesp,
            "initialization code for", member->fullname);

        if (result != TCL_OK) {
            return result;
        }
    }

    /*
     *  If the code body has a Tcl implementation, then compile it here.
     */
    if ((mcode->flags & ITCL_IMPLEMENT_TCL) != 0) {

        result = TclProcCompileProc(interp, mcode->procPtr,
            mcode->procPtr->bodyPtr, (Namespace*)member->classDefn->namesp,
            "body for", member->fullname);

        if (result != TCL_OK) {
            return result;
        }
    }
    return TCL_OK;
}


/*
 * ------------------------------------------------------------------------
 *  Itcl_EvalMemberCode()
 *
 *  Used to execute an ItclMemberCode representation of a code
 *  fragment.  This code may be a body of Tcl commands, or a C handler
 *  procedure.
 *
 *  Executes the command with the given arguments (objc,objv) and
 *  returns an integer status code (TCL_OK/TCL_ERROR).  Returns the
 *  result string or an error message in the interpreter.
 * ------------------------------------------------------------------------
 */
int
Itcl_EvalMemberCode(interp, mfunc, member, contextObj, objc, objv)
    Tcl_Interp *interp;       /* current interpreter */
    ItclMemberFunc *mfunc;    /* member func, or NULL (for error messages) */
    ItclMember *member;       /* command member containing code */
    ItclObject *contextObj;   /* object context, or NULL */
    int objc;                 /* number of arguments */
    Tcl_Obj *CONST objv[];    /* argument objects */
{
    int result = TCL_OK;
    Itcl_CallFrame *oldFramePtr = NULL;

    int i, transparent, newEntry;
    ItclObjectInfo *info;
    ItclMemberCode *mcode;
    ItclContext context;
    Itcl_CallFrame *framePtr, *transFramePtr;

    /*
     *  If this code does not have an implementation yet, then
     *  try to autoload one.  Also, if this is Tcl code, make sure
     *  that it's compiled and ready to use.
     */
    if (Itcl_GetMemberCode(interp, member) != TCL_OK) {
        return TCL_ERROR;
    }
    mcode = member->code;

    /*
     *  Bump the reference count on this code, in case it is
     *  redefined or deleted during execution.
     */
    Itcl_PreserveData((ClientData)mcode);

    /*
     *  Install a new call frame context for the current code.
     *  If the current call frame is marked as "transparent", then
     *  do an "uplevel" operation to move past it.  Transparent
     *  call frames are installed by Itcl_HandleInstance.  They
     *  provide a way of entering an object context without
     *  interfering with the normal call stack.
     */
    transparent = 0;

    info = member->classDefn->info;
    framePtr = _Tcl_GetCallFrame(interp, 0);
    for (i = Itcl_GetStackSize(&info->transparentFrames)-1; i >= 0; i--) {
        transFramePtr = (Itcl_CallFrame*)
            Itcl_GetStackValue(&info->transparentFrames, i);

        if (framePtr == transFramePtr) {
            transparent = 1;
            break;
        }
    }

    if (transparent) {
        framePtr = _Tcl_GetCallFrame(interp, 1);
        oldFramePtr = _Tcl_ActivateCallFrame(interp, framePtr);
    }

    if (Itcl_PushContext(interp, member, member->classDefn, contextObj,
        &context) != TCL_OK) {

        return TCL_ERROR;
    }

    /*
     *  If this is a method with a Tcl implementation, or a
     *  constructor with initCode, then parse its arguments now.
     */
    if (mfunc && objc > 0) {
        if ((mcode->flags & ITCL_IMPLEMENT_TCL) != 0 ||
            ( (member->flags & ITCL_CONSTRUCTOR) != 0 &&
              (member->classDefn->initCode != NULL) ) ) {

            if (Itcl_AssignArgs(interp, objc, objv, mfunc) != TCL_OK) {
                result = TCL_ERROR;
                goto evalMemberCodeDone;
            }
        }
    }

    /*
     *  If this code is a constructor, and if it is being invoked
     *  when an object is first constructed (i.e., the "constructed"
     *  table is still active within the object), then handle the
     *  "initCode" associated with the constructor and make sure that
     *  all base classes are properly constructed.
     *
     *  TRICKY NOTE:
     *    The "initCode" must be executed here.  This is the only
     *    opportunity where the arguments of the constructor are
     *    available in a call frame.
     */
    if ((member->flags & ITCL_CONSTRUCTOR) && contextObj &&
        contextObj->constructed) {

        result = Itcl_ConstructBase(interp, contextObj, member->classDefn);

        if (result != TCL_OK) {
            goto evalMemberCodeDone;
        }
    }

    /*
     *  Execute the code body...
     */
    if ((mcode->flags & ITCL_IMPLEMENT_OBJCMD) != 0) {
        result = (*mcode->cfunc.objCmd)(mcode->clientData,
            interp, objc, objv);
    }
    else if ((mcode->flags & ITCL_IMPLEMENT_ARGCMD) != 0) {
        char **argv;
        argv = (char**)ckalloc( (unsigned)(objc*sizeof(char*)) );
        for (i=0; i < objc; i++) {
            argv[i] = Tcl_GetStringFromObj(objv[i], (int*)NULL);
        }

        result = (*mcode->cfunc.argCmd)(mcode->clientData,
            interp, objc, argv);

        ckfree((char*)argv);
    }
    else if ((mcode->flags & ITCL_IMPLEMENT_TCL) != 0) {
        result = Tcl_EvalObj(interp, mcode->procPtr->bodyPtr);
    }
    else {
        Tcl_Panic("itcl: bad implementation flag for %s", member->fullname);
    }

    /*
     *  If this is a constructor or destructor, and if it is being
     *  invoked at the appropriate time, keep track of which methods
     *  have been called.  This information is used to implicitly
     *  invoke constructors/destructors as needed.
     */
    if ((member->flags & ITCL_DESTRUCTOR) && contextObj &&
         contextObj->destructed) {

        Tcl_CreateHashEntry(contextObj->destructed,
            member->classDefn->fullname, &newEntry);
    }
    if ((member->flags & ITCL_CONSTRUCTOR) && contextObj &&
         contextObj->constructed) {

        Tcl_CreateHashEntry(contextObj->constructed,
            member->classDefn->name, &newEntry);
    }

evalMemberCodeDone:
    Itcl_PopContext(interp, &context);

    if (transparent) {
        (void) _Tcl_ActivateCallFrame(interp, oldFramePtr);
    }
    Itcl_ReleaseData((ClientData)mcode);

    return result;
}


/*
 * ------------------------------------------------------------------------
 *  Itcl_CreateArgList()
 *
 *  Parses a Tcl list representing an argument declaration and returns
 *  a linked list of CompiledLocal values.  Usually invoked as part
 *  of Itcl_CreateMemberFunc() when a new method or procedure is being
 *  defined.
 * ------------------------------------------------------------------------
 */
int
Itcl_CreateArgList(interp, decl, argcPtr, argPtr)
    Tcl_Interp* interp;       /* interpreter managing this function */
    CONST char* decl;         /* string representing argument list */
    int* argcPtr;             /* returns number of args in argument list */
    CompiledLocal** argPtr;   /* returns pointer to parsed argument list */
{
    int status = TCL_OK;  /* assume that this will succeed */

    int i, argc, fargc;
    char **argv, **fargv;
    CompiledLocal *localPtr, *last;

    *argPtr = last = NULL;
    *argcPtr = 0;

    if (decl) {
        if (Tcl_SplitList(interp, (CONST84 char *)decl, &argc, &argv)
		!= TCL_OK) {
            return TCL_ERROR;
        }

        for (i=0; i < argc && status == TCL_OK; i++) {
            if (Tcl_SplitList(interp, argv[i], &fargc, &fargv) != TCL_OK) {
                status = TCL_ERROR;
            }
            else {
                localPtr = NULL;

                if (fargc == 0 || *fargv[0] == '\0') {
                    char mesg[100];
                    sprintf(mesg, "argument #%d has no name", i);
                    Tcl_SetResult(interp, mesg, TCL_VOLATILE);
                    status = TCL_ERROR;
                }
                else if (fargc > 2) {
                    Tcl_AppendResult(interp,
                        "too many fields in argument specifier \"",
                        argv[i], "\"",
                        (char*)NULL);
                    status = TCL_ERROR;
                }
                else if (strstr(fargv[0],"::")) {
                    Tcl_AppendResult(interp,
                        "bad argument name \"", fargv[0], "\"",
                        (char*)NULL);
                    status = TCL_ERROR;
                }
                else if (fargc == 1) {
                    localPtr = Itcl_CreateArg(fargv[0], (char*)NULL);
                }
                else {
                    localPtr = Itcl_CreateArg(fargv[0], fargv[1]);
                }

                if (localPtr) {
                    localPtr->frameIndex = i;

                    if (*argPtr == NULL) {
                        *argPtr = last = localPtr;
                    }
                    else {
                        last->nextPtr = localPtr;
                        last = localPtr;
                    }
                }
            }
            ckfree((char*)fargv);
        }
        ckfree((char*)argv);
    }

    /*
     *  If anything went wrong, destroy whatever arguments were
     *  created and return an error.
     */
    if (status == TCL_OK) {
        *argcPtr = argc;
    } else {
        Itcl_DeleteArgList(*argPtr);
        *argPtr = NULL;
    }
    return status;
}


/*
 * ------------------------------------------------------------------------
 *  Itcl_CreateArg()
 *
 *  Creates a new Tcl Arg structure and fills it with the given
 *  information.  Returns a pointer to the new Arg structure.
 * ------------------------------------------------------------------------
 */
CompiledLocal*
Itcl_CreateArg(name, init)
    CONST char* name;     /* name of new argument */
    CONST char* init;     /* initial value */
{
    CompiledLocal *localPtr = NULL;
    int nameLen;

    if (name == NULL) {
        name = "";
    }
    nameLen = strlen(name);

    localPtr = (CompiledLocal*)ckalloc(
        (unsigned)(sizeof(CompiledLocal)-sizeof(localPtr->name) + nameLen+1)
    );

    localPtr->nextPtr = NULL;
    localPtr->nameLength = nameLen;
    localPtr->frameIndex = 0;  /* set this later */
    ItclInitVarArgument(localPtr);
    localPtr->resolveInfo = NULL;

    if (init != NULL) {
        localPtr->defValuePtr = Tcl_NewStringObj((CONST84 char *)init, -1);
        Tcl_IncrRefCount(localPtr->defValuePtr);
    } else {
        localPtr->defValuePtr = NULL;
    }

    strcpy(localPtr->name, name);

    return localPtr;
}

/*
 * ------------------------------------------------------------------------
 *  Itcl_DeleteArgList()
 *
 *  Destroys a chain of arguments acting as an argument list.  Usually
 *  invoked when a method/proc is being destroyed, to discard its
 *  argument list.
 * ------------------------------------------------------------------------
 */
void
Itcl_DeleteArgList(arglist)
    CompiledLocal *arglist;   /* first argument in arg list chain */
{
    CompiledLocal *localPtr, *next;

    for (localPtr=arglist; localPtr; localPtr=next) {
        if (localPtr->defValuePtr != NULL) {
            Tcl_DecrRefCount(localPtr->defValuePtr);
        }
        if (localPtr->resolveInfo) {
            if (localPtr->resolveInfo->deleteProc) {
                localPtr->resolveInfo->deleteProc(localPtr->resolveInfo);
            } else {
                ckfree((char*)localPtr->resolveInfo);
            }
            localPtr->resolveInfo = NULL;
        }
        next = localPtr->nextPtr;
        ckfree((char*)localPtr);
    }
}

/*
 * ------------------------------------------------------------------------
 *  Itcl_ArgList()
 *
 *  Returns a Tcl_Obj containing the string representation for the
 *  given argument list.  This object has a reference count of 1.
 *  The reference count should be decremented when the string is no
 *  longer needed, and it will free itself.
 * ------------------------------------------------------------------------
 */
Tcl_Obj*
Itcl_ArgList(argc, arglist)
    int argc;                   /* number of arguments */
    CompiledLocal* arglist;     /* first argument in arglist */
{
    char *val;
    Tcl_Obj *objPtr;
    Tcl_DString buffer;

    Tcl_DStringInit(&buffer);

    while (arglist && argc-- > 0) {
        if (arglist->defValuePtr) {
            val = Tcl_GetStringFromObj(arglist->defValuePtr, (int*)NULL);
            Tcl_DStringStartSublist(&buffer);
            Tcl_DStringAppendElement(&buffer, arglist->name);
            Tcl_DStringAppendElement(&buffer, val);
            Tcl_DStringEndSublist(&buffer);
        }
        else {
            Tcl_DStringAppendElement(&buffer, arglist->name);
        }
        arglist = arglist->nextPtr;
    }

    objPtr = Tcl_NewStringObj(Tcl_DStringValue(&buffer),
        Tcl_DStringLength(&buffer));

    Tcl_DStringFree(&buffer);

    return objPtr;
}


/*
 * ------------------------------------------------------------------------
 *  Itcl_EquivArgLists()
 *
 *  Compares two argument lists to see if they are equivalent.  The
 *  first list is treated as a prototype, and the second list must
 *  match it.  Argument names may be different, but they must match in
 *  meaning.  If one argument is optional, the corresponding argument
 *  must also be optional.  If the prototype list ends with the magic
 *  "args" argument, then it matches everything in the other list.
 *
 *  Returns non-zero if the argument lists are equivalent.
 * ------------------------------------------------------------------------
 */
int
Itcl_EquivArgLists(arg1, arg1c, arg2, arg2c)
    CompiledLocal* arg1;   /* prototype argument list */
    int arg1c;             /* number of args in prototype arg list */
    CompiledLocal* arg2;   /* another argument list to match against */
    int arg2c;             /* number of args in matching list */
{
    char *dval1, *dval2;

    while (arg1 && arg1c > 0 && arg2 && arg2c > 0) {
        /*
         *  If the prototype argument list ends with the magic "args"
         *  argument, then it matches everything in the other list.
         */
        if (arg1c == 1 && strcmp(arg1->name,"args") == 0) {
            return 1;
        }

        /*
         *  If one has a default value, then the other must have the
         *  same default value.
         */
        if (arg1->defValuePtr) {
            if (arg2->defValuePtr == NULL) {
                return 0;
            }

            dval1 = Tcl_GetStringFromObj(arg1->defValuePtr, (int*)NULL);
            dval2 = Tcl_GetStringFromObj(arg2->defValuePtr, (int*)NULL);
            if (strcmp(dval1, dval2) != 0) {
                return 0;
            }
        }
        else if (arg2->defValuePtr) {
            return 0;
        }

        arg1 = arg1->nextPtr;  arg1c--;
        arg2 = arg2->nextPtr;  arg2c--;
    }
    if (arg1c == 1 && strcmp(arg1->name,"args") == 0) {
        return 1;
    }
    return (arg1c == 0 && arg2c == 0);
}


/*
 * ------------------------------------------------------------------------
 *  Itcl_GetMemberFuncUsage()
 *
 *  Returns a string showing how a command member should be invoked.
 *  If the command member is a method, then the specified object name
 *  is reported as part of the invocation path:
 *
 *      obj method arg ?arg arg ...?
 *
 *  Otherwise, the "obj" pointer is ignored, and the class name is
 *  used as the invocation path:
 *
 *      class::proc arg ?arg arg ...?
 *
 *  Returns the string by appending it onto the Tcl_Obj passed in as
 *  an argument.
 * ------------------------------------------------------------------------
 */
void
Itcl_GetMemberFuncUsage(mfunc, contextObj, objPtr)
    ItclMemberFunc *mfunc;      /* command member being examined */
    ItclObject *contextObj;     /* invoked with respect to this object */
    Tcl_Obj *objPtr;            /* returns: string showing usage */
{
    int argcount;
    char *name;
    CompiledLocal *arglist, *argPtr;
    Tcl_HashEntry *entry;
    ItclMemberFunc *mf;
    ItclClass *cdefnPtr;

    /*
     *  If the command is a method and an object context was
     *  specified, then add the object context.  If the method
     *  was a constructor, and if the object is being created,
     *  then report the invocation via the class creation command.
     */
    if ((mfunc->member->flags & ITCL_COMMON) == 0) {
        if ((mfunc->member->flags & ITCL_CONSTRUCTOR) != 0 &&
            contextObj->constructed) {

            cdefnPtr = (ItclClass*)contextObj->classDefn;
            mf = NULL;
            entry = Tcl_FindHashEntry(&cdefnPtr->resolveCmds, "constructor");
            if (entry) {
                mf = (ItclMemberFunc*)Tcl_GetHashValue(entry);
            }

            if (mf == mfunc) {
                Tcl_GetCommandFullName(contextObj->classDefn->interp,
                    contextObj->classDefn->accessCmd, objPtr);
                Tcl_AppendToObj(objPtr, " ", -1);
                name = (char *) Tcl_GetCommandName(
		    contextObj->classDefn->interp, contextObj->accessCmd);
                Tcl_AppendToObj(objPtr, name, -1);
            } else {
                Tcl_AppendToObj(objPtr, mfunc->member->fullname, -1);
            }
        } else if (contextObj && contextObj->accessCmd) {
            name = (char *) Tcl_GetCommandName(contextObj->classDefn->interp,
                contextObj->accessCmd);
            Tcl_AppendStringsToObj(objPtr, name, " ", mfunc->member->name,
                (char*)NULL);
        } else {
            Tcl_AppendStringsToObj(objPtr, "<object> ", mfunc->member->name,
                (char*)NULL);
        }
    } else {
        Tcl_AppendToObj(objPtr, mfunc->member->fullname, -1);
    }

    /*
     *  Add the argument usage info.
     */
    if (mfunc->member->code) {
        arglist = mfunc->member->code->arglist;
        argcount = mfunc->member->code->argcount;
    } else if (mfunc->arglist) {
        arglist = mfunc->arglist;
        argcount = mfunc->argcount;
    } else {
        arglist = NULL;
        argcount = 0;
    }

    if (arglist) {
        for (argPtr=arglist;
             argPtr && argcount > 0;
             argPtr=argPtr->nextPtr, argcount--) {

            if (argcount == 1 && strcmp(argPtr->name, "args") == 0) {
                Tcl_AppendToObj(objPtr, " ?arg arg ...?", -1);
            }
            else if (argPtr->defValuePtr) {
                Tcl_AppendStringsToObj(objPtr, " ?", argPtr->name, "?",
                    (char*)NULL);
            }
            else {
                Tcl_AppendStringsToObj(objPtr, " ", argPtr->name,
                    (char*)NULL);
            }
        }
    }
}


/*
 * ------------------------------------------------------------------------
 *  Itcl_ExecMethod()
 *
 *  Invoked by Tcl to handle the execution of a user-defined method.
 *  A method is similar to the usual Tcl proc, but has access to
 *  object-specific data.  If for some reason there is no current
 *  object context, then a method call is inappropriate, and an error
 *  is returned.
 *
 *  Methods are implemented either as Tcl code fragments, or as C-coded
 *  procedures.  For Tcl code fragments, command arguments are parsed
 *  according to the argument list, and the body is executed in the
 *  scope of the class where it was defined.  For C procedures, the
 *  arguments are passed in "as-is", and the procedure is executed in
 *  the most-specific class scope.
 * ------------------------------------------------------------------------
 */
int
Itcl_ExecMethod(clientData, interp, objc, objv)
    ClientData clientData;   /* method definition */
    Tcl_Interp *interp;      /* current interpreter */
    int objc;                /* number of arguments */
    Tcl_Obj *CONST objv[];   /* argument objects */
{
    ItclMemberFunc *mfunc = (ItclMemberFunc*)clientData;
    ItclMember *member = mfunc->member;
    int result = TCL_OK;

    char *token;
    Tcl_HashEntry *entry;
    ItclClass *contextClass;
    ItclObject *contextObj;

    /*
     *  Make sure that the current namespace context includes an
     *  object that is being manipulated.  Methods can be executed
     *  only if an object context exists.
     */
    if (Itcl_GetContext(interp, &contextClass, &contextObj) != TCL_OK) {
        return TCL_ERROR;
    }
    if (contextObj == NULL) {
        Tcl_AppendResult(interp,
            "cannot access object-specific info without an object context",
            (char*)NULL);
        return TCL_ERROR;
    }

    /*
     *  Make sure that this command member can be accessed from
     *  the current namespace context.
     */
    if (mfunc->member->protection != ITCL_PUBLIC) {
        Tcl_Namespace *contextNs = Itcl_GetTrueNamespace(interp,
            contextClass->info);

        if (!Itcl_CanAccessFunc(mfunc, contextNs)) {
            Tcl_AppendResult(interp,
                "can't access \"", member->fullname, "\": ",
                Itcl_ProtectionStr(member->protection), " function",
                (char*)NULL);
            return TCL_ERROR;
        }
    }

    /*
     *  All methods should be "virtual" unless they are invoked with
     *  a "::" scope qualifier.
     *
     *  To implement the "virtual" behavior, find the most-specific
     *  implementation for the method by looking in the "resolveCmds"
     *  table for this class.
     */
    token = Tcl_GetStringFromObj(objv[0], (int*)NULL);
    if (strstr(token, "::") == NULL) {
        entry = Tcl_FindHashEntry(&contextObj->classDefn->resolveCmds,
            member->name);

        if (entry) {
            mfunc = (ItclMemberFunc*)Tcl_GetHashValue(entry);
            member = mfunc->member;
        }
    }

    /*
     *  Execute the code for the method.  Be careful to protect
     *  the method in case it gets deleted during execution.
     */
    Itcl_PreserveData((ClientData)mfunc);

    result = Itcl_EvalMemberCode(interp, mfunc, member, contextObj,
        objc, objv);

    result = Itcl_ReportFuncErrors(interp, mfunc, contextObj, result);

    Itcl_ReleaseData((ClientData)mfunc);

    return result;
}


/*
 * ------------------------------------------------------------------------
 *  Itcl_ExecProc()
 *
 *  Invoked by Tcl to handle the execution of a user-defined proc.
 *
 *  Procs are implemented either as Tcl code fragments, or as C-coded
 *  procedures.  For Tcl code fragments, command arguments are parsed
 *  according to the argument list, and the body is executed in the
 *  scope of the class where it was defined.  For C procedures, the
 *  arguments are passed in "as-is", and the procedure is executed in
 *  the most-specific class scope.
 * ------------------------------------------------------------------------
 */
int
Itcl_ExecProc(clientData, interp, objc, objv)
    ClientData clientData;   /* proc definition */
    Tcl_Interp *interp;      /* current interpreter */
    int objc;                /* number of arguments */
    Tcl_Obj *CONST objv[];   /* argument objects */
{
    ItclMemberFunc *mfunc = (ItclMemberFunc*)clientData;
    ItclMember *member = mfunc->member;
    int result = TCL_OK;

    /*
     *  Make sure that this command member can be accessed from
     *  the current namespace context.
     */
    if (mfunc->member->protection != ITCL_PUBLIC) {
        Tcl_Namespace *contextNs = Itcl_GetTrueNamespace(interp,
            mfunc->member->classDefn->info);

        if (!Itcl_CanAccessFunc(mfunc, contextNs)) {
            Tcl_AppendResult(interp,
                "can't access \"", member->fullname, "\": ",
                Itcl_ProtectionStr(member->protection), " function",
                (char*)NULL);
            return TCL_ERROR;
        }
    }

    /*
     *  Execute the code for the proc.  Be careful to protect
     *  the proc in case it gets deleted during execution.
     */
    Itcl_PreserveData((ClientData)mfunc);

    result = Itcl_EvalMemberCode(interp, mfunc, member, (ItclObject*)NULL,
        objc, objv);

    result = Itcl_ReportFuncErrors(interp, mfunc, (ItclObject*)NULL, result);

    Itcl_ReleaseData((ClientData)mfunc);

    return result;
}


/*
 * ------------------------------------------------------------------------
 *  Itcl_PushContext()
 *
 *  Sets up the class/object context so that a body of [incr Tcl]
 *  code can be executed.  This procedure pushes a call frame with
 *  the proper namespace context for the class.  If an object context
 *  is supplied, the object's instance variables are integrated into
 *  the call frame so they can be accessed as local variables.
 * ------------------------------------------------------------------------
 */
int
Itcl_PushContext(interp, member, contextClass, contextObj, contextPtr)
    Tcl_Interp *interp;       /* interpreter managing this body of code */
    ItclMember *member;       /* member containing code body */
    ItclClass *contextClass;  /* class context */
    ItclObject *contextObj;   /* object context, or NULL */
    ItclContext *contextPtr;  /* storage space for class/object context */
{
    ItclCallFrame *framePtr = &contextPtr->frame;

    int result, localCt, newEntry;
    ItclMemberCode *mcode;
    Proc *procPtr;
    Tcl_HashEntry *entry;

    /*
     *  Activate the call frame.  If this fails, we'll bail out
     *  before allocating any resources.
     *
     *  NOTE:  Always push a call frame that looks like a proc.
     *    This causes global variables to be handled properly
     *    inside methods/procs.
     */
    result = Tcl_PushCallFrame(interp, (Tcl_CallFrame*)framePtr,
                 contextClass->namesp, /* isProcCallFrame */ 1);

    if (result != TCL_OK) {
        return result;
    }

    contextPtr->classDefn = contextClass;
    contextPtr->compiledLocals = &contextPtr->localStorage[0];

    /*
     *  If this is an object context, register it in a hash table
     *  of all known contexts.  We'll need this later if we
     *  call Itcl_GetContext to get the object context for the
     *  current call frame.
     */
    if (contextObj) {
        entry = Tcl_CreateHashEntry(&contextClass->info->contextFrames,
            (char*)framePtr, &newEntry);

        Itcl_PreserveData((ClientData)contextObj);
        Tcl_SetHashValue(entry, (ClientData)contextObj);
    }

    /*
     *  Set up the compiled locals in the call frame and assign
     *  argument variables.
     */
    if (member) {
        mcode = member->code;
        procPtr = mcode->procPtr;

        /*
         * Invoking TclInitCompiledLocals with a framePtr->procPtr->bodyPtr
         * that is not a compiled byte code type leads to a crash. So
         * make sure that the body is compiled here. This needs to
         * be done even if the body of the Itcl method is not implemented
         * as a Tcl proc or has no implementation. The empty string should
         * have been defined as the body if no implementation was defined.
         */
        assert(mcode->procPtr->bodyPtr != NULL);

        result = TclProcCompileProc(interp, mcode->procPtr,
            mcode->procPtr->bodyPtr, (Namespace*)member->classDefn->namesp,
            "body for", member->fullname);

        if (result != TCL_OK) {
            return result;
        }

        /*
         *  If there are too many compiled locals to fit in the default
         *  storage space for the context, then allocate more space.
         */
        localCt = procPtr->numCompiledLocals;
        if (localCt >
		(int)(sizeof(contextPtr->localStorage)/itclVarLocalSize)) {
            contextPtr->compiledLocals = (Var*)ckalloc(
                (unsigned)(localCt * itclVarLocalSize)
            );
        }

        /*
         * Initialize and resolve compiled variable references.
         * Class variables will have special resolution rules.
         * In that case, we call their "resolver" procs to get our
         * hands on the variable, and we make the compiled local a
         * link to the real variable.
         */

        framePtr->procPtr = procPtr;
        framePtr->numCompiledLocals = localCt;
        framePtr->compiledLocals = contextPtr->compiledLocals;

        TclInitCompiledLocals(interp, (CallFrame *) framePtr,
            (Namespace*)contextClass->namesp);
    }
    return result;
}


/*
 * ------------------------------------------------------------------------
 *  Itcl_PopContext()
 *
 *  Removes a class/object context previously set up by Itcl_PushContext.
 *  Usually called after an [incr Tcl] code body has been executed,
 *  to clean up.
 * ------------------------------------------------------------------------
 */
void
Itcl_PopContext(interp, contextPtr)
    Tcl_Interp *interp;       /* interpreter managing this body of code */
    ItclContext *contextPtr;  /* storage space for class/object context */
{
    Itcl_CallFrame *framePtr;
    ItclObjectInfo *info;
    ItclObject *contextObj;
    Tcl_HashEntry *entry;

    /*
     *  See if the current call frame has an object context
     *  associated with it.  If so, release the claim on the
     *  object info.
     */
    framePtr = _Tcl_GetCallFrame(interp, 0);
    info = contextPtr->classDefn->info;

    entry = Tcl_FindHashEntry(&info->contextFrames, (char*)framePtr);
    if (entry != NULL) {
        contextObj = (ItclObject*)Tcl_GetHashValue(entry);
        Itcl_ReleaseData((ClientData)contextObj);
        Tcl_DeleteHashEntry(entry);
    }

    /*
     *  Remove the call frame.
     */
    Tcl_PopCallFrame(interp);

    /*
     * Free the compiledLocals array if malloc'ed storage was used.
     */
    if (contextPtr->compiledLocals != &contextPtr->localStorage[0]) {
        ckfree((char*)contextPtr->compiledLocals);
    }
}


/*
 * ------------------------------------------------------------------------
 *  Itcl_GetContext()
 *
 *  Convenience routine for looking up the current object/class context.
 *  Useful in implementing methods/procs to see what class, and perhaps
 *  what object, is active.
 *
 *  Returns TCL_OK if the current namespace is a class namespace.
 *  Also returns pointers to the class definition, and to object
 *  data if an object context is active.  Returns TCL_ERROR (along
 *  with an error message in the interpreter) if a class namespace
 *  is not active.
 * ------------------------------------------------------------------------
 */
int
Itcl_GetContext(interp, cdefnPtr, odefnPtr)
    Tcl_Interp *interp;           /* current interpreter */
    ItclClass **cdefnPtr;         /* returns:  class definition or NULL */
    ItclObject **odefnPtr;        /* returns:  object data or NULL */
{
    Tcl_Namespace *activeNs = Tcl_GetCurrentNamespace(interp);
    ItclObjectInfo *info;
    Itcl_CallFrame *framePtr;
    Tcl_HashEntry *entry;

    /*
     *  Return NULL for anything that cannot be found.
     */
    *cdefnPtr = NULL;
    *odefnPtr = NULL;

    /*
     *  If the active namespace is a class namespace, then return
     *  all known info.  See if the current call frame is a known
     *  object context, and if so, return that context.
     */
    if (Itcl_IsClassNamespace(activeNs)) {
        *cdefnPtr = (ItclClass*)activeNs->clientData;

        framePtr = _Tcl_GetCallFrame(interp, 0);

        info = (*cdefnPtr)->info;
        entry = Tcl_FindHashEntry(&info->contextFrames, (char*)framePtr);

        if (entry != NULL) {
            *odefnPtr = (ItclObject*)Tcl_GetHashValue(entry);
        }
        return TCL_OK;
    }

    /*
     *  If there is no class/object context, return an error message.
     */
    Tcl_AppendResult(interp,
        "namespace \"", activeNs->fullName, "\" is not a class namespace",
        (char*)NULL);

    return TCL_ERROR;
}


/*
 * ------------------------------------------------------------------------
 *  Itcl_AssignArgs()
 *
 *  Matches a list of arguments against a Tcl argument specification.
 *  Supports all of the rules regarding arguments for Tcl procs, including
 *  default arguments and variable-length argument lists.
 *
 *  Assumes that a local call frame is already installed.  As variables
 *  are successfully matched, they are stored as variables in the call
 *  frame.  Returns TCL_OK on success, or TCL_ERROR (along with an error
 *  message in interp->result) on error.
 * ------------------------------------------------------------------------
 */
int
Itcl_AssignArgs(interp, objc, objv, mfunc)
    Tcl_Interp *interp;        /* interpreter */
    int objc;                  /* number of arguments */
    Tcl_Obj *CONST objv[];     /* argument objects */
    ItclMemberFunc *mfunc;     /* member function info (for error messages) */
{
    ItclMemberCode *mcode = mfunc->member->code;

    int result = TCL_OK;

    int defargc;
    char **defargv = NULL;
    Tcl_Obj **defobjv = NULL;
    int configc = 0;
    ItclVarDefn **configVars = NULL;
    char **configVals = NULL;

    int vi, argsLeft;
    ItclClass *contextClass;
    ItclObject *contextObj;
    CompiledLocal *argPtr;
    ItclCallFrame *framePtr;
    Var *varPtr;
    Tcl_Obj *objPtr, *listPtr;
    char *value;

    framePtr = (ItclCallFrame *) _Tcl_GetCallFrame(interp, 0);
    framePtr->objc = objc;
    framePtr->objv = objv;  /* ref counts for args are incremented below */

    /*
     *  See if there is a current object context.  We may need
     *  it later on.
     */
    (void) Itcl_GetContext(interp, &contextClass, &contextObj);
    Tcl_ResetResult(interp);

    /*
     *  Match the actual arguments against the procedure's formal
     *  parameters to compute local variables.
     */
    varPtr = framePtr->compiledLocals;

    for (argsLeft=mcode->argcount, argPtr=mcode->arglist, objv++, objc--;
         argsLeft > 0;
         argPtr=argPtr->nextPtr, argsLeft--, ItclNextLocal(varPtr), objv++, objc--)
    {
        if (!TclIsVarArgument(argPtr)) {
            Tcl_Panic("local variable %s is not argument but should be",
                argPtr->name);
            return TCL_ERROR;
        }
        if (TclIsVarTemporary(argPtr)) {
            Tcl_Panic("local variable is temporary but should be an argument");
            return TCL_ERROR;
        }

        /*
         *  Handle the special case of the last formal being "args".
         *  When it occurs, assign it a list consisting of all the
         *  remaining actual arguments.
         */
        if ((argsLeft == 1) && (strcmp(argPtr->name, "args") == 0)) {
            if (objc < 0) objc = 0;

            listPtr = Tcl_NewListObj(objc, objv);
            ItclVarObjValue(varPtr) = listPtr;
            Tcl_IncrRefCount(listPtr); /* local var is a reference */
	    ItclClearVarUndefined(varPtr);
            objc = 0;

            break;
        }

        /*
         *  Handle the special case of the last formal being "config".
         *  When it occurs, treat all remaining arguments as public
         *  variable assignments.  Set the local "config" variable
         *  to the list of public variables assigned.
         */
        else if ( (argsLeft == 1) &&
                  (strcmp(argPtr->name, "config") == 0) &&
                  contextObj )
        {
            /*
             *  If this is not an old-style method, discourage against
             *  the use of the "config" argument.
             */
            if ((mfunc->member->flags & ITCL_OLD_STYLE) == 0) {
                Tcl_AppendResult(interp,
                    "\"config\" argument is an anachronism\n",
                    "[incr Tcl] no longer supports the \"config\" argument.\n",
                    "Instead, use the \"args\" argument and then use the\n",
                    "built-in configure method to handle args like this:\n",
                    "  eval configure $args",
                    (char*)NULL);
                result = TCL_ERROR;
                goto argErrors;
            }

            /*
             *  Otherwise, handle the "config" argument in the usual way...
             *   - parse all "-name value" assignments
             *   - set "config" argument to the list of variable names
             */
            if (objc > 0) {  /* still have some arguments left? */

                result = ItclParseConfig(interp, objc, objv, contextObj,
                    &configc, &configVars, &configVals);

                if (result != TCL_OK) {
                    goto argErrors;
                }

                listPtr = Tcl_NewListObj(0, (Tcl_Obj**)NULL);
                for (vi=0; vi < configc; vi++) {
                    objPtr = Tcl_NewStringObj(
                        configVars[vi]->member->classDefn->name, -1);
                    Tcl_AppendToObj(objPtr, "::", -1);
                    Tcl_AppendToObj(objPtr, configVars[vi]->member->name, -1);

                    Tcl_ListObjAppendElement(interp, listPtr, objPtr);
                }

                ItclVarObjValue(varPtr) = listPtr;
                Tcl_IncrRefCount(listPtr); /* local var is a reference */
		ItclClearVarUndefined(varPtr);

                objc = 0;  /* all remaining args handled */
            }

            else if (argPtr->defValuePtr) {
                value = Tcl_GetStringFromObj(argPtr->defValuePtr, (int*)NULL);

                result = Tcl_SplitList(interp, value, &defargc, &defargv);
                if (result != TCL_OK) {
                    goto argErrors;
                }
                defobjv = (Tcl_Obj**)ckalloc(
                    (unsigned)(defargc*sizeof(Tcl_Obj*))
                );
                for (vi=0; vi < defargc; vi++) {
                    objPtr = Tcl_NewStringObj(defargv[vi], -1);
                    Tcl_IncrRefCount(objPtr);
                    defobjv[vi] = objPtr;
                }

                result = ItclParseConfig(interp, defargc, defobjv, contextObj,
                    &configc, &configVars, &configVals);

                if (result != TCL_OK) {
                    goto argErrors;
                }

                listPtr = Tcl_NewListObj(0, (Tcl_Obj**)NULL);
                for (vi=0; vi < configc; vi++) {
                    objPtr = Tcl_NewStringObj(
                        configVars[vi]->member->classDefn->name, -1);
                    Tcl_AppendToObj(objPtr, "::", -1);
                    Tcl_AppendToObj(objPtr, configVars[vi]->member->name, -1);

                    Tcl_ListObjAppendElement(interp, listPtr, objPtr);
                }

                ItclVarObjValue(varPtr) = listPtr;
                Tcl_IncrRefCount(listPtr); /* local var is a reference */
		ItclClearVarUndefined(varPtr);
            }
            else {
                objPtr = Tcl_NewStringObj("", 0);
                ItclVarObjValue(varPtr) = objPtr;
                Tcl_IncrRefCount(objPtr); /* local var is a reference */
		ItclClearVarUndefined(varPtr);
            }
        }

        /*
         *  Resume the usual processing of arguments...
         */
        else if (objc > 0) {          /* take next arg as value */
            objPtr = *objv;
            ItclVarObjValue(varPtr) = objPtr;
	    ItclClearVarUndefined(varPtr);
            Tcl_IncrRefCount(objPtr);  /* local var is a reference */
        }
        else if (argPtr->defValuePtr) {    /* ...or use default value */
            objPtr = argPtr->defValuePtr;
            ItclVarObjValue(varPtr) = objPtr;
	    ItclClearVarUndefined(varPtr);
            Tcl_IncrRefCount(objPtr);  /* local var is a reference */
        }
        else {
            if (mfunc) {
                objPtr = Tcl_GetObjResult(interp);
                Tcl_AppendToObj(objPtr, "wrong # args: should be \"", -1);
                Itcl_GetMemberFuncUsage(mfunc, contextObj, objPtr);
                Tcl_AppendToObj(objPtr, "\"", -1);
            } else {
                Tcl_AppendResult(interp,
                    "no value given for parameter \"", argPtr->name, "\"",
                    (char*)NULL);
            }
            result = TCL_ERROR;
            goto argErrors;
        }
    }

    if (objc > 0) {
        if (mfunc) {
            objPtr = Tcl_GetObjResult(interp);
            Tcl_AppendToObj(objPtr, "wrong # args: should be \"", -1);
            Itcl_GetMemberFuncUsage(mfunc, contextObj, objPtr);
            Tcl_AppendToObj(objPtr, "\"", -1);
        } else {
            Tcl_AppendResult(interp,
                "too many arguments",
                (char*)NULL);
        }
        result = TCL_ERROR;
        goto argErrors;
    }

    /*
     *  Handle any "config" assignments.
     */
    if (configc > 0) {
        if (ItclHandleConfig(interp, configc, configVars, configVals,
                contextObj) != TCL_OK) {

            result = TCL_ERROR;
            goto argErrors;
        }
    }

    /*
     *  All arguments were successfully matched.
     */
    result = TCL_OK;

    /*
     *  If any errors were found, clean up and return error status.
     */
argErrors:
    if (defobjv) {
        for (vi=0; vi < defargc; vi++) {
            Tcl_DecrRefCount(defobjv[vi]);
        }
        ckfree((char*)defobjv);
    }
    if (defargv) {
        ckfree((char*)defargv);
    }
    if (configVars) {
        ckfree((char*)configVars);
    }
    if (configVals) {
        ckfree((char*)configVals);
    }
    return result;
}


/*
 * ------------------------------------------------------------------------
 *  ItclParseConfig()
 *
 *  Parses a set of arguments as "-variable value" assignments.
 *  Interprets all variable names in the most-specific class scope,
 *  so that an inherited method with a "config" parameter will work
 *  correctly.  Returns a list of public variable names and their
 *  corresponding values; both lists should passed to ItclHandleConfig()
 *  to perform assignments, and freed when no longer in use.  Returns a
 *  status TCL_OK/TCL_ERROR and returns error messages in the interpreter.
 * ------------------------------------------------------------------------
 */
static int
ItclParseConfig(interp, objc, objv, contextObj, rargc, rvars, rvals)
    Tcl_Interp *interp;      /* interpreter */
    int objc;                /* number of arguments */
    Tcl_Obj *CONST objv[];   /* argument objects */
    ItclObject *contextObj;  /* object whose public vars are being config'd */
    int *rargc;              /* return: number of variables accessed */
    ItclVarDefn ***rvars;    /* return: list of variables */
    char ***rvals;           /* return: list of values */
{
    int result = TCL_OK;
    ItclVarLookup *vlookup;
    Tcl_HashEntry *entry;
    char *varName, *value;

    if (objc < 0) objc = 0;
    *rargc = 0;
    *rvars = (ItclVarDefn**)ckalloc((unsigned)(objc*sizeof(ItclVarDefn*)));
    *rvals = (char**)ckalloc((unsigned)(objc*sizeof(char*)));

    while (objc-- > 0) {
        /*
         *  Next argument should be "-variable"
         */
        varName = Tcl_GetStringFromObj(*objv, (int*)NULL);
        if (*varName != '-') {
            Tcl_AppendResult(interp,
                "syntax error in config assignment \"",
                varName, "\": should be \"-variable value\"",
                (char*)NULL);
            result = TCL_ERROR;
            break;
        }
        else if (objc-- <= 0) {
            Tcl_AppendResult(interp,
                "syntax error in config assignment \"",
                varName, "\": should be \"-variable value\" (missing value)",
                (char*)NULL);
            result = TCL_ERROR;
            break;
        }

        entry = Tcl_FindHashEntry(&contextObj->classDefn->resolveVars,
            varName+1);

        if (entry) {
            vlookup = (ItclVarLookup*)Tcl_GetHashValue(entry);
            value = Tcl_GetStringFromObj(*(objv+1), (int*)NULL);

            (*rvars)[*rargc] = vlookup->vdefn;  /* variable definition */
            (*rvals)[*rargc] = value;           /* config value */
            (*rargc)++;
            objv += 2;
        }
        else {
            Tcl_AppendResult(interp,
                "syntax error in config assignment \"",
                varName, "\": unrecognized variable",
                (char*)NULL);
            result = TCL_ERROR;
            break;
        }
    }
    return result;
}

/*
 * ------------------------------------------------------------------------
 *  ItclHandleConfig()
 *
 *  Handles the assignment of "config" values to public variables.
 *  The list of assignments is parsed in ItclParseConfig(), but the
 *  actual assignments are performed here.  If the variables have any
 *  associated "config" code, it is invoked here as well.  If errors
 *  are detected during assignment or "config" code execution, the
 *  variable is set back to its previous value and an error is returned.
 *
 *  Returns a status TCL_OK/TCL_ERROR, and returns any error messages
 *  in the given interpreter.
 * ------------------------------------------------------------------------
 */
static int
ItclHandleConfig(interp, argc, vars, vals, contextObj)
    Tcl_Interp *interp;      /* interpreter currently in control */
    int argc;                /* number of assignments */
    ItclVarDefn **vars;      /* list of public variable definitions */
    char **vals;             /* list of public variable values */
    ItclObject *contextObj;  /* object whose public vars are being config'd */
{
    int result = TCL_OK;

    int i;
    CONST char *val;
    Tcl_DString lastval;
    ItclContext context;
    Itcl_CallFrame *oldFramePtr, *uplevelFramePtr;

    Tcl_DStringInit(&lastval);

    /*
     *  All "config" assignments are performed in the most-specific
     *  class scope, so that inherited methods with "config" arguments
     *  will work correctly.
     */
    result = Itcl_PushContext(interp, (ItclMember*)NULL,
        contextObj->classDefn, contextObj, &context);

    if (result != TCL_OK) {
        return TCL_ERROR;
    }

    /*
     *  Perform each assignment and execute the "config" code
     *  associated with each variable.  If any errors are encountered,
     *  set the variable back to its previous value, and return an error.
     */
    for (i=0; i < argc; i++) {
        val = Tcl_GetVar2(interp, vars[i]->member->fullname, (char*)NULL, 0);
        if (!val) {
            val = "";
        }
        Tcl_DStringSetLength(&lastval, 0);
        Tcl_DStringAppend(&lastval, val, -1);

        /*
         *  Set the variable to the specified value.
         */
        if (!Tcl_SetVar2(interp, vars[i]->member->fullname, (char*)NULL,
            vals[i], 0)) {

            char msg[256];
            sprintf(msg, "\n    (while configuring public variable \"%.100s\")", vars[i]->member->fullname);
            Tcl_AddErrorInfo(interp, msg);
            result = TCL_ERROR;
            break;
        }

        /*
         *  If the variable has a "config" condition, then execute it.
         *  If it fails, put the variable back the way it was and return
         *  an error.
         *
         *  TRICKY NOTE:  Be careful to evaluate the code one level
         *    up in the call stack, so that it's executed in the
         *    calling context, and not in the context that we've
         *    set up for public variable access.
         */
        if (vars[i]->member->code) {

            uplevelFramePtr = _Tcl_GetCallFrame(interp, 1);
            oldFramePtr = _Tcl_ActivateCallFrame(interp, uplevelFramePtr);

            result = Itcl_EvalMemberCode(interp, (ItclMemberFunc*)NULL,
                vars[i]->member, contextObj, 0, (Tcl_Obj* CONST*)NULL);

            (void) _Tcl_ActivateCallFrame(interp, oldFramePtr);

            if (result != TCL_OK) {
                char msg[256];
                sprintf(msg, "\n    (while configuring public variable \"%.100s\")", vars[i]->member->fullname);
                Tcl_AddErrorInfo(interp, msg);
                Tcl_SetVar2(interp, vars[i]->member->fullname, (char*)NULL,
                    Tcl_DStringValue(&lastval), 0);
                break;
            }
        }
    }

    /*
     *  Clean up and return.
     */
    Itcl_PopContext(interp, &context);
    Tcl_DStringFree(&lastval);

    return result;
}


/*
 * ------------------------------------------------------------------------
 *  Itcl_ConstructBase()
 *
 *  Usually invoked just before executing the body of a constructor
 *  when an object is first created.  This procedure makes sure that
 *  all base classes are properly constructed.  If an "initCode" fragment
 *  was defined with the constructor for the class, then it is invoked.
 *  After that, the list of base classes is checked for constructors
 *  that are defined but have not yet been invoked.  Each of these is
 *  invoked implicitly with no arguments.
 *
 *  Assumes that a local call frame is already installed, and that
 *  constructor arguments have already been matched and are sitting in
 *  this frame.  Returns TCL_OK on success; otherwise, this procedure
 *  returns TCL_ERROR, along with an error message in the interpreter.
 * ------------------------------------------------------------------------
 */
int
Itcl_ConstructBase(interp, contextObj, contextClass)
    Tcl_Interp *interp;       /* interpreter */
    ItclObject *contextObj;   /* object being constructed */
    ItclClass *contextClass;  /* current class being constructed */
{
    int result;
    Itcl_ListElem *elem;
    ItclClass *cdefn;
    Tcl_HashEntry *entry;

    /*
     *  If the class has an "initCode", invoke it in the current context.
     *
     *  TRICKY NOTE:
     *    This context is the call frame containing the arguments
     *    for the constructor.  The "initCode" makes sense right
     *    now--just before the body of the constructor is executed.
     */
    if (contextClass->initCode) {
        if (Tcl_EvalObj(interp, contextClass->initCode) != TCL_OK) {
            return TCL_ERROR;
        }
    }

    /*
     *  Scan through the list of base classes and see if any of these
     *  have not been constructed.  Invoke base class constructors
     *  implicitly, as needed.  Go through the list of base classes
     *  in reverse order, so that least-specific classes are constructed
     *  first.
     */
    elem = Itcl_LastListElem(&contextClass->bases);
    while (elem) {
        cdefn = (ItclClass*)Itcl_GetListValue(elem);

        if (!Tcl_FindHashEntry(contextObj->constructed, cdefn->name)) {

            result = Itcl_InvokeMethodIfExists(interp, "constructor",
                cdefn, contextObj, 0, (Tcl_Obj* CONST*)NULL);

            if (result != TCL_OK) {
                return TCL_ERROR;
            }

            /*
             *  The base class may not have a constructor, but its
             *  own base classes could have one.  If the constructor
             *  wasn't found in the last step, then other base classes
             *  weren't constructed either.  Make sure that all of its
             *  base classes are properly constructed.
             */
            entry = Tcl_FindHashEntry(&cdefn->functions, "constructor");
            if (entry == NULL) {
                result = Itcl_ConstructBase(interp, contextObj, cdefn);
                if (result != TCL_OK) {
                    return TCL_ERROR;
                }
            }
        }
        elem = Itcl_PrevListElem(elem);
    }
    return TCL_OK;
}


/*
 * ------------------------------------------------------------------------
 *  Itcl_InvokeMethodIfExists()
 *
 *  Looks for a particular method in the specified class.  If the
 *  method is found, it is invoked with the given arguments.  Any
 *  protection level (protected/private) for the method is ignored.
 *  If the method does not exist, this procedure does nothing.
 *
 *  This procedure is used primarily to invoke the constructor/destructor
 *  when an object is created/destroyed.
 *
 *  Returns TCL_OK on success; otherwise, this procedure returns
 *  TCL_ERROR along with an error message in the interpreter.
 * ------------------------------------------------------------------------
 */
int
Itcl_InvokeMethodIfExists(interp, name, contextClass, contextObj, objc, objv)
    Tcl_Interp *interp;       /* interpreter */
    CONST char *name;         /* name of desired method */
    ItclClass *contextClass;  /* current class being constructed */
    ItclObject *contextObj;   /* object being constructed */
    int objc;                 /* number of arguments */
    Tcl_Obj *CONST objv[];    /* argument objects */
{
    int result = TCL_OK;

    ItclMemberFunc *mfunc;
    ItclMember *member;
    Tcl_HashEntry *entry;
    Tcl_Obj *cmdlinePtr;
    int cmdlinec;
    Tcl_Obj **cmdlinev;

    /*
     *  Scan through the list of base classes and see if any of these
     *  have not been constructed.  Invoke base class constructors
     *  implicitly, as needed.  Go through the list of base classes
     *  in reverse order, so that least-specific classes are constructed
     *  first.
     */
    entry = Tcl_FindHashEntry(&contextClass->functions, name);

    if (entry) {
        mfunc  = (ItclMemberFunc*)Tcl_GetHashValue(entry);
        member = mfunc->member;

        /*
         *  Prepend the method name to the list of arguments.
         */
        cmdlinePtr = Itcl_CreateArgs(interp, name, objc, objv);

        (void) Tcl_ListObjGetElements((Tcl_Interp*)NULL, cmdlinePtr,
            &cmdlinec, &cmdlinev);

        /*
         *  Execute the code for the method.  Be careful to protect
         *  the method in case it gets deleted during execution.
         */
        Itcl_PreserveData((ClientData)mfunc);

        result = Itcl_EvalMemberCode(interp, mfunc, member,
            contextObj, cmdlinec, cmdlinev);

        result = Itcl_ReportFuncErrors(interp, mfunc,
            contextObj, result);

        Itcl_ReleaseData((ClientData)mfunc);
        Tcl_DecrRefCount(cmdlinePtr);
    }
    return result;
}


/*
 * ------------------------------------------------------------------------
 *  Itcl_ReportFuncErrors()
 *
 *  Used to interpret the status code returned when the body of a
 *  Tcl-style proc is executed.  Handles the "errorInfo" and "errorCode"
 *  variables properly, and adds error information into the interpreter
 *  if anything went wrong.  Returns a new status code that should be
 *  treated as the return status code for the command.
 *
 *  This same operation is usually buried in the Tcl InterpProc()
 *  procedure.  It is defined here so that it can be reused more easily.
 * ------------------------------------------------------------------------
 */
int
Itcl_ReportFuncErrors(interp, mfunc, contextObj, result)
    Tcl_Interp* interp;        /* interpreter being modified */
    ItclMemberFunc *mfunc;     /* command member that was invoked */
    ItclObject *contextObj;    /* object context for this command */
    int result;                /* integer status code from proc body */
{
    Interp* iPtr = (Interp*)interp;
    Tcl_Obj *objPtr;
    char num[20];

    if (result != TCL_OK) {
        if (result == TCL_RETURN) {
            result = TclUpdateReturnInfo(iPtr);
        }
        else if (result == TCL_ERROR) {
            objPtr = Tcl_NewStringObj("\n    ", -1);
            Tcl_IncrRefCount(objPtr);

            if (mfunc->member->flags & ITCL_CONSTRUCTOR) {
                Tcl_AppendToObj(objPtr, "while constructing object \"", -1);
                Tcl_GetCommandFullName(contextObj->classDefn->interp,
                    contextObj->accessCmd, objPtr);
                Tcl_AppendToObj(objPtr, "\" in ", -1);
                Tcl_AppendToObj(objPtr, mfunc->member->fullname, -1);
                if ((mfunc->member->code->flags & ITCL_IMPLEMENT_TCL) != 0) {
                    Tcl_AppendToObj(objPtr, " (", -1);
                }
            }

            else if (mfunc->member->flags & ITCL_DESTRUCTOR) {
                Tcl_AppendToObj(objPtr, "while deleting object \"", -1);
                Tcl_GetCommandFullName(contextObj->classDefn->interp,
                    contextObj->accessCmd, objPtr);
                Tcl_AppendToObj(objPtr, "\" in ", -1);
                Tcl_AppendToObj(objPtr, mfunc->member->fullname, -1);
                if ((mfunc->member->code->flags & ITCL_IMPLEMENT_TCL) != 0) {
                    Tcl_AppendToObj(objPtr, " (", -1);
                }
            }

            else {
                Tcl_AppendToObj(objPtr, "(", -1);

                if (contextObj && contextObj->accessCmd) {
                    Tcl_AppendToObj(objPtr, "object \"", -1);
                    Tcl_GetCommandFullName(contextObj->classDefn->interp,
                        contextObj->accessCmd, objPtr);
                    Tcl_AppendToObj(objPtr, "\" ", -1);
                }

                if ((mfunc->member->flags & ITCL_COMMON) != 0) {
                    Tcl_AppendToObj(objPtr, "procedure", -1);
                } else {
                    Tcl_AppendToObj(objPtr, "method", -1);
                }
                Tcl_AppendToObj(objPtr, " \"", -1);
                Tcl_AppendToObj(objPtr, mfunc->member->fullname, -1);
                Tcl_AppendToObj(objPtr, "\" ", -1);
            }

            if ((mfunc->member->code->flags & ITCL_IMPLEMENT_TCL) != 0) {
                Tcl_AppendToObj(objPtr, "body line ", -1);
                sprintf(num, "%d", iPtr->errorLine);
                Tcl_AppendToObj(objPtr, num, -1);
                Tcl_AppendToObj(objPtr, ")", -1);
            } else {
                Tcl_AppendToObj(objPtr, ")", -1);
            }

            Tcl_AddErrorInfo(interp, Tcl_GetStringFromObj(objPtr, (int*)NULL));
            Tcl_DecrRefCount(objPtr);
        }

        else if (result == TCL_BREAK) {
            Tcl_ResetResult(interp);
            Tcl_AppendToObj(Tcl_GetObjResult(interp),
                    "invoked \"break\" outside of a loop", -1);
            result = TCL_ERROR;
        }

        else if (result == TCL_CONTINUE) {
            Tcl_ResetResult(interp);
            Tcl_AppendToObj(Tcl_GetObjResult(interp),
                    "invoked \"continue\" outside of a loop", -1);
            result = TCL_ERROR;
        }
    }
    return result;
}
