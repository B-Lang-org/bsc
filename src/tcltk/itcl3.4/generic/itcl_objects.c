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
 *  This segment handles "objects" which are instantiated from class
 *  definitions.  Objects contain public/protected/private data members
 *  from all classes in a derivation hierarchy.
 *
 * ========================================================================
 *  AUTHOR:  Michael J. McLennan
 *           Bell Labs Innovations for Lucent Technologies
 *           mmclennan@lucent.com
 *           http://www.tcltk.com/itcl
 *
 *     RCS:  $Id: itcl_objects.c,v 1.17 2007/08/07 20:05:30 msofer Exp $
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
static void ItclReportObjectUsage _ANSI_ARGS_((Tcl_Interp *interp,
    ItclObject* obj));

static char* ItclTraceThisVar _ANSI_ARGS_((ClientData cdata,
    Tcl_Interp *interp, CONST char *name1, CONST char *name2, int flags));

static void ItclDestroyObject _ANSI_ARGS_((ClientData cdata));
static void ItclFreeObject _ANSI_ARGS_((char* cdata));

static int ItclDestructBase _ANSI_ARGS_((Tcl_Interp *interp,
    ItclObject* obj, ItclClass* cdefn, int flags));

static void ItclCreateObjVar _ANSI_ARGS_((Tcl_Interp *interp,
    ItclVarDefn* vdefn, ItclObject* obj));


/*
 * ------------------------------------------------------------------------
 *  Itcl_CreateObject()
 *
 *  Creates a new object instance belonging to the given class.
 *  Supports complex object names like "namesp::namesp::name" by
 *  following the namespace path and creating the object in the
 *  desired namespace.
 *
 *  Automatically creates and initializes data members, including the
 *  built-in protected "this" variable containing the object name.
 *  Installs an access command in the current namespace, and invokes
 *  the constructor to initialize the object.
 *
 *  If any errors are encountered, the object is destroyed and this
 *  procedure returns TCL_ERROR (along with an error message in the
 *  interpreter).  Otherwise, it returns TCL_OK, along with a pointer
 *  to the new object data in roPtr.
 * ------------------------------------------------------------------------
 */
int
Itcl_CreateObject(interp, name, cdefn, objc, objv, roPtr)
    Tcl_Interp *interp;      /* interpreter mananging new object */
    CONST char* name;        /* name of new object */
    ItclClass *cdefn;        /* class for new object */
    int objc;                /* number of arguments */
    Tcl_Obj *CONST objv[];   /* argument objects */
    ItclObject **roPtr;      /* returns: pointer to object data */
{
    ItclClass *cdefnPtr = (ItclClass*)cdefn;
    int result = TCL_OK;

    char *head, *tail;
    Tcl_DString buffer, objName;
    Tcl_Namespace *parentNs;
    ItclContext context;
    Tcl_Command cmd;
    ItclObject *newObj;
    ItclClass *cdPtr;
    ItclVarDefn *vdefn;
    ItclHierIter hier;
    Tcl_HashEntry *entry;
    Tcl_HashSearch place;
    int newEntry;
    Itcl_InterpState istate;

    /*
     *  If installing an object access command will clobber another
     *  command, signal an error.  Be careful to look for the object
     *  only in the current namespace context.  Otherwise, we might
     *  find a global command, but that wouldn't be clobbered!
     */
    cmd = Tcl_FindCommand(interp, (CONST84 char *)name,
	(Tcl_Namespace*)NULL, TCL_NAMESPACE_ONLY);

    if (cmd != NULL && !Itcl_IsStub(cmd)) {
        Tcl_AppendResult(interp,
		"command \"", name, "\" already exists in namespace \"",
		Tcl_GetCurrentNamespace(interp)->fullName, "\"",
		(char*) NULL);
        return TCL_ERROR;
    }

    /*
     *  Extract the namespace context and the simple object
     *  name for the new object.
     */
    Itcl_ParseNamespPath(name, &buffer, &head, &tail);
    if (head) {
        parentNs = Itcl_FindClassNamespace(interp, head);

        if (!parentNs) {
            Tcl_AppendResult(interp,
		    "namespace \"", head, "\" not found in context \"",
		    Tcl_GetCurrentNamespace(interp)->fullName, "\"",
		    (char *) NULL);
            Tcl_DStringFree(&buffer);
            return TCL_ERROR;
        }
    } else {
        parentNs = Tcl_GetCurrentNamespace(interp);
    }

    Tcl_DStringInit(&objName);
    if (parentNs != Tcl_GetGlobalNamespace(interp)) {
        Tcl_DStringAppend(&objName, parentNs->fullName, -1);
    }
    Tcl_DStringAppend(&objName, "::", -1);
    Tcl_DStringAppend(&objName, tail, -1);

    /*
     *  Create a new object and initialize it.
     */
    newObj = (ItclObject*)ckalloc(sizeof(ItclObject));
    newObj->classDefn = cdefnPtr;
    Itcl_PreserveData((ClientData)cdefnPtr);

    newObj->dataSize = cdefnPtr->numInstanceVars;
    newObj->data = (Var**)ckalloc((unsigned)(newObj->dataSize*sizeof(Var*)));

    newObj->constructed = (Tcl_HashTable*)ckalloc(sizeof(Tcl_HashTable));
    Tcl_InitHashTable(newObj->constructed, TCL_STRING_KEYS);
    newObj->destructed = NULL;

    /*
     *  Add a command to the current namespace with the object name.
     *  This is done before invoking the constructors so that the
     *  command can be used during construction to query info.
     */
    Itcl_PreserveData((ClientData)newObj);
    newObj->accessCmd = Tcl_CreateObjCommand(interp,
        Tcl_DStringValue(&objName), Itcl_HandleInstance,
        (ClientData)newObj, ItclDestroyObject);

    Itcl_PreserveData((ClientData)newObj);  /* while we're using this... */
    Itcl_EventuallyFree((ClientData)newObj, ItclFreeObject);

    Tcl_DStringFree(&buffer);
    Tcl_DStringFree(&objName);

    /*
     *  Install the class namespace and object context so that
     *  the object's data members can be initialized via simple
     *  "set" commands.
     */
    if (Itcl_PushContext(interp, (ItclMember*)NULL, cdefnPtr, newObj,
        &context) != TCL_OK) {

        return TCL_ERROR;
    }

    Itcl_InitHierIter(&hier, cdefn);

    cdPtr = Itcl_AdvanceHierIter(&hier);
    while (cdPtr != NULL) {
        entry = Tcl_FirstHashEntry(&cdPtr->variables, &place);
        while (entry) {
            vdefn = (ItclVarDefn*)Tcl_GetHashValue(entry);
            if ((vdefn->member->flags & ITCL_THIS_VAR) != 0) {
                if (cdPtr == cdefnPtr) {
                    ItclCreateObjVar(interp, vdefn, newObj);
                    Tcl_SetVar2(interp, "this", (char*)NULL, "", 0);
                    Tcl_TraceVar2(interp, "this", NULL,
                        TCL_TRACE_READS|TCL_TRACE_WRITES, ItclTraceThisVar,
                        (ClientData)newObj);
                }
            }
            else if ( (vdefn->member->flags & ITCL_COMMON) == 0) {
                ItclCreateObjVar(interp, vdefn, newObj);
            }
            entry = Tcl_NextHashEntry(&place);
        }
        cdPtr = Itcl_AdvanceHierIter(&hier);
    }
    Itcl_DeleteHierIter(&hier);

    Itcl_PopContext(interp, &context);  /* back to calling context */

    /*
     *  Now construct the object.  Look for a constructor in the
     *  most-specific class, and if there is one, invoke it.
     *  This will cause a chain reaction, making sure that all
     *  base classes constructors are invoked as well, in order
     *  from least- to most-specific.  Any constructors that are
     *  not called out explicitly in "initCode" code fragments are
     *  invoked implicitly without arguments.
     */
    result = Itcl_InvokeMethodIfExists(interp, "constructor",
        cdefn, newObj, objc, objv);

    /*
     *  If there is no constructor, construct the base classes
     *  in case they have constructors.  This will cause the
     *  same chain reaction.
     */
    if (!Tcl_FindHashEntry(&cdefn->functions, "constructor")) {
        result = Itcl_ConstructBase(interp, newObj, cdefn);
    }

    /*
     *  If construction failed, then delete the object access
     *  command.  This will destruct the object and delete the
     *  object data.  Be careful to save and restore the interpreter
     *  state, since the destructors may generate errors of their own.
     */
    if (result != TCL_OK) {
        istate = Itcl_SaveInterpState(interp, result);

	/* Bug 227824.
	 * The constructor may destroy the object, possibly indirectly
	 * through the destruction of the main widget in the iTk
	 * megawidget it tried to construct. If this happens we must
	 * not try to destroy the access command a second time.
	 */
	if (newObj->accessCmd != (Tcl_Command) NULL) {
	    Tcl_DeleteCommandFromToken(interp, newObj->accessCmd);
	    newObj->accessCmd = NULL;
	}
        result = Itcl_RestoreInterpState(interp, istate);
    }

    /*
     *  At this point, the object is fully constructed.
     *  Destroy the "constructed" table in the object data, since
     *  it is no longer needed.
     */
    Tcl_DeleteHashTable(newObj->constructed);
    ckfree((char*)newObj->constructed);
    newObj->constructed = NULL;

    /*
     *  Add it to the list of all known objects. The only
     *  tricky thing to watch out for is the case where the
     *  object deleted itself inside its own constructor.
     *  In that case, we don't want to add the object to
     *  the list of valid objects. We can determine that
     *  the object deleted itself by checking to see if
     *  its accessCmd member is NULL.
     */
    if (result == TCL_OK && (newObj->accessCmd != NULL))  {
        entry = Tcl_CreateHashEntry(&cdefnPtr->info->objects,
            (char*)newObj->accessCmd, &newEntry);

        Tcl_SetHashValue(entry, (ClientData)newObj);
    }

    /*
     *  Release the object.  If it was destructed above, it will
     *  die at this point.
     */
    Itcl_ReleaseData((ClientData)newObj);

    *roPtr = newObj;
    return result;
}


/*
 * ------------------------------------------------------------------------
 *  Itcl_DeleteObject()
 *
 *  Attempts to delete an object by invoking its destructor.
 *
 *  If the destructor is successful, then the object is deleted by
 *  removing its access command, and this procedure returns TCL_OK.
 *  Otherwise, the object will remain alive, and this procedure
 *  returns TCL_ERROR (along with an error message in the interpreter).
 * ------------------------------------------------------------------------
 */
int
Itcl_DeleteObject(interp, contextObj)
    Tcl_Interp *interp;      /* interpreter mananging object */
    ItclObject *contextObj;  /* object to be deleted */
{
    ItclClass *cdefnPtr = (ItclClass*)contextObj->classDefn;

    Tcl_HashEntry *entry;
    Command *cmdPtr;

    Itcl_PreserveData((ClientData)contextObj);

    /*
     *  Invoke the object's destructors.
     */
    if (Itcl_DestructObject(interp, contextObj, 0) != TCL_OK) {
        Itcl_ReleaseData((ClientData)contextObj);
        return TCL_ERROR;
    }

    /*
     *  Remove the object from the global list.
     */
    entry = Tcl_FindHashEntry(&cdefnPtr->info->objects,
        (char*)contextObj->accessCmd);

    if (entry) {
        Tcl_DeleteHashEntry(entry);
    }

    /*
     *  Change the object's access command so that it can be
     *  safely deleted without attempting to destruct the object
     *  again.  Then delete the access command.  If this is
     *  the last use of the object data, the object will die here.
     */
    cmdPtr = (Command*)contextObj->accessCmd;
    cmdPtr->deleteProc = Itcl_ReleaseData;

    Tcl_DeleteCommandFromToken(interp, contextObj->accessCmd);
    contextObj->accessCmd = NULL;

    Itcl_ReleaseData((ClientData)contextObj);  /* object should die here */

    return TCL_OK;
}


/*
 * ------------------------------------------------------------------------
 *  Itcl_DestructObject()
 *
 *  Invokes the destructor for a particular object.  Usually invoked
 *  by Itcl_DeleteObject() or Itcl_DestroyObject() as a part of the
 *  object destruction process.  If the ITCL_IGNORE_ERRS flag is
 *  included, all destructors are invoked even if errors are
 *  encountered, and the result will always be TCL_OK.
 *
 *  Returns TCL_OK on success, or TCL_ERROR (along with an error
 *  message in the interpreter) if anything goes wrong.
 * ------------------------------------------------------------------------
 */
int
Itcl_DestructObject(interp, contextObj, flags)
    Tcl_Interp *interp;      /* interpreter mananging new object */
    ItclObject *contextObj;  /* object to be destructed */
    int flags;               /* flags: ITCL_IGNORE_ERRS */
{
    int result;

    /*
     *  If there is a "destructed" table, then this object is already
     *  being destructed.  Flag an error, unless errors are being
     *  ignored.
     */
    if (contextObj->destructed) {
        if ((flags & ITCL_IGNORE_ERRS) == 0) {
            Tcl_AppendResult(interp,
		    "can't delete an object while it is being destructed",
		    (char*)NULL);
            return TCL_ERROR;
        }
        return TCL_OK;
    }

    /*
     *  Create a "destructed" table to keep track of which destructors
     *  have been invoked.  This is used in ItclDestructBase to make
     *  sure that all base class destructors have been called,
     *  explicitly or implicitly.
     */
    contextObj->destructed = (Tcl_HashTable*)ckalloc(sizeof(Tcl_HashTable));
    Tcl_InitHashTable(contextObj->destructed, TCL_STRING_KEYS);

    /*
     *  Destruct the object starting from the most-specific class.
     *  If all goes well, return the null string as the result.
     */
    result = ItclDestructBase(interp, contextObj, contextObj->classDefn, flags);

    if (result == TCL_OK) {
        Tcl_ResetResult(interp);
    }

    Tcl_DeleteHashTable(contextObj->destructed);
    ckfree((char*)contextObj->destructed);
    contextObj->destructed = NULL;

    return result;
}

/*
 * ------------------------------------------------------------------------
 *  ItclDestructBase()
 *
 *  Invoked by Itcl_DestructObject() to recursively destruct an object
 *  from the specified class level.  Finds and invokes the destructor
 *  for the specified class, and then recursively destructs all base
 *  classes.  If the ITCL_IGNORE_ERRS flag is included, all destructors
 *  are invoked even if errors are encountered, and the result will
 *  always be TCL_OK.
 *
 *  Returns TCL_OK on success, or TCL_ERROR (along with an error message
 *  in interp->result) on error.
 * ------------------------------------------------------------------------
 */
static int
ItclDestructBase(interp, contextObj, contextClass, flags)
    Tcl_Interp *interp;       /* interpreter */
    ItclObject *contextObj;   /* object being destructed */
    ItclClass *contextClass;  /* current class being destructed */
    int flags;                /* flags: ITCL_IGNORE_ERRS */
{
    int result;
    Itcl_ListElem *elem;
    ItclClass *cdefn;

    /*
     *  Look for a destructor in this class, and if found,
     *  invoke it.
     */
    if (!Tcl_FindHashEntry(contextObj->destructed, contextClass->fullname)) {

        result = Itcl_InvokeMethodIfExists(interp, "destructor",
            contextClass, contextObj, 0, (Tcl_Obj* CONST*)NULL);

        if (result != TCL_OK) {
            return TCL_ERROR;
        }
    }

    /*
     *  Scan through the list of base classes recursively and destruct
     *  them.  Traverse the list in normal order, so that we destruct
     *  from most- to least-specific.
     */
    elem = Itcl_FirstListElem(&contextClass->bases);
    while (elem) {
        cdefn = (ItclClass*)Itcl_GetListValue(elem);

        if (ItclDestructBase(interp, contextObj, cdefn, flags) != TCL_OK) {
            return TCL_ERROR;
        }
        elem = Itcl_NextListElem(elem);
    }

    /*
     *  Throw away any result from the destructors and return.
     */
    Tcl_ResetResult(interp);
    return TCL_OK;
}


/*
 * ------------------------------------------------------------------------
 *  Itcl_FindObject()
 *
 *  Searches for an object with the specified name, which have
 *  namespace scope qualifiers like "namesp::namesp::name", or may
 *  be a scoped value such as "namespace inscope ::foo obj".
 *
 *  If an error is encountered, this procedure returns TCL_ERROR
 *  along with an error message in the interpreter.  Otherwise, it
 *  returns TCL_OK.  If an object was found, "roPtr" returns a
 *  pointer to the object data.  Otherwise, it returns NULL.
 * ------------------------------------------------------------------------
 */
int
Itcl_FindObject(interp, name, roPtr)
    Tcl_Interp *interp;      /* interpreter containing this object */
    CONST char *name;        /* name of the object */
    ItclObject **roPtr;      /* returns: object data or NULL */
{
    Tcl_Namespace *contextNs = NULL;

    char *cmdName;
    Tcl_Command cmd;
    Command *cmdPtr;

    /*
     *  The object name may be a scoped value of the form
     *  "namespace inscope <namesp> <command>".  If it is,
     *  decode it.
     */
    if (Itcl_DecodeScopedCommand(interp, name, &contextNs, &cmdName)
        != TCL_OK) {
        return TCL_ERROR;
    }

    /*
     *  Look for the object's access command, and see if it has
     *  the appropriate command handler.
     */
    cmd = Tcl_FindCommand(interp, cmdName, contextNs, /* flags */ 0);
    if (cmd != NULL && Itcl_IsObject(cmd)) {
        cmdPtr = (Command*)cmd;
        *roPtr = (ItclObject*)cmdPtr->objClientData;
    }
    else {
        *roPtr = NULL;
    }

    ckfree(cmdName);

    return TCL_OK;
}


/*
 * ------------------------------------------------------------------------
 *  Itcl_IsObject()
 *
 *  Checks the given Tcl command to see if it represents an itcl object.
 *  Returns non-zero if the command is associated with an object.
 * ------------------------------------------------------------------------
 */
int
Itcl_IsObject(cmd)
    Tcl_Command cmd;         /* command being tested */
{
    Command *cmdPtr = (Command*)cmd;

    if (cmdPtr->deleteProc == ItclDestroyObject) {
        return 1;
    }

    /*
     *  This may be an imported command.  Try to get the real
     *  command and see if it represents an object.
     */
    cmdPtr = (Command*)TclGetOriginalCommand(cmd);
    if (cmdPtr && cmdPtr->deleteProc == ItclDestroyObject) {
        return 1;
    }
    return 0;
}


/*
 * ------------------------------------------------------------------------
 *  Itcl_ObjectIsa()
 *
 *  Checks to see if an object belongs to the given class.  An object
 *  "is-a" member of the class if the class appears anywhere in its
 *  inheritance hierarchy.  Returns non-zero if the object belongs to
 *  the class, and zero otherwise.
 * ------------------------------------------------------------------------
 */
int
Itcl_ObjectIsa(contextObj, cdefn)
    ItclObject *contextObj;   /* object being tested */
    ItclClass *cdefn;         /* class to test for "is-a" relationship */
{
    Tcl_HashEntry *entry;
    entry = Tcl_FindHashEntry(&contextObj->classDefn->heritage, (char*)cdefn);
    return (entry != NULL);
}


/*
 * ------------------------------------------------------------------------
 *  Itcl_HandleInstance()
 *
 *  Invoked by Tcl whenever the user issues a command associated with
 *  an object instance.  Handles the following syntax:
 *
 *    <objName> <method> <args>...
 *
 * ------------------------------------------------------------------------
 */
int
Itcl_HandleInstance(clientData, interp, objc, objv)
    ClientData clientData;   /* object definition */
    Tcl_Interp *interp;      /* current interpreter */
    int objc;                /* number of arguments */
    Tcl_Obj *CONST objv[];   /* argument objects */
{
    ItclObject *contextObj = (ItclObject*)clientData;

    int result;
    char *token;
    Tcl_HashEntry *entry;
    ItclMemberFunc *mfunc;
    ItclObjectInfo *info;
    ItclContext context;
    ItclCallFrame *framePtr;

    if (objc < 2) {
        Tcl_AppendResult(interp,
		"wrong # args: should be one of...",
		(char *) NULL);
        ItclReportObjectUsage(interp, contextObj);
        return TCL_ERROR;
    }

    /*
     *  Make sure that the specified operation is really an
     *  object method, and it is accessible.  If not, return usage
     *  information for the object.
     */
    token = Tcl_GetStringFromObj(objv[1], (int*)NULL);
    mfunc = NULL;

    entry = Tcl_FindHashEntry(&contextObj->classDefn->resolveCmds, token);
    if (entry) {
        mfunc = (ItclMemberFunc*)Tcl_GetHashValue(entry);

        if ((mfunc->member->flags & ITCL_COMMON) != 0) {
            mfunc = NULL;
        }
        else if (mfunc->member->protection != ITCL_PUBLIC) {
            Tcl_Namespace *contextNs = Itcl_GetTrueNamespace(interp,
                mfunc->member->classDefn->info);

            if (!Itcl_CanAccessFunc(mfunc, contextNs)) {
                mfunc = NULL;
            }
        }
    }

    if ( !mfunc && (*token != 'i' || strcmp(token,"info") != 0) ) {
        Tcl_AppendResult(interp,
		"bad option \"", token, "\": should be one of...",
		(char*)NULL);
        ItclReportObjectUsage(interp, contextObj);
        return TCL_ERROR;
    }

    /*
     *  Install an object context and invoke the method.
     *
     *  TRICKY NOTE:  We need to pass the object context into the
     *    method, but activating the context here puts us one level
     *    down, and when the method is called, it will activate its
     *    own context, putting us another level down.  If anyone
     *    were to execute an "uplevel" command in the method, they
     *    would notice the extra call frame.  So we mark this frame
     *    as "transparent" and Itcl_EvalMemberCode will automatically
     *    do an "uplevel" operation to correct the problem.
     */
    info = contextObj->classDefn->info;

    if (Itcl_PushContext(interp, (ItclMember*)NULL, contextObj->classDefn,
        contextObj, &context) != TCL_OK) {

        return TCL_ERROR;
    }

    framePtr = &context.frame;
    Itcl_PushStack((ClientData)framePtr, &info->transparentFrames);

    /* Bug 227824
     * The tcl core will blow up in 'TclLookupVar' if we don't reset
     * the 'isProcCallFrame'. This happens because without the
     * callframe refered to by 'framePtr' will be inconsistent
     * ('isProcCallFrame' set, but 'procPtr' not set).
     */
    if (*token == 'i' && strcmp(token,"info") == 0) {
        framePtr->isProcCallFrame = 0;
    }

    result = Itcl_EvalArgs(interp, objc-1, objv+1);

    Itcl_PopStack(&info->transparentFrames);
    Itcl_PopContext(interp, &context);

    return result;
}


/*
 * ------------------------------------------------------------------------
 *  Itcl_GetInstanceVar()
 *
 *  Returns the current value for an object data member.  The member
 *  name is interpreted with respect to the given class scope, which
 *  is usually the most-specific class for the object.
 *
 *  If successful, this procedure returns a pointer to a string value
 *  which remains alive until the variable changes it value.  If
 *  anything goes wrong, this returns NULL.
 * ------------------------------------------------------------------------
 */
CONST char*
Itcl_GetInstanceVar(interp, name, contextObj, contextClass)
    Tcl_Interp *interp;       /* current interpreter */
    CONST char *name;         /* name of desired instance variable */
    ItclObject *contextObj;   /* current object */
    ItclClass *contextClass;  /* name is interpreted in this scope */
{
    ItclContext context;
    CONST char *val;

    /*
     *  Make sure that the current namespace context includes an
     *  object that is being manipulated.
     */
    if (contextObj == NULL) {
        Tcl_ResetResult(interp);
        Tcl_SetResult(interp,
		"cannot access object-specific info without an object context",
		TCL_STATIC);
        return NULL;
    }

    /*
     *  Install the object context and access the data member
     *  like any other variable.
     */
    if (Itcl_PushContext(interp, (ItclMember*)NULL, contextClass,
        contextObj, &context) != TCL_OK) {

        return NULL;
    }

    val = Tcl_GetVar2(interp, (CONST84 char *)name, (char*)NULL,
	    TCL_LEAVE_ERR_MSG);
    Itcl_PopContext(interp, &context);

    return val;
}


/*
 * ------------------------------------------------------------------------
 *  ItclReportObjectUsage()
 *
 *  Appends information to the given interp summarizing the usage
 *  for all of the methods available for this object.  Useful when
 *  reporting errors in Itcl_HandleInstance().
 * ------------------------------------------------------------------------
 */
static void
ItclReportObjectUsage(interp, contextObj)
    Tcl_Interp *interp;      /* current interpreter */
    ItclObject *contextObj;  /* current object */
{
    ItclClass *cdefnPtr = (ItclClass*)contextObj->classDefn;
    int ignore = ITCL_CONSTRUCTOR | ITCL_DESTRUCTOR | ITCL_COMMON;

    int cmp;
    char *name;
    Itcl_List cmdList;
    Itcl_ListElem *elem;
    Tcl_HashEntry *entry;
    Tcl_HashSearch place;
    ItclMemberFunc *mfunc, *cmpDefn;
    Tcl_Obj *resultPtr;

    /*
     *  Scan through all methods in the virtual table and sort
     *  them in alphabetical order.  Report only the methods
     *  that have simple names (no ::'s) and are accessible.
     */
    Itcl_InitList(&cmdList);
    entry = Tcl_FirstHashEntry(&cdefnPtr->resolveCmds, &place);
    while (entry) {
        name  = Tcl_GetHashKey(&cdefnPtr->resolveCmds, entry);
        mfunc = (ItclMemberFunc*)Tcl_GetHashValue(entry);

        if (strstr(name,"::") || (mfunc->member->flags & ignore) != 0) {
            mfunc = NULL;
        }
        else if (mfunc->member->protection != ITCL_PUBLIC) {
            Tcl_Namespace *contextNs = Itcl_GetTrueNamespace(interp,
                mfunc->member->classDefn->info);

            if (!Itcl_CanAccessFunc(mfunc, contextNs)) {
                mfunc = NULL;
            }
        }

        if (mfunc) {
            elem = Itcl_FirstListElem(&cmdList);
            while (elem) {
                cmpDefn = (ItclMemberFunc*)Itcl_GetListValue(elem);
                cmp = strcmp(mfunc->member->name, cmpDefn->member->name);
                if (cmp < 0) {
                    Itcl_InsertListElem(elem, (ClientData)mfunc);
                    mfunc = NULL;
                    break;
                }
                else if (cmp == 0) {
                    mfunc = NULL;
                    break;
                }
                elem = Itcl_NextListElem(elem);
            }
            if (mfunc) {
                Itcl_AppendList(&cmdList, (ClientData)mfunc);
            }
        }
        entry = Tcl_NextHashEntry(&place);
    }

    /*
     *  Add a series of statements showing usage info.
     */
    resultPtr = Tcl_GetObjResult(interp);
    elem = Itcl_FirstListElem(&cmdList);
    while (elem) {
        mfunc = (ItclMemberFunc*)Itcl_GetListValue(elem);
        Tcl_AppendToObj(resultPtr, "\n  ", -1);
        Itcl_GetMemberFuncUsage(mfunc, contextObj, resultPtr);

        elem = Itcl_NextListElem(elem);
    }
    Itcl_DeleteList(&cmdList);
}


/*
 * ------------------------------------------------------------------------
 *  ItclTraceThisVar()
 *
 *  Invoked to handle read/write traces on the "this" variable built
 *  into each object.
 *
 *  On read, this procedure updates the "this" variable to contain the
 *  current object name.  This is done dynamically, since an object's
 *  identity can change if its access command is renamed.
 *
 *  On write, this procedure returns an error string, warning that
 *  the "this" variable cannot be set.
 * ------------------------------------------------------------------------
 */
/* ARGSUSED */
static char*
ItclTraceThisVar(cdata, interp, name1, name2, flags)
    ClientData cdata;	    /* object instance data */
    Tcl_Interp *interp;	    /* interpreter managing this variable */
    CONST char *name1;	    /* variable name */
    CONST char *name2;	    /* unused */
    int flags;		    /* flags indicating read/write */
{
    ItclObject *contextObj = (ItclObject*)cdata;
    char *objName;
    Tcl_Obj *objPtr;

    /*
     *  Handle read traces on "this"
     */
    if ((flags & TCL_TRACE_READS) != 0) {
        objPtr = Tcl_NewStringObj("", -1);
        Tcl_IncrRefCount(objPtr);

        if (contextObj->accessCmd) {
            Tcl_GetCommandFullName(contextObj->classDefn->interp,
                contextObj->accessCmd, objPtr);
        }

        objName = Tcl_GetString(objPtr);
        Tcl_SetVar(interp, (CONST84 char *)name1, objName, 0);

        Tcl_DecrRefCount(objPtr);
        return NULL;
    }

    /*
     *  Handle write traces on "this"
     */
    if ((flags & TCL_TRACE_WRITES) != 0) {
        return "variable \"this\" cannot be modified";
    }
    return NULL;
}


/*
 * ------------------------------------------------------------------------
 *  ItclDestroyObject()
 *
 *  Invoked when the object access command is deleted to implicitly
 *  destroy the object.  Invokes the object's destructors, ignoring
 *  any errors encountered along the way.  Removes the object from
 *  the list of all known objects and releases the access command's
 *  claim to the object data.
 *
 *  Note that the usual way to delete an object is via Itcl_DeleteObject().
 *  This procedure is provided as a back-up, to handle the case when
 *  an object is deleted by removing its access command.
 * ------------------------------------------------------------------------
 */
static void
ItclDestroyObject(cdata)
    ClientData cdata;  /* object instance data */
{
    ItclObject *contextObj = (ItclObject*)cdata;
    ItclClass *cdefnPtr = (ItclClass*)contextObj->classDefn;
    Tcl_HashEntry *entry;
    Itcl_InterpState istate;

    /*
     *  Attempt to destruct the object, but ignore any errors.
     */
    istate = Itcl_SaveInterpState(cdefnPtr->interp, 0);
    Itcl_DestructObject(cdefnPtr->interp, contextObj, ITCL_IGNORE_ERRS);
    Itcl_RestoreInterpState(cdefnPtr->interp, istate);

    /*
     *  Now, remove the object from the global object list.
     *  We're careful to do this here, after calling the destructors.
     *  Once the access command is nulled out, the "this" variable
     *  won't work properly.
     */
    if (contextObj->accessCmd) {
        entry = Tcl_FindHashEntry(&cdefnPtr->info->objects,
            (char*)contextObj->accessCmd);

        if (entry) {
            Tcl_DeleteHashEntry(entry);
        }
        contextObj->accessCmd = NULL;
    }

    Itcl_ReleaseData((ClientData)contextObj);
}


/*
 * ------------------------------------------------------------------------
 *  ItclFreeObject()
 *
 *  Deletes all instance variables and frees all memory associated with
 *  the given object instance.  This is usually invoked automatically
 *  by Itcl_ReleaseData(), when an object's data is no longer being used.
 * ------------------------------------------------------------------------
 */
static void
ItclFreeObject(cdata)
    char* cdata;  /* object instance data */
{
    ItclObject *contextObj = (ItclObject*)cdata;
    Tcl_Interp *interp = contextObj->classDefn->interp;

    int i;
    ItclClass *cdPtr;
    ItclHierIter hier;
    Tcl_HashSearch place;
    Tcl_HashEntry *entry;
    ItclVarDefn *vdefn;
    ItclContext context;
    Itcl_InterpState istate;

    /*
     *  Install the class namespace and object context so that
     *  the object's data members can be destroyed via simple
     *  "unset" commands.  This makes sure that traces work properly
     *  and all memory gets cleaned up.
     *
     *  NOTE:  Be careful to save and restore the interpreter state.
     *    Data can get freed in the middle of any operation, and
     *    we can't affort to clobber the interpreter with any errors
     *    from below.
     */
    istate = Itcl_SaveInterpState(interp, 0);

    /*
     *  Scan through all object-specific data members and destroy the
     *  actual variables that maintain the object state.  Do this
     *  by unsetting each variable, so that traces are fired off
     *  correctly.  Make sure that the built-in "this" variable is
     *  only destroyed once.  Also, be careful to activate the
     *  namespace for each class, so that private variables can
     *  be accessed.
     */
    Itcl_InitHierIter(&hier, contextObj->classDefn);
    cdPtr = Itcl_AdvanceHierIter(&hier);
    while (cdPtr != NULL) {

        if (Itcl_PushContext(interp, (ItclMember*)NULL, cdPtr,
            contextObj, &context) == TCL_OK) {

            entry = Tcl_FirstHashEntry(&cdPtr->variables, &place);
            while (entry) {
                vdefn = (ItclVarDefn*)Tcl_GetHashValue(entry);
                if ((vdefn->member->flags & ITCL_THIS_VAR) != 0) {
                    if (cdPtr == contextObj->classDefn) {
                        Tcl_UnsetVar2(interp, vdefn->member->fullname,
                            (char*)NULL, 0);
                    }
                }
                else if ((vdefn->member->flags & ITCL_COMMON) == 0) {
                    Tcl_UnsetVar2(interp, vdefn->member->fullname,
                        (char*)NULL, 0);
                }
                entry = Tcl_NextHashEntry(&place);
            }
            Itcl_PopContext(interp, &context);
        }

        cdPtr = Itcl_AdvanceHierIter(&hier);
    }
    Itcl_DeleteHierIter(&hier);

    /*
     *  Free the memory associated with object-specific variables.
     *  For normal variables this would be done automatically by
     *  CleanupVar() when the variable is unset.  But object-specific
     *  variables are protected by an extra reference count, and they
     *  must be deleted explicitly here.
     */
    for (i=0; i < contextObj->dataSize; i++) {
        if (contextObj->data[i]) {
            ckfree((char*)contextObj->data[i]);
        }
    }

    Itcl_RestoreInterpState(interp, istate);

    /*
     *  Free any remaining memory associated with the object.
     */
    ckfree((char*)contextObj->data);

    if (contextObj->constructed) {
        Tcl_DeleteHashTable(contextObj->constructed);
        ckfree((char*)contextObj->constructed);
    }
    if (contextObj->destructed) {
        Tcl_DeleteHashTable(contextObj->destructed);
        ckfree((char*)contextObj->destructed);
    }
    Itcl_ReleaseData((ClientData)contextObj->classDefn);

    ckfree((char*)contextObj);
}


/*
 * ------------------------------------------------------------------------
 *  ItclCreateObjVar()
 *
 *  Creates one variable acting as a data member for a specific
 *  object.  Initializes the variable according to its definition,
 *  and sets up its reference count so that it cannot be deleted
 *  by ordinary means.  Installs the new variable directly into
 *  the data array for the specified object.
 * ------------------------------------------------------------------------
 */
static void
ItclCreateObjVar(interp, vdefn, contextObj)
    Tcl_Interp* interp;       /* interpreter managing this object */
    ItclVarDefn* vdefn;       /* variable definition */
    ItclObject* contextObj;   /* object being updated */
{
    Var *varPtr;
    Tcl_HashEntry *entry;
    ItclVarLookup *vlookup;
    ItclContext context;

    varPtr = _TclNewVar();
#if ITCL_TCL_PRE_8_5
    if (itclOldRuntime) {    
	varPtr->name = vdefn->member->name;
	varPtr->nsPtr = (Namespace*)vdefn->member->classDefn->namesp;

	/*
	 *  NOTE:  Tcl reports a "dangling upvar" error for variables
	 *         with a null "hPtr" field.  Put something non-zero
	 *         in here to keep Tcl_SetVar2() happy.  The only time
	 *         this field is really used is it remove a variable
	 *         from the hash table that contains it in CleanupVar,
	 *         but since these variables are protected by their
	 *         higher refCount, they will not be deleted by CleanupVar
	 *         anyway.  These variables are unset and removed in
	 *         ItclFreeObject().
	 */
	varPtr->hPtr = (Tcl_HashEntry*)0x1;
	ItclVarRefCount(varPtr) = 1;  /* protect from being deleted */
    }
#endif

    /*
     *  Install the new variable in the object's data array.
     *  Look up the appropriate index for the object using
     *  the data table in the class definition.
     */
    entry = Tcl_FindHashEntry(&contextObj->classDefn->resolveVars,
        vdefn->member->fullname);

    if (entry) {
        vlookup = (ItclVarLookup*)Tcl_GetHashValue(entry);
        contextObj->data[vlookup->var.index] = varPtr;
    }

    /*
     *  If this variable has an initial value, initialize it
     *  here using a "set" command.
     *
     *  TRICKY NOTE:  We push an object context for the class that
     *    owns the variable, so that we don't have any trouble
     *    accessing it.
     */
    if (vdefn->init) {
        if (Itcl_PushContext(interp, (ItclMember*)NULL,
            vdefn->member->classDefn, contextObj, &context) == TCL_OK) {

            Tcl_SetVar2(interp, vdefn->member->fullname,
                (char*)NULL, vdefn->init, 0);
            Itcl_PopContext(interp, &context);
        }
    }
}


/*
 * ------------------------------------------------------------------------
 *  Itcl_ScopedVarResolver()
 *
 *  This procedure is installed to handle variable resolution throughout
 *  an entire interpreter.  It looks for scoped variable references of
 *  the form:
 *
 *    @itcl ::namesp::namesp::object variable
 *
 *  If a reference like this is recognized, this procedure finds the
 *  desired variable in the object and returns the variable, along with
 *  the status code TCL_OK.  If the variable does not start with
 *  "@itcl", this procedure returns TCL_CONTINUE, and variable
 *  resolution continues using the normal rules.  If anything goes
 *  wrong, this procedure returns TCL_ERROR, and access to the
 *  variable is denied.
 * ------------------------------------------------------------------------
 */
int
Itcl_ScopedVarResolver(interp, name, contextNs, flags, rPtr)
    Tcl_Interp *interp;        /* current interpreter */
    CONST char *name;                /* variable name being resolved */
    Tcl_Namespace *contextNs;  /* current namespace context */
    int flags;                 /* TCL_LEAVE_ERR_MSG => leave error message */
    Tcl_Var *rPtr;             /* returns: resolved variable */
{
    int namec;
    char **namev;
    Tcl_Interp *errs;
    Tcl_CmdInfo cmdInfo;
    ItclObject *contextObj;
    ItclVarLookup *vlookup;
    Tcl_HashEntry *entry;

    /*
     *  See if the variable starts with "@itcl".  If not, then
     *  let the variable resolution process continue.
     */
    if (*name != '@' || strncmp(name, "@itcl", 5) != 0) {
        return TCL_CONTINUE;
    }

    /*
     *  Break the variable name into parts and extract the object
     *  name and the variable name.
     */
    if (flags & TCL_LEAVE_ERR_MSG) {
        errs = interp;
    } else {
        errs = NULL;
    }

    if (Tcl_SplitList(errs, (CONST84 char *)name, &namec, &namev)
	    != TCL_OK) {
        return TCL_ERROR;
    }
    if (namec != 3) {
        if (errs) {
            Tcl_AppendResult(errs,
		    "scoped variable \"", name, "\" is malformed: ",
		    "should be: @itcl object variable",
		    (char*) NULL);
        }
        ckfree((char*)namev);
        return TCL_ERROR;
    }

    /*
     *  Look for the command representing the object and extract
     *  the object context.
     */
    if (!Tcl_GetCommandInfo(interp, namev[1], &cmdInfo)) {
        if (errs) {
            Tcl_AppendResult(errs,
                "can't resolve scoped variable \"", name, "\": ",
                "can't find object ", namev[1],
                (char*)NULL);
        }
        ckfree((char*)namev);
        return TCL_ERROR;
    }
    contextObj = (ItclObject*)cmdInfo.objClientData;

    /*
     *  Resolve the variable with respect to the most-specific
     *  class definition.
     */
    entry = Tcl_FindHashEntry(&contextObj->classDefn->resolveVars, namev[2]);
    if (!entry) {
        if (errs) {
            Tcl_AppendResult(errs,
                "can't resolve scoped variable \"", name, "\": ",
                "no such data member ", namev[2],
                (char*)NULL);
        }
        ckfree((char*)namev);
        return TCL_ERROR;
    }

    vlookup = (ItclVarLookup*)Tcl_GetHashValue(entry);
    *rPtr = (Tcl_Var) contextObj->data[vlookup->var.index];

    ckfree((char*)namev);
    return TCL_OK;
}
