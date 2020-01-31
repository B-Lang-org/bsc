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
 *  These procedures handle class definitions.  Classes are composed of
 *  data members (public/protected/common) and the member functions
 *  (methods/procs) that operate on them.  Each class has its own
 *  namespace which manages the class scope.
 *
 * ========================================================================
 *  AUTHOR:  Michael J. McLennan
 *           Bell Labs Innovations for Lucent Technologies
 *           mmclennan@lucent.com
 *           http://www.tcltk.com/itcl
 *
 *     RCS:  $Id: itcl_class.c,v 1.24 2007/08/07 20:05:29 msofer Exp $
 * ========================================================================
 *           Copyright (c) 1993-1998  Lucent Technologies, Inc.
 * ------------------------------------------------------------------------
 * See the file "license.terms" for information on usage and redistribution
 * of this file, and for a DISCLAIMER OF ALL WARRANTIES.
 */
#include "itclInt.h"

/*
 * This structure is a subclass of Tcl_ResolvedVarInfo that contains the
 * ItclVarLookup info needed at runtime.
 */
typedef struct ItclResolvedVarInfo {
    Tcl_ResolvedVarInfo vinfo;        /* This must be the first element. */
    ItclVarLookup *vlookup;           /* Pointer to lookup info. */
} ItclResolvedVarInfo;

/*
 *  FORWARD DECLARATIONS
 */
static void ItclDestroyClass _ANSI_ARGS_((ClientData cdata));
static void ItclDestroyClassNamesp _ANSI_ARGS_((ClientData cdata));
static void ItclFreeClass _ANSI_ARGS_((char* cdata));

static Tcl_Var ItclClassRuntimeVarResolver _ANSI_ARGS_((
    Tcl_Interp *interp, Tcl_ResolvedVarInfo *vinfoPtr));

extern int itclCompatFlags;


/*
 * ------------------------------------------------------------------------
 *  Itcl_CreateClass()
 *
 *  Creates a namespace and its associated class definition data.
 *  If a namespace already exists with that name, then this routine
 *  returns TCL_ERROR, along with an error message in the interp.
 *  If successful, it returns TCL_OK and a pointer to the new class
 *  definition.
 * ------------------------------------------------------------------------
 */
int
Itcl_CreateClass(interp, path, info, rPtr)
    Tcl_Interp* interp;		/* interpreter that will contain new class */
    CONST char* path;		/* name of new class */
    ItclObjectInfo *info;	/* info for all known objects */
    ItclClass **rPtr;		/* returns: pointer to class definition */
{
    char *head, *tail;
    Tcl_DString buffer;
    Tcl_Command cmd;
    Tcl_Namespace *classNs;
    ItclClass *cdPtr;
    ItclVarDefn *vdefn;
    Tcl_HashEntry *entry;
    int newEntry;

    /*
     *  Make sure that a class with the given name does not
     *  already exist in the current namespace context.  If a
     *  namespace exists, that's okay.  It may have been created
     *  to contain stubs during a "namespace import" operation.
     *  We'll just replace the namespace data below with the
     *  proper class data.
     */
    classNs = Tcl_FindNamespace(interp, (CONST84 char *)path,
	    (Tcl_Namespace*)NULL, /* flags */ 0);

    if (classNs != NULL && Itcl_IsClassNamespace(classNs)) {
        Tcl_AppendResult(interp,
            "class \"", path, "\" already exists",
            (char*)NULL);
        return TCL_ERROR;
    }

    /*
     *  Make sure that a command with the given class name does not
     *  already exist in the current namespace.  This prevents the
     *  usual Tcl commands from being clobbered when a programmer
     *  makes a bogus call like "class info".
     */
    cmd = Tcl_FindCommand(interp, (CONST84 char *)path,
	    (Tcl_Namespace*)NULL, /* flags */ TCL_NAMESPACE_ONLY);

    if (cmd != NULL && !Itcl_IsStub(cmd)) {
        Tcl_AppendResult(interp,
            "command \"", path, "\" already exists",
            (char*)NULL);

        if (strstr(path,"::") == NULL) {
            Tcl_AppendResult(interp,
                " in namespace \"",
                Tcl_GetCurrentNamespace(interp)->fullName, "\"",
                (char*)NULL);
        }
        return TCL_ERROR;
    }

    /*
     *  Make sure that the class name does not have any goofy
     *  characters:
     *
     *    .  =>  reserved for member access like:  class.publicVar
     */
    Itcl_ParseNamespPath(path, &buffer, &head, &tail);

    if (strstr(tail,".")) {
        Tcl_AppendResult(interp,
            "bad class name \"", tail, "\"",
            (char*)NULL);
        Tcl_DStringFree(&buffer);
        return TCL_ERROR;
    }
    Tcl_DStringFree(&buffer);

    /*
     *  Allocate class definition data.
     */
    cdPtr = (ItclClass*)ckalloc(sizeof(ItclClass));
    cdPtr->name = NULL;
    cdPtr->fullname = NULL;
    cdPtr->interp = interp;
    cdPtr->info = info;  Itcl_PreserveData((ClientData)info);
    cdPtr->namesp = NULL;
    cdPtr->accessCmd = NULL;

    Tcl_InitHashTable(&cdPtr->variables, TCL_STRING_KEYS);
    Tcl_InitHashTable(&cdPtr->functions, TCL_STRING_KEYS);

    cdPtr->numInstanceVars = 0;
    Tcl_InitHashTable(&cdPtr->resolveVars, TCL_STRING_KEYS);
    Tcl_InitHashTable(&cdPtr->resolveCmds, TCL_STRING_KEYS);

    Itcl_InitList(&cdPtr->bases);
    Itcl_InitList(&cdPtr->derived);

    cdPtr->initCode = NULL;
    cdPtr->unique   = 0;
    cdPtr->flags    = 0;

    /*
     *  Initialize the heritage info--each class starts with its
     *  own class definition in the heritage.  Base classes are
     *  added to the heritage from the "inherit" statement.
     */
    Tcl_InitHashTable(&cdPtr->heritage, TCL_ONE_WORD_KEYS);
    (void) Tcl_CreateHashEntry(&cdPtr->heritage, (char*)cdPtr, &newEntry);

    /*
     *  Create a namespace to represent the class.  Add the class
     *  definition info as client data for the namespace.  If the
     *  namespace already exists, then replace any existing client
     *  data with the class data.
     */
    Itcl_PreserveData((ClientData)cdPtr);

    if (classNs == NULL) {
        classNs = Tcl_CreateNamespace(interp, (CONST84 char *)path,
            (ClientData)cdPtr, ItclDestroyClassNamesp);
    }
    else {
        if (classNs->clientData && classNs->deleteProc) {
            (*classNs->deleteProc)(classNs->clientData);
        }
        classNs->clientData = (ClientData)cdPtr;
        classNs->deleteProc = ItclDestroyClassNamesp;
    }

    Itcl_EventuallyFree((ClientData)cdPtr, ItclFreeClass);

    if (classNs == NULL) {
        Itcl_ReleaseData((ClientData)cdPtr);
        return TCL_ERROR;
    }

    cdPtr->namesp = classNs;

    cdPtr->name = (char*)ckalloc((unsigned)(strlen(classNs->name)+1));
    strcpy(cdPtr->name, classNs->name);

    cdPtr->fullname = (char*)ckalloc((unsigned)(strlen(classNs->fullName)+1));
    strcpy(cdPtr->fullname, classNs->fullName);

    /*
     *  Add special name resolution procedures to the class namespace
     *  so that members are accessed according to the rules for
     *  [incr Tcl].
     */
    Tcl_SetNamespaceResolvers(classNs,
	    (Tcl_ResolveCmdProc*)Itcl_ClassCmdResolver,
	    (Tcl_ResolveVarProc*)Itcl_ClassVarResolver,
	    (Tcl_ResolveCompiledVarProc*)Itcl_ClassCompiledVarResolver);

    /*
     *  Add the built-in "this" variable to the list of data members.
     */
    (void) Itcl_CreateVarDefn(interp, cdPtr, "this",
        (char*)NULL, (char*)NULL, &vdefn);

    vdefn->member->protection = ITCL_PROTECTED;  /* always "protected" */
    vdefn->member->flags |= ITCL_THIS_VAR;       /* mark as "this" variable */

    entry = Tcl_CreateHashEntry(&cdPtr->variables, "this", &newEntry);
    Tcl_SetHashValue(entry, (ClientData)vdefn);

    /*
     *  Create a command in the current namespace to manage the class:
     *    <className>
     *    <className> <objName> ?<constructor-args>?
     */
    Itcl_PreserveData((ClientData)cdPtr);

    cdPtr->accessCmd = Tcl_CreateObjCommand(interp,
        cdPtr->fullname, Itcl_HandleClass,
        (ClientData)cdPtr, ItclDestroyClass);

    *rPtr = cdPtr;
    return TCL_OK;
}


/*
 * ------------------------------------------------------------------------
 *  Itcl_DeleteClass()
 *
 *  Deletes a class by deleting all derived classes and all objects in
 *  that class, and finally, by destroying the class namespace.  This
 *  procedure provides a friendly way of doing this.  If any errors
 *  are detected along the way, the process is aborted.
 *
 *  Returns TCL_OK if successful, or TCL_ERROR (along with an error
 *  message in the interpreter) if anything goes wrong.
 * ------------------------------------------------------------------------
 */
int
Itcl_DeleteClass(interp, cdefnPtr)
    Tcl_Interp *interp;     /* interpreter managing this class */
    ItclClass *cdefnPtr;    /* class namespace */
{
    ItclClass *cdPtr = NULL;

    Itcl_ListElem *elem;
    ItclObject *contextObj;
    Tcl_HashEntry *entry;
    Tcl_HashSearch place;
    Tcl_DString buffer;

    /*
     *  Destroy all derived classes, since these lose their meaning
     *  when the base class goes away.  If anything goes wrong,
     *  abort with an error.
     *
     *  TRICKY NOTE:  When a derived class is destroyed, it
     *    automatically deletes itself from the "derived" list.
     */
    elem = Itcl_FirstListElem(&cdefnPtr->derived);
    while (elem) {
        cdPtr = (ItclClass*)Itcl_GetListValue(elem);
        elem = Itcl_NextListElem(elem);  /* advance here--elem will go away */

        if (Itcl_DeleteClass(interp, cdPtr) != TCL_OK) {
            goto deleteClassFail;
        }
    }

    /*
     *  Scan through and find all objects that belong to this class.
     *  Note that more specialized objects have already been
     *  destroyed above, when derived classes were destroyed.
     *  Destroy objects and report any errors.
     */
    entry = Tcl_FirstHashEntry(&cdefnPtr->info->objects, &place);
    while (entry) {
        contextObj = (ItclObject*)Tcl_GetHashValue(entry);

        if (contextObj->classDefn == cdefnPtr) {
            if (Itcl_DeleteObject(interp, contextObj) != TCL_OK) {
                cdPtr = cdefnPtr;
                goto deleteClassFail;
            }

	    /*
	     * Fix 227804: Whenever an object to delete was found we
	     * have to reset the search to the beginning as the
	     * current entry in the search was deleted and accessing it
	     * is therefore not allowed anymore.
	     */

	    entry = Tcl_FirstHashEntry(&cdefnPtr->info->objects, &place);
	    continue;
        }

        entry = Tcl_NextHashEntry(&place);
    }

    /*
     *  Destroy the namespace associated with this class.
     *
     *  TRICKY NOTE:
     *    The cleanup procedure associated with the namespace is
     *    invoked automatically.  It does all of the same things
     *    above, but it also disconnects this class from its
     *    base-class lists, and removes the class access command.
     */
    Tcl_DeleteNamespace(cdefnPtr->namesp);
    return TCL_OK;

deleteClassFail:
    Tcl_DStringInit(&buffer);
    Tcl_DStringAppend(&buffer, "\n    (while deleting class \"", -1);
    Tcl_DStringAppend(&buffer, cdPtr->namesp->fullName, -1);
    Tcl_DStringAppend(&buffer, "\")", -1);
    Tcl_AddErrorInfo(interp, Tcl_DStringValue(&buffer));
    Tcl_DStringFree(&buffer);
    return TCL_ERROR;
}


/*
 * ------------------------------------------------------------------------
 *  ItclDestroyClass()
 *
 *  Invoked whenever the access command for a class is destroyed.
 *  Destroys the namespace associated with the class, which also
 *  destroys all objects in the class and all derived classes.
 *  Disconnects this class from the "derived" class lists of its
 *  base classes, and releases any claim to the class definition
 *  data.  If this is the last use of that data, the class will
 *  completely vanish at this point.
 * ------------------------------------------------------------------------
 */
static void
ItclDestroyClass(cdata)
    ClientData cdata;  /* class definition to be destroyed */
{
    ItclClass *cdefnPtr = (ItclClass*)cdata;
    cdefnPtr->accessCmd = NULL;

    Tcl_DeleteNamespace(cdefnPtr->namesp);
    Itcl_ReleaseData((ClientData)cdefnPtr);
}


/*
 * ------------------------------------------------------------------------
 *  ItclDestroyClassNamesp()
 *
 *  Invoked whenever the namespace associated with a class is destroyed.
 *  Destroys all objects associated with this class and all derived
 *  classes.  Disconnects this class from the "derived" class lists
 *  of its base classes, and removes the class access command.  Releases
 *  any claim to the class definition data.  If this is the last use
 *  of that data, the class will completely vanish at this point.
 * ------------------------------------------------------------------------
 */
static void
ItclDestroyClassNamesp(cdata)
    ClientData cdata;  /* class definition to be destroyed */
{
    ItclClass *cdefnPtr = (ItclClass*)cdata;
    ItclObject *contextObj;
    Itcl_ListElem *elem, *belem;
    ItclClass *cdPtr, *basePtr, *derivedPtr;
    Tcl_HashEntry *entry;
    Tcl_HashSearch place;

    /*
     *  Destroy all derived classes, since these lose their meaning
     *  when the base class goes away.
     *
     *  TRICKY NOTE:  When a derived class is destroyed, it
     *    automatically deletes itself from the "derived" list.
     */
    elem = Itcl_FirstListElem(&cdefnPtr->derived);
    while (elem) {
        cdPtr = (ItclClass*)Itcl_GetListValue(elem);
        Tcl_DeleteNamespace(cdPtr->namesp);

	/* As the first namespace is now destroyed we have to get the
         * new first element of the hash table. We cannot go to the
         * next element from the current one, because the current one
         * is deleted. itcl Patch #593112, for Bug #577719.
	 */

        elem = Itcl_FirstListElem(&cdefnPtr->derived);
    }

    /*
     *  Scan through and find all objects that belong to this class.
     *  Destroy them quietly by deleting their access command.
     */
    entry = Tcl_FirstHashEntry(&cdefnPtr->info->objects, &place);
    while (entry) {
        contextObj = (ItclObject*)Tcl_GetHashValue(entry);
        if (contextObj->classDefn == cdefnPtr) {
            Tcl_DeleteCommandFromToken(cdefnPtr->interp, contextObj->accessCmd);
	    /*
	     * Fix 227804: Whenever an object to delete was found we
	     * have to reset the search to the beginning as the
	     * current entry in the search was deleted and accessing it
	     * is therefore not allowed anymore.
	     */

	    entry = Tcl_FirstHashEntry(&cdefnPtr->info->objects, &place);
	    continue;
        }
        entry = Tcl_NextHashEntry(&place);
    }

    /*
     *  Next, remove this class from the "derived" list in
     *  all base classes.
     */
    belem = Itcl_FirstListElem(&cdefnPtr->bases);
    while (belem) {
        basePtr = (ItclClass*)Itcl_GetListValue(belem);

        elem = Itcl_FirstListElem(&basePtr->derived);
        while (elem) {
            derivedPtr = (ItclClass*)Itcl_GetListValue(elem);
            if (derivedPtr == cdefnPtr) {
                Itcl_ReleaseData( Itcl_GetListValue(elem) );
                elem = Itcl_DeleteListElem(elem);
            } else {
                elem = Itcl_NextListElem(elem);
            }
        }
        belem = Itcl_NextListElem(belem);
    }

    /*
     *  Next, destroy the access command associated with the class.
     */
    if (cdefnPtr->accessCmd) {
        Command *cmdPtr = (Command*)cdefnPtr->accessCmd;

        cmdPtr->deleteProc = Itcl_ReleaseData;
        Tcl_DeleteCommandFromToken(cdefnPtr->interp, cdefnPtr->accessCmd);
    }

    /*
     *  Release the namespace's claim on the class definition.
     */
    Itcl_ReleaseData((ClientData)cdefnPtr);
}


/*
 * ------------------------------------------------------------------------
 *  ItclFreeClass()
 *
 *  Frees all memory associated with a class definition.  This is
 *  usually invoked automatically by Itcl_ReleaseData(), when class
 *  data is no longer being used.
 * ------------------------------------------------------------------------
 */
static void
ItclFreeClass(cdata)
    char *cdata;  /* class definition to be destroyed */
{
    ItclClass *cdefnPtr = (ItclClass*)cdata;

    Itcl_ListElem *elem;
    Tcl_HashSearch place;
    Tcl_HashEntry *entry;
    ItclVarDefn *vdefn;
    ItclVarLookup *vlookup;
    VarInHash *varPtr;

    /*
     *  Tear down the list of derived classes.  This list should
     *  really be empty if everything is working properly, but
     *  release it here just in case.
     */
    elem = Itcl_FirstListElem(&cdefnPtr->derived);
    while (elem) {
        Itcl_ReleaseData( Itcl_GetListValue(elem) );
        elem = Itcl_NextListElem(elem);
    }
    Itcl_DeleteList(&cdefnPtr->derived);

    /*
     *  Tear down the variable resolution table.  Some records
     *  appear multiple times in the table (for x, foo::x, etc.)
     *  so each one has a reference count.
     */

    entry = Tcl_FirstHashEntry(&cdefnPtr->resolveVars, &place);
    while (entry) {
        vlookup = (ItclVarLookup*)Tcl_GetHashValue(entry);
        if (--vlookup->usage == 0) {
            /*
             *  If this is a common variable owned by this class,
             *  then release the class's hold on it.  If it's no
             *  longer being used, move it into a variable table
             *  for destruction.
             */
            if ( (vlookup->vdefn->member->flags & ITCL_COMMON) != 0 &&
                 vlookup->vdefn->member->classDefn == cdefnPtr ) {
                varPtr = (VarInHash*)vlookup->var.common;
                if (--ItclVarRefCount(varPtr) == 0) {
		    /*
		     * This is called after the namespace is already gone: the
		     * variable is already unset and ready to be freed.
		     */
		    
		    ckfree((char *)varPtr);
                }
            }
            ckfree((char*)vlookup);
        }
        entry = Tcl_NextHashEntry(&place);
    }
    Tcl_DeleteHashTable(&cdefnPtr->resolveVars);

    /*
     *  Tear down the virtual method table...
     */
    Tcl_DeleteHashTable(&cdefnPtr->resolveCmds);

    /*
     *  Delete all variable definitions.
     */
    entry = Tcl_FirstHashEntry(&cdefnPtr->variables, &place);
    while (entry) {
        vdefn = (ItclVarDefn*)Tcl_GetHashValue(entry);
        Itcl_DeleteVarDefn(vdefn);
        entry = Tcl_NextHashEntry(&place);
    }
    Tcl_DeleteHashTable(&cdefnPtr->variables);

    /*
     *  Delete all function definitions.
     */
    entry = Tcl_FirstHashEntry(&cdefnPtr->functions, &place);
    while (entry) {
        Itcl_ReleaseData( Tcl_GetHashValue(entry) );
        entry = Tcl_NextHashEntry(&place);
    }
    Tcl_DeleteHashTable(&cdefnPtr->functions);

    /*
     *  Release the claim on all base classes.
     */
    elem = Itcl_FirstListElem(&cdefnPtr->bases);
    while (elem) {
        Itcl_ReleaseData( Itcl_GetListValue(elem) );
        elem = Itcl_NextListElem(elem);
    }
    Itcl_DeleteList(&cdefnPtr->bases);
    Tcl_DeleteHashTable(&cdefnPtr->heritage);

    /*
     *  Free up the object initialization code.
     */
    if (cdefnPtr->initCode) {
        Tcl_DecrRefCount(cdefnPtr->initCode);
    }

    Itcl_ReleaseData((ClientData)cdefnPtr->info);

    ckfree(cdefnPtr->name);
    ckfree(cdefnPtr->fullname);

    ckfree((char*)cdefnPtr);
}


/*
 * ------------------------------------------------------------------------
 *  Itcl_IsClassNamespace()
 *
 *  Checks to see whether or not the given namespace represents an
 *  [incr Tcl] class.  Returns non-zero if so, and zero otherwise.
 * ------------------------------------------------------------------------
 */
int
Itcl_IsClassNamespace(namesp)
    Tcl_Namespace *namesp;  /* namespace being tested */
{
    Namespace *nsPtr = (Namespace*)namesp;

    if (nsPtr != NULL) {
        return (nsPtr->deleteProc == ItclDestroyClassNamesp);
    }
    return 0;
}


/*
 * ------------------------------------------------------------------------
 *  Itcl_IsClass()
 *
 *  Checks the given Tcl command to see if it represents an itcl class.
 *  Returns non-zero if the command is associated with a class.
 * ------------------------------------------------------------------------
 */
int
Itcl_IsClass(cmd)
    Tcl_Command cmd;         /* command being tested */
{
    Command *cmdPtr = (Command*)cmd;

    if (cmdPtr->deleteProc == ItclDestroyClass) {
        return 1;
    }

    /*
     *  This may be an imported command.  Try to get the real
     *  command and see if it represents a class.
     */
    cmdPtr = (Command*)TclGetOriginalCommand(cmd);
    if (cmdPtr && cmdPtr->deleteProc == ItclDestroyClass) {
        return 1;
    }
    return 0;
}


/*
 * ------------------------------------------------------------------------
 *  Itcl_FindClass()
 *
 *  Searches for the specified class in the active namespace.  If the
 *  class is found, this procedure returns a pointer to the class
 *  definition.  Otherwise, if the autoload flag is non-zero, an
 *  attempt will be made to autoload the class definition.  If it
 *  still can't be found, this procedure returns NULL, along with an
 *  error message in the interpreter.
 * ------------------------------------------------------------------------
 */
ItclClass*
Itcl_FindClass(interp, path, autoload)
    Tcl_Interp* interp;		/* interpreter containing class */
    CONST char* path;		/* path name for class */
    int autoload;		/* should class be loaded */
{
    Tcl_Namespace* classNs;

    /*
     *  Search for a namespace with the specified name, and if
     *  one is found, see if it is a class namespace.
     */
    classNs = Itcl_FindClassNamespace(interp, path);

    if (classNs && Itcl_IsClassNamespace(classNs)) {
        return (ItclClass*)classNs->clientData;
    }

    /*
     *  If the autoload flag is set, try to autoload the class
     *  definition.
     */
    if (autoload) {
        if (Tcl_VarEval(interp, "::auto_load ", path, (char*)NULL) != TCL_OK) {
            char msg[256];
            sprintf(msg, "\n    (while attempting to autoload class \"%.200s\")", path);
            Tcl_AddErrorInfo(interp, msg);
            return NULL;
        }
        Tcl_ResetResult(interp);

        classNs = Itcl_FindClassNamespace(interp, path);
        if (classNs && Itcl_IsClassNamespace(classNs)) {
            return (ItclClass*)classNs->clientData;
        }
    }

    Tcl_AppendResult(interp, "class \"", path, "\" not found in context \"",
        Tcl_GetCurrentNamespace(interp)->fullName, "\"",
        (char*)NULL);

    return NULL;
}

/*
 * ------------------------------------------------------------------------
 *  Itcl_FindClassNamespace()
 *
 *  Searches for the specified class namespace.  The normal Tcl procedure
 *  Tcl_FindNamespace also searches for namespaces, but only in the
 *  current namespace context.  This makes it hard to find one class
 *  from within another.  For example, suppose. you have two namespaces
 *  Foo and Bar.  If you're in the context of Foo and you look for
 *  Bar, you won't find it with Tcl_FindNamespace.  This behavior is
 *  okay for namespaces, but wrong for classes.
 *
 *  This procedure search for a class namespace.  If the name is
 *  absolute (i.e., starts with "::"), then that one name is checked,
 *  and the class is either found or not.  But if the name is relative,
 *  it is sought in the current namespace context and in the global
 *  context, just like the normal command lookup.
 *
 *  This procedure returns a pointer to the desired namespace, or
 *  NULL if the namespace was not found.
 * ------------------------------------------------------------------------
 */
Tcl_Namespace*
Itcl_FindClassNamespace(interp, path)
    Tcl_Interp* interp;        /* interpreter containing class */
    CONST char* path;                /* path name for class */
{
    Tcl_Namespace* contextNs = Tcl_GetCurrentNamespace(interp);
    Tcl_Namespace* classNs;
    Tcl_DString buffer;

    /*
     *  Look up the namespace.  If the name is not absolute, then
     *  see if it's the current namespace, and try the global
     *  namespace as well.
     */
    classNs = Tcl_FindNamespace(interp, (CONST84 char *)path,
	    (Tcl_Namespace*)NULL, /* flags */ 0);

    if ( !classNs && contextNs->parentPtr != NULL &&
         !(*path == ':' && *(path+1) == ':') ) {

        if (strcmp(contextNs->name, path) == 0) {
            classNs = contextNs;
        }
        else {
            Tcl_DStringInit(&buffer);
            Tcl_DStringAppend(&buffer, "::", -1);
            Tcl_DStringAppend(&buffer, path, -1);

            classNs = Tcl_FindNamespace(interp, Tcl_DStringValue(&buffer),
                (Tcl_Namespace*)NULL, /* flags */ 0);

            Tcl_DStringFree(&buffer);
        }
    }
    return classNs;
}


/*
 * ------------------------------------------------------------------------
 *  Itcl_HandleClass()
 *
 *  Invoked by Tcl whenever the user issues the command associated with
 *  a class name.  Handles the following syntax:
 *
 *    <className>
 *    <className> <objName> ?<args>...?
 *
 *  Without any arguments, the command does nothing.  In the olden days,
 *  this allowed the class name to be invoked by itself to prompt the
 *  autoloader to load the class definition.  Today, this behavior is
 *  retained for backward compatibility with old releases.
 *
 *  If arguments are specified, then this procedure creates a new
 *  object named <objName> in the appropriate class.  Note that if
 *  <objName> contains "#auto", that part is automatically replaced
 *  by a unique string built from the class name.
 * ------------------------------------------------------------------------
 */
int
Itcl_HandleClass(clientData, interp, objc, objv)
    ClientData clientData;   /* class definition */
    Tcl_Interp *interp;      /* current interpreter */
    int objc;                /* number of arguments */
    Tcl_Obj *CONST objv[];   /* argument objects */
{
    ItclClass *cdefnPtr = (ItclClass*)clientData;
    int result = TCL_OK;

    Tcl_DString buffer;  /* buffer used to build object names */
    char *token, *objName, *match;

    ItclObject *newObj;
    Itcl_CallFrame frame;

    /*
     *  If the command is invoked without an object name, then do nothing.
     *  This used to support autoloading--that the class name could be
     *  invoked as a command by itself, prompting the autoloader to
     *  load the class definition.  We retain the behavior here for
     *  backward-compatibility with earlier releases.
     */
    if (objc == 1) {
        return TCL_OK;
    }

    /*
     *  If the object name is "::", and if this is an old-style class
     *  definition, then treat the remaining arguments as a command
     *  in the class namespace.  This used to be the way of invoking
     *  a class proc, but the new syntax is "class::proc" (without
     *  spaces).
     */
    token = Tcl_GetStringFromObj(objv[1], (int*)NULL);
    if ((*token == ':') && (strcmp(token,"::") == 0) && (objc > 2)) {
        if ((cdefnPtr->flags & ITCL_OLD_STYLE) != 0) {

            result = Tcl_PushCallFrame(interp, (Tcl_CallFrame *) &frame,
                 cdefnPtr->namesp, /* isProcCallFrame */ 0);

            if (result != TCL_OK) {
                return result;
            }
            result = Itcl_EvalArgs(interp, objc-2, objv+2);

            Tcl_PopCallFrame(interp);
            return result;
        }

        /*
         *  If this is not an old-style class, then return an error
         *  describing the syntax change.
         */
        Tcl_AppendResult(interp,
            "syntax \"class :: proc\" is an anachronism\n",
            "[incr Tcl] no longer supports this syntax.\n",
            "Instead, remove the spaces from your procedure invocations:\n",
            "  ",
            Tcl_GetStringFromObj(objv[0], (int*)NULL), "::",
            Tcl_GetStringFromObj(objv[2], (int*)NULL), " ?args?",
            (char*)NULL);
        return TCL_ERROR;
    }

    /*
     *  Otherwise, we have a proper object name.  Create a new instance
     *  with that name.  If the name contains "#auto", replace this with
     *  a uniquely generated string based on the class name.
     */
    Tcl_DStringInit(&buffer);
    objName = token;
    match = strstr(token, "#auto");
    if (match != NULL) {
	int len;
	char unique[TCL_INTEGER_SPACE]; /* for unique part of object names */
	Tcl_CmdInfo dummy;
	Tcl_UniChar ch;

	Tcl_DStringAppend(&buffer, token, (match - token));

	/*
	 * Only lowercase the first char of $class, per itcl #auto semantics
	 */
	len = Tcl_UtfToUniChar(cdefnPtr->name, &ch);
	ch = Tcl_UniCharToLower(ch);
	Tcl_UniCharToUtfDString(&ch, 1, &buffer);
	Tcl_DStringAppend(&buffer, cdefnPtr->name + len, -1);

	/*
	 *  Substitute a unique part in for "#auto", and keep
	 *  incrementing a counter until a valid name is found.
	 */
	len = Tcl_DStringLength(&buffer);
	do {
	    sprintf(unique, "%d", cdefnPtr->unique++);

	    Tcl_DStringTrunc(&buffer, len);
	    Tcl_DStringAppend(&buffer, unique, -1);
	    Tcl_DStringAppend(&buffer, match+5, -1);

	    objName = Tcl_DStringValue(&buffer);

	    /*
	     * [Fix 227811] Check for any command with the given name, not
	     * only objects.
	     */

	    if (Tcl_GetCommandInfo (interp, objName, &dummy) == 0) {
		break;  /* if an error is found, bail out! */
	    }
	} while (1);
    }

    /*
     *  Try to create a new object.  If successful, return the
     *  object name as the result of this command.
     */
    result = Itcl_CreateObject(interp, objName, cdefnPtr,
        objc-2, objv+2, &newObj);

    if (result == TCL_OK) {
        Tcl_SetObjResult(interp, Tcl_NewStringObj(objName, -1));
    }

    Tcl_DStringFree(&buffer);
    return result;
}


/*
 * ------------------------------------------------------------------------
 *  Itcl_ClassCmdResolver()
 *
 *  Used by the class namespaces to handle name resolution for all
 *  commands.  This procedure looks for references to class methods
 *  and procs, and returns TCL_OK along with the appropriate Tcl
 *  command in the rPtr argument.  If a particular command is private,
 *  this procedure returns TCL_ERROR and access to the command is
 *  denied.  If a command is not recognized, this procedure returns
 *  TCL_CONTINUE, and lookup continues via the normal Tcl name
 *  resolution rules.
 * ------------------------------------------------------------------------
 */
int
Itcl_ClassCmdResolver(interp, name, context, flags, rPtr)
    Tcl_Interp *interp;		/* current interpreter */
    CONST char* name;		/* name of the command being accessed */
    Tcl_Namespace *context;	/* namespace performing the resolution */
    int flags;			/* TCL_LEAVE_ERR_MSG => leave error messages
				 *   in interp if anything goes wrong */
    Tcl_Command *rPtr;		/* returns: resolved command */
{
    ItclClass *cdefn = (ItclClass*)context->clientData;

    Tcl_HashEntry *entry;
    ItclMemberFunc *mfunc;
    Command *cmdPtr;
    int isCmdDeleted;

    /*
     *  If the command is a member function, and if it is
     *  accessible, return its Tcl command handle.
     */
    entry = Tcl_FindHashEntry(&cdefn->resolveCmds, name);
    if (!entry) {
        return TCL_CONTINUE;
    }

    mfunc = (ItclMemberFunc*)Tcl_GetHashValue(entry);


    /*
     *  For protected/private functions, figure out whether or
     *  not the function is accessible from the current context.
     *
     *  TRICKY NOTE:  Use Itcl_GetTrueNamespace to determine
     *    the current context.  If the current call frame is
     *    "transparent", this handles it properly.
     */
    if (mfunc->member->protection != ITCL_PUBLIC) {
        context = Itcl_GetTrueNamespace(interp, cdefn->info);

        if (!Itcl_CanAccessFunc(mfunc, context)) {

            if ((flags & TCL_LEAVE_ERR_MSG) != 0) {
                Tcl_AppendResult(interp,
                    "can't access \"", name, "\": ",
                    Itcl_ProtectionStr(mfunc->member->protection),
                    " variable",
                    (char*)NULL);
            }
            return TCL_ERROR;
        }
    }

    /*
     *  Looks like we found an accessible member function.
     *
     *  TRICKY NOTE:  Check to make sure that the command handle
     *    is still valid.  If someone has deleted or renamed the
     *    command, it may not be.  This is just the time to catch
     *    it--as it is being resolved again by the compiler.
     */
    cmdPtr = (Command*)mfunc->accessCmd;
    
    /*
     * The following #if is needed so itcl can be compiled with
     * all versions of Tcl.  The integer "deleted" was renamed to
     * "flags" in tcl8.4a2.  This #if is also found in itcl_ensemble.c .
     * We're using a runtime check with itclCompatFlags to adjust for
     * the behavior of this change, too.
     *
     */
#if (TCL_MAJOR_VERSION == 8) && (TCL_MINOR_VERSION < 4)
#   define CMD_IS_DELETED 0x1  /* If someone ever changes this from tcl.h,
				* we must change our logic here, too */
	isCmdDeleted = (!cmdPtr ||
		(itclCompatFlags & ITCL_COMPAT_USECMDFLAGS ?
		(cmdPtr->deleted & CMD_IS_DELETED) :
		cmdPtr->deleted));
#else
	isCmdDeleted = (!cmdPtr ||
		(itclCompatFlags & ITCL_COMPAT_USECMDFLAGS ?
		(cmdPtr->flags & CMD_IS_DELETED) :
		cmdPtr->flags));
#endif

    if (isCmdDeleted) {
	mfunc->accessCmd = NULL;

	if ((flags & TCL_LEAVE_ERR_MSG) != 0) {
	    Tcl_AppendResult(interp,
		"can't access \"", name, "\": deleted or redefined\n",
		"(use the \"body\" command to redefine methods/procs)",
		(char*)NULL);
	}
	return TCL_ERROR;   /* disallow access! */
    }

    *rPtr = mfunc->accessCmd;
    return TCL_OK;
}


/*
 * ------------------------------------------------------------------------
 *  Itcl_ClassVarResolver()
 *
 *  Used by the class namespaces to handle name resolution for runtime
 *  variable accesses.  This procedure looks for references to both
 *  common variables and instance variables at runtime.  It is used as
 *  a second line of defense, to handle references that could not be
 *  resolved as compiled locals.
 *
 *  If a variable is found, this procedure returns TCL_OK along with
 *  the appropriate Tcl variable in the rPtr argument.  If a particular
 *  variable is private, this procedure returns TCL_ERROR and access
 *  to the variable is denied.  If a variable is not recognized, this
 *  procedure returns TCL_CONTINUE, and lookup continues via the normal
 *  Tcl name resolution rules.
 * ------------------------------------------------------------------------
 */
int
Itcl_ClassVarResolver(interp, name, context, flags, rPtr)
    Tcl_Interp *interp;       /* current interpreter */
    CONST char* name;	      /* name of the variable being accessed */
    Tcl_Namespace *context;   /* namespace performing the resolution */
    int flags;                /* TCL_LEAVE_ERR_MSG => leave error messages
                               *   in interp if anything goes wrong */
    Tcl_Var *rPtr;            /* returns: resolved variable */
{
    Interp *iPtr = (Interp *) interp;
    ItclCallFrame *varFramePtr = (ItclCallFrame *) iPtr->varFramePtr;

    ItclClass *cdefn = (ItclClass*)context->clientData;
    ItclObject *contextObj;
    Itcl_CallFrame *framePtr;
    Tcl_HashEntry *entry;
    ItclVarLookup *vlookup;

    assert(Itcl_IsClassNamespace(context));

    /*
     *  If this is a global variable, handle it in the usual
     *  Tcl manner.
     */
    if (flags & TCL_GLOBAL_ONLY) {
        return TCL_CONTINUE;
    }

    /*
     *  See if this is a formal parameter in the current proc scope.
     *  If so, that variable has precedence.  Look it up and return
     *  it here.  This duplicates some of the functionality of
     *  TclLookupVar, but we return it here (instead of returning
     *  TCL_CONTINUE) to avoid looking it up again later.
     */
    if (varFramePtr && varFramePtr->isProcCallFrame
        && strstr(name,"::") == NULL) {

        Proc *procPtr = varFramePtr->procPtr;

        /*
         *  Search through compiled locals first...
         */
        if (procPtr) {
            int localCt = procPtr->numCompiledLocals;
            CompiledLocal *localPtr = procPtr->firstLocalPtr;
            Var *localVarPtr = varFramePtr->compiledLocals;
            int nameLen = strlen(name);
            int i;

            for (i=0; i < localCt; i++) {
                if (!TclIsVarTemporary(localPtr)) {
                    register char *localName = localPtr->name;
                    if ((name[0] == localName[0])
                            && (nameLen == localPtr->nameLength)
                            && (strcmp(name, localName) == 0)) {
                        *rPtr = (Tcl_Var)localVarPtr;
                        return TCL_OK;
                    }
                }
                ItclNextLocal(localVarPtr);
                localPtr = localPtr->nextPtr;
            }
        }

        /*
         *  If it's not a compiled local, then look in the frame's
         *  var hash table next.  This variable may have been
         *  created on the fly.
         */
        if (varFramePtr->varTablePtr != NULL) {
	    *rPtr = (Tcl_Var) ItclVarHashFindVar(varFramePtr->varTablePtr, name);
	    if (*rPtr) {
                return TCL_OK;
            }
        }
    }

    /*
     *  See if the variable is a known data member and accessible.
     */
    entry = Tcl_FindHashEntry(&cdefn->resolveVars, name);
    if (entry == NULL) {
        return TCL_CONTINUE;
    }

    vlookup = (ItclVarLookup*)Tcl_GetHashValue(entry);
    if (!vlookup->accessible) {
        return TCL_CONTINUE;
    }

    /*
     * If this is a common data member, then its variable
     * is easy to find.  Return it directly.
     */
    if ((vlookup->vdefn->member->flags & ITCL_COMMON) != 0) {
        *rPtr = vlookup->var.common;
        return TCL_OK;
    }

    /*
     *  If this is an instance variable, then we have to
     *  find the object context, then index into its data
     *  array to get the actual variable.
     */
    framePtr = _Tcl_GetCallFrame(interp, 0);

    entry = Tcl_FindHashEntry(&cdefn->info->contextFrames, (char*)framePtr);
    if (entry == NULL) {
        return TCL_CONTINUE;
    }
    contextObj = (ItclObject*)Tcl_GetHashValue(entry);

    /*
     *  TRICKY NOTE:  We've resolved the variable in the current
     *    class context, but we must also be careful to get its
     *    index from the most-specific class context.  Variables
     *    are arranged differently depending on which class
     *    constructed the object.
     */
    if (contextObj->classDefn != vlookup->vdefn->member->classDefn) {
        entry = Tcl_FindHashEntry(&contextObj->classDefn->resolveVars,
            vlookup->vdefn->member->fullname);

        if (entry) {
            vlookup = (ItclVarLookup*)Tcl_GetHashValue(entry);
        }
    }
    *rPtr = (Tcl_Var)contextObj->data[vlookup->var.index];
    return TCL_OK;
}


/*
 * ------------------------------------------------------------------------
 *  Itcl_ClassCompiledVarResolver()
 *
 *  Used by the class namespaces to handle name resolution for compile
 *  time variable accesses.  This procedure looks for references to
 *  both common variables and instance variables at compile time.  If
 *  the variables are found, they are characterized in a generic way
 *  by their ItclVarLookup record.  At runtime, Tcl constructs the
 *  compiled local variables by calling ItclClassRuntimeVarResolver.
 *
 *  If a variable is found, this procedure returns TCL_OK along with
 *  information about the variable in the rPtr argument.  If a particular
 *  variable is private, this procedure returns TCL_ERROR and access
 *  to the variable is denied.  If a variable is not recognized, this
 *  procedure returns TCL_CONTINUE, and lookup continues via the normal
 *  Tcl name resolution rules.
 * ------------------------------------------------------------------------
 */
int
Itcl_ClassCompiledVarResolver(interp, name, length, context, rPtr)
    Tcl_Interp *interp;         /* current interpreter */
    CONST char* name;                 /* name of the variable being accessed */
    int length;                 /* number of characters in name */
    Tcl_Namespace *context;     /* namespace performing the resolution */
    Tcl_ResolvedVarInfo **rPtr; /* returns: info that makes it possible to
                                 *   resolve the variable at runtime */
{
    ItclClass *cdefn = (ItclClass*)context->clientData;
    Tcl_HashEntry *entry;
    ItclVarLookup *vlookup;
    char *buffer, storage[64];

    assert(Itcl_IsClassNamespace(context));

    /*
     *  Copy the name to local storage so we can NULL terminate it.
     *  If the name is long, allocate extra space for it.
     */
    if (length < sizeof(storage)) {
        buffer = storage;
    } else {
        buffer = (char*)ckalloc((unsigned)(length+1));
    }
    memcpy((void*)buffer, (void*)name, (size_t)length);
    buffer[length] = '\0';

    entry = Tcl_FindHashEntry(&cdefn->resolveVars, buffer);

    if (buffer != storage) {
        ckfree(buffer);
    }

    /*
     *  If the name is not found, or if it is inaccessible,
     *  continue on with the normal Tcl name resolution rules.
     */
    if (entry == NULL) {
        return TCL_CONTINUE;
    }

    vlookup = (ItclVarLookup*)Tcl_GetHashValue(entry);
    if (!vlookup->accessible) {
        return TCL_CONTINUE;
    }

    /*
     *  Return the ItclVarLookup record.  At runtime, Tcl will
     *  call ItclClassRuntimeVarResolver with this record, to
     *  plug in the appropriate variable for the current object
     *  context.
     */
    (*rPtr) = (Tcl_ResolvedVarInfo *) ckalloc(sizeof(ItclResolvedVarInfo));
    (*rPtr)->fetchProc = ItclClassRuntimeVarResolver;
    (*rPtr)->deleteProc = NULL;
    ((ItclResolvedVarInfo*)(*rPtr))->vlookup = vlookup;

    return TCL_OK;
}


/*
 * ------------------------------------------------------------------------
 *  ItclClassRuntimeVarResolver()
 *
 *  Invoked when Tcl sets up the call frame for an [incr Tcl] method/proc
 *  at runtime.  Resolves data members identified earlier by
 *  Itcl_ClassCompiledVarResolver.  Returns the Tcl_Var representation
 *  for the data member.
 * ------------------------------------------------------------------------
 */
static Tcl_Var
ItclClassRuntimeVarResolver(interp, resVarInfo)
    Tcl_Interp *interp;               /* current interpreter */
    Tcl_ResolvedVarInfo *resVarInfo;  /* contains ItclVarLookup rep
                                       * for variable */
{
    ItclVarLookup *vlookup = ((ItclResolvedVarInfo*)resVarInfo)->vlookup;

    Itcl_CallFrame *framePtr;
    ItclClass *cdefn;
    ItclObject *contextObj;
    Tcl_HashEntry *entry;

    /*
     *  If this is a common data member, then the associated
     *  variable is known directly.
     */
    if ((vlookup->vdefn->member->flags & ITCL_COMMON) != 0) {
        return vlookup->var.common;
    }
    cdefn = vlookup->vdefn->member->classDefn;

    /*
     *  Otherwise, get the current object context and find the
     *  variable in its data table.
     *
     *  TRICKY NOTE:  Get the index for this variable using the
     *    virtual table for the MOST-SPECIFIC class.
     */
    framePtr = _Tcl_GetCallFrame(interp, 0);

    entry = Tcl_FindHashEntry(&cdefn->info->contextFrames, (char*)framePtr);
    if (entry) {
        contextObj = (ItclObject*)Tcl_GetHashValue(entry);

        if (contextObj != NULL) {
            if (contextObj->classDefn != vlookup->vdefn->member->classDefn) {
                entry = Tcl_FindHashEntry(&contextObj->classDefn->resolveVars,
                    vlookup->vdefn->member->fullname);

                if (entry) {
                    vlookup = (ItclVarLookup*)Tcl_GetHashValue(entry);
                }
            }
            return (Tcl_Var)contextObj->data[vlookup->var.index];
        }
    }
    return NULL;
}


/*
 * ------------------------------------------------------------------------
 *  Itcl_BuildVirtualTables()
 *
 *  Invoked whenever the class heritage changes or members are added or
 *  removed from a class definition to rebuild the member lookup
 *  tables.  There are two tables:
 *
 *  METHODS:  resolveCmds
 *    Used primarily in Itcl_ClassCmdResolver() to resolve all
 *    command references in a namespace.
 *
 *  DATA MEMBERS:  resolveVars
 *    Used primarily in Itcl_ClassVarResolver() to quickly resolve
 *    variable references in each class scope.
 *
 *  These tables store every possible name for each command/variable
 *  (member, class::member, namesp::class::member, etc.).  Members
 *  in a derived class may shadow members with the same name in a
 *  base class.  In that case, the simple name in the resolution
 *  table will point to the most-specific member.
 * ------------------------------------------------------------------------
 */
void
Itcl_BuildVirtualTables(cdefnPtr)
    ItclClass* cdefnPtr;       /* class definition being updated */
{
    Tcl_HashEntry *entry;
    Tcl_HashSearch place;
    ItclVarLookup *vlookup;
    ItclVarDefn *vdefn;
    ItclMemberFunc *mfunc;
    ItclHierIter hier;
    ItclClass *cdPtr;
    Namespace* nsPtr;
    Tcl_DString buffer, buffer2;
    int newEntry;

    Tcl_DStringInit(&buffer);
    Tcl_DStringInit(&buffer2);

    /*
     *  Clear the variable resolution table.
     */
    entry = Tcl_FirstHashEntry(&cdefnPtr->resolveVars, &place);
    while (entry) {
        vlookup = (ItclVarLookup*)Tcl_GetHashValue(entry);
        if (--vlookup->usage == 0) {
            ckfree((char*)vlookup);
        }
        entry = Tcl_NextHashEntry(&place);
    }
    Tcl_DeleteHashTable(&cdefnPtr->resolveVars);
    Tcl_InitHashTable(&cdefnPtr->resolveVars, TCL_STRING_KEYS);
    cdefnPtr->numInstanceVars = 0;

    /*
     *  Set aside the first object-specific slot for the built-in
     *  "this" variable.  Only allocate one of these, even though
     *  there is a definition for "this" in each class scope.
     */
    cdefnPtr->numInstanceVars++;

    /*
     *  Scan through all classes in the hierarchy, from most to
     *  least specific.  Add a lookup entry for each variable
     *  into the table.
     */
    Itcl_InitHierIter(&hier, cdefnPtr);
    cdPtr = Itcl_AdvanceHierIter(&hier);
    while (cdPtr != NULL) {
        entry = Tcl_FirstHashEntry(&cdPtr->variables, &place);
        while (entry) {
            vdefn = (ItclVarDefn*)Tcl_GetHashValue(entry);

            vlookup = (ItclVarLookup*)ckalloc(sizeof(ItclVarLookup));
            vlookup->vdefn = vdefn;
            vlookup->usage = 0;
            vlookup->leastQualName = NULL;

            /*
             *  If this variable is PRIVATE to another class scope,
             *  then mark it as "inaccessible".
             */
            vlookup->accessible =
                ( vdefn->member->protection != ITCL_PRIVATE ||
                  vdefn->member->classDefn == cdefnPtr );

            /*
             *  If this is a common variable, then keep a reference to
             *  the variable directly.  Otherwise, keep an index into
             *  the object's variable table.
             */
            if ((vdefn->member->flags & ITCL_COMMON) != 0) {
                nsPtr = (Namespace*)cdPtr->namesp;
                vlookup->var.common = (Tcl_Var) ItclVarHashFindVar(&nsPtr->varTable, vdefn->member->name);
                assert(vlookup->var.common  != NULL);
            }
            else {
                /*
                 *  If this is a reference to the built-in "this"
                 *  variable, then its index is "0".  Otherwise,
                 *  add another slot to the end of the table.
                 */
                if ((vdefn->member->flags & ITCL_THIS_VAR) != 0) {
                    vlookup->var.index = 0;
                }
                else {
                    vlookup->var.index = cdefnPtr->numInstanceVars++;
                }
            }

            /*
             *  Create all possible names for this variable and enter
             *  them into the variable resolution table:
             *     var
             *     class::var
             *     namesp1::class::var
             *     namesp2::namesp1::class::var
             *     ...
             */
            Tcl_DStringSetLength(&buffer, 0);
            Tcl_DStringAppend(&buffer, vdefn->member->name, -1);
            nsPtr = (Namespace*)cdPtr->namesp;

            while (1) {
                entry = Tcl_CreateHashEntry(&cdefnPtr->resolveVars,
                    Tcl_DStringValue(&buffer), &newEntry);

                if (newEntry) {
                    Tcl_SetHashValue(entry, (ClientData)vlookup);
                    vlookup->usage++;

                    if (!vlookup->leastQualName) {
                        vlookup->leastQualName =
                            Tcl_GetHashKey(&cdefnPtr->resolveVars, entry);
                    }
                }

                if (nsPtr == NULL) {
                    break;
                }
                Tcl_DStringSetLength(&buffer2, 0);
                Tcl_DStringAppend(&buffer2, Tcl_DStringValue(&buffer), -1);
                Tcl_DStringSetLength(&buffer, 0);
                Tcl_DStringAppend(&buffer, nsPtr->name, -1);
                Tcl_DStringAppend(&buffer, "::", -1);
                Tcl_DStringAppend(&buffer, Tcl_DStringValue(&buffer2), -1);

                nsPtr = nsPtr->parentPtr;
            }

            /*
             *  If this record is not needed, free it now.
             */
            if (vlookup->usage == 0) {
                ckfree((char*)vlookup);
            }
            entry = Tcl_NextHashEntry(&place);
        }
        cdPtr = Itcl_AdvanceHierIter(&hier);
    }
    Itcl_DeleteHierIter(&hier);

    /*
     *  Clear the command resolution table.
     */
    Tcl_DeleteHashTable(&cdefnPtr->resolveCmds);
    Tcl_InitHashTable(&cdefnPtr->resolveCmds, TCL_STRING_KEYS);

    /*
     *  Scan through all classes in the hierarchy, from most to
     *  least specific.  Look for the first (most-specific) definition
     *  of each member function, and enter it into the table.
     */
    Itcl_InitHierIter(&hier, cdefnPtr);
    cdPtr = Itcl_AdvanceHierIter(&hier);
    while (cdPtr != NULL) {
        entry = Tcl_FirstHashEntry(&cdPtr->functions, &place);
        while (entry) {
            mfunc = (ItclMemberFunc*)Tcl_GetHashValue(entry);

            /*
             *  Create all possible names for this function and enter
             *  them into the command resolution table:
             *     func
             *     class::func
             *     namesp1::class::func
             *     namesp2::namesp1::class::func
             *     ...
             */
            Tcl_DStringSetLength(&buffer, 0);
            Tcl_DStringAppend(&buffer, mfunc->member->name, -1);
            nsPtr = (Namespace*)cdPtr->namesp;

            while (1) {
                entry = Tcl_CreateHashEntry(&cdefnPtr->resolveCmds,
                    Tcl_DStringValue(&buffer), &newEntry);

                if (newEntry) {
                    Tcl_SetHashValue(entry, (ClientData)mfunc);
                }

                if (nsPtr == NULL) {
                    break;
                }
                Tcl_DStringSetLength(&buffer2, 0);
                Tcl_DStringAppend(&buffer2, Tcl_DStringValue(&buffer), -1);
                Tcl_DStringSetLength(&buffer, 0);
                Tcl_DStringAppend(&buffer, nsPtr->name, -1);
                Tcl_DStringAppend(&buffer, "::", -1);
                Tcl_DStringAppend(&buffer, Tcl_DStringValue(&buffer2), -1);

                nsPtr = nsPtr->parentPtr;
            }
            entry = Tcl_NextHashEntry(&place);
        }
        cdPtr = Itcl_AdvanceHierIter(&hier);
    }
    Itcl_DeleteHierIter(&hier);

    Tcl_DStringFree(&buffer);
    Tcl_DStringFree(&buffer2);
}


/*
 * ------------------------------------------------------------------------
 *  Itcl_CreateVarDefn()
 *
 *  Creates a new class variable definition.  If this is a public
 *  variable, it may have a bit of "config" code that is used to
 *  update the object whenever the variable is modified via the
 *  built-in "configure" method.
 *
 *  Returns TCL_ERROR along with an error message in the specified
 *  interpreter if anything goes wrong.  Otherwise, this returns
 *  TCL_OK and a pointer to the new variable definition in "vdefnPtr".
 * ------------------------------------------------------------------------
 */
int
Itcl_CreateVarDefn(interp, cdefn, name, init, config, vdefnPtr)
    Tcl_Interp *interp;       /* interpreter managing this transaction */
    ItclClass* cdefn;         /* class containing this variable */
    char* name;               /* variable name */
    char* init;               /* initial value */
    char* config;             /* code invoked when variable is configured */
    ItclVarDefn** vdefnPtr;   /* returns: new variable definition */
{
    int newEntry;
    ItclVarDefn *vdefn;
    ItclMemberCode *mcode;
    Tcl_HashEntry *entry;

    /*
     *  Add this variable to the variable table for the class.
     *  Make sure that the variable name does not already exist.
     */
    entry = Tcl_CreateHashEntry(&cdefn->variables, name, &newEntry);
    if (!newEntry) {
        Tcl_AppendResult(interp,
            "variable name \"", name, "\" already defined in class \"",
            cdefn->fullname, "\"",
            (char*)NULL);
        return TCL_ERROR;
    }

    /*
     *  If this variable has some "config" code, try to capture
     *  its implementation.
     */
    if (config) {
        if (Itcl_CreateMemberCode(interp, cdefn, (char*)NULL, config,
            &mcode) != TCL_OK) {

            Tcl_DeleteHashEntry(entry);
            return TCL_ERROR;
        }
        Itcl_PreserveData((ClientData)mcode);
        Itcl_EventuallyFree((ClientData)mcode, (Tcl_FreeProc*) Itcl_DeleteMemberCode);
    }
    else {
        mcode = NULL;
    }

    /*
     *  If everything looks good, create the variable definition.
     */
    vdefn = (ItclVarDefn*)ckalloc(sizeof(ItclVarDefn));
    vdefn->member = Itcl_CreateMember(interp, cdefn, name);
    vdefn->member->code = mcode;

    if (vdefn->member->protection == ITCL_DEFAULT_PROTECT) {
        vdefn->member->protection = ITCL_PROTECTED;
    }

    if (init) {
        vdefn->init = (char*)ckalloc((unsigned)(strlen(init)+1));
        strcpy(vdefn->init, init);
    }
    else {
        vdefn->init = NULL;
    }

    Tcl_SetHashValue(entry, (ClientData)vdefn);

    *vdefnPtr = vdefn;
    return TCL_OK;
}

/*
 * ------------------------------------------------------------------------
 *  Itcl_DeleteVarDefn()
 *
 *  Destroys a variable definition created by Itcl_CreateVarDefn(),
 *  freeing all resources associated with it.
 * ------------------------------------------------------------------------
 */
void
Itcl_DeleteVarDefn(vdefn)
    ItclVarDefn *vdefn;   /* variable definition to be destroyed */
{
    Itcl_DeleteMember(vdefn->member);

    if (vdefn->init) {
        ckfree(vdefn->init);
    }
    ckfree((char*)vdefn);
}


/*
 * ------------------------------------------------------------------------
 *  Itcl_GetCommonVar()
 *
 *  Returns the current value for a common class variable.  The member
 *  name is interpreted with respect to the given class scope.  That
 *  scope is installed as the current context before querying the
 *  variable.  This by-passes the protection level in case the variable
 *  is "private".
 *
 *  If successful, this procedure returns a pointer to a string value
 *  which remains alive until the variable changes it value.  If
 *  anything goes wrong, this returns NULL.
 * ------------------------------------------------------------------------
 */
CONST char*
Itcl_GetCommonVar(interp, name, contextClass)
    Tcl_Interp *interp;        /* current interpreter */
    CONST char *name;                /* name of desired instance variable */
    ItclClass *contextClass;   /* name is interpreted in this scope */
{
    CONST char *val = NULL;
    int result;
    Itcl_CallFrame frame;

    /*
     *  Activate the namespace for the given class.  That installs
     *  the appropriate name resolution rules and by-passes any
     *  security restrictions.
     */
    result = Tcl_PushCallFrame(interp, (Tcl_CallFrame *) &frame,
                 contextClass->namesp, /*isProcCallFrame*/ 0);

    if (result == TCL_OK) {
        val = Tcl_GetVar2(interp, (CONST84 char *)name, (char*)NULL, 0);
        Tcl_PopCallFrame(interp);
    }
    return val;
}


/*
 * ------------------------------------------------------------------------
 *  Itcl_CreateMember()
 *
 *  Creates the data record representing a class member.  This is the
 *  generic representation for a data member or member function.
 *  Returns a pointer to the new representation.
 * ------------------------------------------------------------------------
 */
ItclMember*
Itcl_CreateMember(interp, cdefn, name)
    Tcl_Interp* interp;            /* interpreter managing this action */
    ItclClass *cdefn;              /* class definition */
    CONST char* name;              /* name of new member */
{
    ItclMember *memPtr;
    int fullsize;

    /*
     *  Allocate the memory for a class member and fill in values.
     */
    memPtr = (ItclMember*)ckalloc(sizeof(ItclMember));
    memPtr->interp       = interp;
    memPtr->classDefn    = cdefn;
    memPtr->flags        = 0;
    memPtr->protection   = Itcl_Protection(interp, 0);
    memPtr->code         = NULL;

    fullsize = strlen(cdefn->fullname) + strlen(name) + 2;
    memPtr->fullname = (char*)ckalloc((unsigned)(fullsize+1));
    strcpy(memPtr->fullname, cdefn->fullname);
    strcat(memPtr->fullname, "::");
    strcat(memPtr->fullname, name);

    memPtr->name = (char*)ckalloc((unsigned)(strlen(name)+1));
    strcpy(memPtr->name, name);

    return memPtr;
}


/*
 * ------------------------------------------------------------------------
 *  Itcl_DeleteMember()
 *
 *  Destroys all data associated with the given member function definition.
 *  Usually invoked by the interpreter when a member function is deleted.
 * ------------------------------------------------------------------------
 */
void
Itcl_DeleteMember(memPtr)
    ItclMember *memPtr;  /* pointer to member function definition */
{
    if (memPtr) {
        ckfree(memPtr->name);
        ckfree(memPtr->fullname);

        if (memPtr->code) {
            Itcl_ReleaseData((ClientData)memPtr->code);
        }
        memPtr->code = NULL;

        ckfree((char*)memPtr);
    }
}


/*
 * ------------------------------------------------------------------------
 *  Itcl_InitHierIter()
 *
 *  Initializes an iterator for traversing the hierarchy of the given
 *  class.  Subsequent calls to Itcl_AdvanceHierIter() will return
 *  the base classes in order from most-to-least specific.
 * ------------------------------------------------------------------------
 */
void
Itcl_InitHierIter(iter,cdefn)
    ItclHierIter *iter;   /* iterator used for traversal */
    ItclClass *cdefn;     /* class definition for start of traversal */
{
    Itcl_InitStack(&iter->stack);
    Itcl_PushStack((ClientData)cdefn, &iter->stack);
    iter->current = cdefn;
}

/*
 * ------------------------------------------------------------------------
 *  Itcl_DeleteHierIter()
 *
 *  Destroys an iterator for traversing class hierarchies, freeing
 *  all memory associated with it.
 * ------------------------------------------------------------------------
 */
void
Itcl_DeleteHierIter(iter)
    ItclHierIter *iter;  /* iterator used for traversal */
{
    Itcl_DeleteStack(&iter->stack);
    iter->current = NULL;
}

/*
 * ------------------------------------------------------------------------
 *  Itcl_AdvanceHierIter()
 *
 *  Moves a class hierarchy iterator forward to the next base class.
 *  Returns a pointer to the current class definition, or NULL when
 *  the end of the hierarchy has been reached.
 * ------------------------------------------------------------------------
 */
ItclClass*
Itcl_AdvanceHierIter(iter)
    ItclHierIter *iter;  /* iterator used for traversal */
{
    register Itcl_ListElem *elem;
    ItclClass *cdPtr;

    iter->current = (ItclClass*)Itcl_PopStack(&iter->stack);

    /*
     *  Push classes onto the stack in reverse order, so that
     *  they will be popped off in the proper order.
     */
    if (iter->current) {
        cdPtr = (ItclClass*)iter->current;
        elem = Itcl_LastListElem(&cdPtr->bases);
        while (elem) {
            Itcl_PushStack(Itcl_GetListValue(elem), &iter->stack);
            elem = Itcl_PrevListElem(elem);
        }
    }
    return iter->current;
}
