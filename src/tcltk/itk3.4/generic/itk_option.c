/*
 * ------------------------------------------------------------------------
 *      PACKAGE:  [incr Tk]
 *  DESCRIPTION:  Building mega-widgets with [incr Tcl]
 *
 *  [incr Tk] provides a framework for building composite "mega-widgets"
 *  using [incr Tcl] classes.  It defines a set of base classes that are
 *  specialized to create all other widgets.
 *
 *  This file defines procedures used to manage mega-widget options
 *  specified within class definitions.
 *
 * ========================================================================
 *  AUTHOR:  Michael J. McLennan
 *           Bell Labs Innovations for Lucent Technologies
 *           mmclennan@lucent.com
 *           http://www.tcltk.com/itcl
 *
 *     RCS:  $Id: itk_option.c,v 1.7 2007/05/24 23:23:59 hobbs Exp $
 * ========================================================================
 *           Copyright (c) 1993-1998  Lucent Technologies, Inc.
 * ------------------------------------------------------------------------
 * See the file "license.terms" for information on usage and redistribution
 * of this file, and for a DISCLAIMER OF ALL WARRANTIES.
 */
#include "itk.h"

/*
 *  FORWARD DECLARATIONS
 */
static char* ItkTraceClassDestroy _ANSI_ARGS_((ClientData cdata,
    Tcl_Interp *interp, CONST char *name1, CONST char *name2, int flags));
static Tcl_HashTable* ItkGetClassesWithOptInfo _ANSI_ARGS_((
    Tcl_Interp *interp));
static void ItkFreeClassesWithOptInfo _ANSI_ARGS_((ClientData cdata,
    Tcl_Interp *interp));


/*
 * ------------------------------------------------------------------------
 *  Itk_ClassOptionDefineCmd()
 *
 *  Invoked when a class definition is being parse to handle an
 *  itk_option declaration.  Adds a new option to a mega-widget
 *  declaration, with some code that will be executed whenever the
 *  option is changed via "configure".  If there is already an existing
 *  option by that name, then this new option is folded into the
 *  existing option, but the <init> value is ignored.  The X11 resource
 *  database names must be consistent with the existing option.
 *
 *  Handles the following syntax:
 *
 *      itk_option define <switch> <resName> <resClass> <init> ?<config>?
 *
 *  Returns TCL_OK/TCL_ERROR to indicate success/failure.
 * ------------------------------------------------------------------------
 */
/* ARGSUSED */
int
Itk_ClassOptionDefineCmd(clientData, interp, objc, objv)
    ClientData clientData;   /* class parser info */
    Tcl_Interp *interp;      /* current interpreter */
    int objc;                /* number of arguments */
    Tcl_Obj *CONST objv[];   /* argument objects */
{
    ItclObjectInfo *info = (ItclObjectInfo*)clientData;
    ItclClass *cdefn = (ItclClass*)Itcl_PeekStack(&info->cdefnStack);

    int newEntry;
    char *switchName, *resName, *resClass, *init, *config;
    ItkClassOptTable *optTable;
    Tcl_HashEntry *entry;
    ItkClassOption *opt;

    /*
     *  Make sure that the arguments look right.  The option switch
     *  name must start with a '-'.
     */
    if (objc < 5 || objc > 6) {
        Tcl_WrongNumArgs(interp, 1, objv,
            "-switch resourceName resourceClass init ?config?");
        return TCL_ERROR;
    }

    switchName = Tcl_GetStringFromObj(objv[1], (int*)NULL);
    if (*switchName != '-') {
        Tcl_AppendResult(interp,
            "bad option name \"", switchName, "\": should be -", switchName,
            (char*)NULL);
        return TCL_ERROR;
    }
    if (strstr(switchName, ".")) {
        Tcl_AppendResult(interp,
            "bad option name \"", switchName, "\": illegal character \".\"",
            (char*)NULL);
        return TCL_ERROR;
    }

    resName = Tcl_GetStringFromObj(objv[2], (int*)NULL);
    if (!islower((int)*resName)) {
        Tcl_AppendResult(interp,
            "bad resource name \"", resName,
            "\": should start with a lower case letter",
            (char*)NULL);
        return TCL_ERROR;
    }

    resClass = Tcl_GetStringFromObj(objv[3], (int*)NULL);
    if (!isupper((int)*resClass)) {
        Tcl_AppendResult(interp,
            "bad resource class \"", resClass,
            "\": should start with an upper case letter",
            (char*)NULL);
        return TCL_ERROR;
    }

    /*
     *  Make sure that this option has not already been defined in
     *  the context of this class.  Options can be redefined in
     *  other classes, but can only be defined once in a given
     *  class.  This ensures that there will be no confusion about
     *  which option is being referenced if the configuration code
     *  is redefined by a subsequent "body" command.
     */
    optTable = Itk_CreateClassOptTable(interp, cdefn);
    entry = Tcl_CreateHashEntry(&optTable->options, switchName, &newEntry);

    if (!newEntry) {
        Tcl_AppendResult(interp,
            "option \"", switchName, "\" already defined in class \"",
            cdefn->fullname, "\"",
            (char*)NULL);
        return TCL_ERROR;
    }

    /*
     *  Create a new option record and add it to the table for this
     *  class.
     */
    init = Tcl_GetStringFromObj(objv[4], (int*)NULL);

    if (objc == 6) {
        config = Tcl_GetStringFromObj(objv[5], (int*)NULL);
    } else {
        config = NULL;
    }

    if (Itk_CreateClassOption(interp, cdefn, switchName, resName, resClass,
        init, config, &opt) != TCL_OK) {
        return TCL_ERROR;
    }

    Tcl_SetHashValue(entry, (ClientData)opt);
    Itk_OptListAdd(&optTable->order, entry);
    return TCL_OK;
}


/*
 * ------------------------------------------------------------------------
 *  Itk_ClassOptionIllegalCmd()
 *
 *  Invoked when a class definition is being parse to handle an
 *  itk_option declaration.  Handles an "illegal" declaration like
 *  "add" or "remove", which can only be used after a widget has
 *  been created.  Returns TCL_ERROR along with an error message.
 * ------------------------------------------------------------------------
 */
/* ARGSUSED */
int
Itk_ClassOptionIllegalCmd(clientData, interp, objc, objv)
    ClientData clientData;   /* class parser info */
    Tcl_Interp *interp;      /* current interpreter */
    int objc;                /* number of arguments */
    Tcl_Obj *CONST objv[];   /* argument objects */
{
    char *op = Tcl_GetStringFromObj(objv[0], (int*)NULL);

    Tcl_AppendResult(interp,
        "can only ", op, " options for a specific widget\n",
        "(move this command into the constructor)",
        (char*)NULL);

    return TCL_ERROR;
}


/*
 * ------------------------------------------------------------------------
 *  Itk_ConfigClassOption()
 *
 *  Invoked whenever a class-based configuration option has been
 *  configured with a new value.  If the option has any extra code
 *  associated with it, the code is invoked at this point to bring
 *  the widget up-to-date.
 *
 *  Returns TCL_OK on success, or TCL_ERROR (along with an error
 *  message in the interpreter) if anything goes wrong.
 * ------------------------------------------------------------------------
 */
/* ARGSUSED */
int
Itk_ConfigClassOption(interp, contextObj, cdata, newval)
    Tcl_Interp *interp;        /* interpreter managing the class */
    ItclObject *contextObj;    /* object being configured */
    ClientData cdata;          /* class option */
    CONST char *newval;        /* new value for this option */
{
    ItkClassOption *opt = (ItkClassOption*)cdata;
    int result = TCL_OK;
    ItclMemberCode *mcode;

    /*
     *  If the option has any config code, execute it now.
     *  Make sure that the namespace context is set up correctly.
     */
    mcode = opt->member->code;
    if (mcode && mcode->procPtr->bodyPtr) {
        result = Itcl_EvalMemberCode(interp, (ItclMemberFunc*)NULL,
            opt->member, contextObj, 0, (Tcl_Obj**)NULL);
    }
    return result;
}


/*
 * ------------------------------------------------------------------------
 *  Itk_CreateClassOptTable()
 *
 *  Finds or creates an option table which will contain all of the
 *  class-based configuration options for a mega-widget.  These are
 *  the options included in the class definition which add new behavior
 *  to the mega-widget.
 *
 *  This table is automatically deleted by ItkTraceClassDestroy
 *  whenever the class namespace is destroyed.  The "unset" operation
 *  of a private class variable is used to detect the destruction of
 *  the namespace.
 *
 *  Returns a pointer to an option table which will contain pointers to
 *  ItkClassOption records.
 * ------------------------------------------------------------------------
 */
ItkClassOptTable*
Itk_CreateClassOptTable(interp, cdefn)
    Tcl_Interp *interp;        /* interpreter managing the class */
    ItclClass *cdefn;          /* class definition */
{
    int newEntry, result;
    Tcl_HashTable *itkClasses;
    Tcl_HashEntry *entry;
    ItkClassOptTable *optTable;
    Itcl_CallFrame frame;

    /*
     *  Look for the specified class definition in the table.
     *  If it does not yet exist, then create a new slot for it.
     *  When a table is created for the first time, add a
     *  special sentinel variable "_itk_option_data" to the
     *  class namespace, and put a trace on this variable.
     *  Whenever it is destroyed, have it delete the option table
     *  for this class.
     */
    itkClasses = ItkGetClassesWithOptInfo(interp);

    entry = Tcl_CreateHashEntry(itkClasses, (char*)cdefn, &newEntry);
    if (newEntry) {
        optTable = (ItkClassOptTable*)ckalloc(sizeof(ItkClassOptTable));
        Tcl_InitHashTable(&optTable->options, TCL_STRING_KEYS);
        Itk_OptListInit(&optTable->order, &optTable->options);

        Tcl_SetHashValue(entry, (ClientData)optTable);

        result = Tcl_PushCallFrame(interp, (Tcl_CallFrame *) &frame,
             cdefn->namesp, /* isProcCallFrame */ 0);

        if (result == TCL_OK) {
            Tcl_TraceVar(interp, "_itk_option_data",
                (TCL_TRACE_UNSETS | TCL_NAMESPACE_ONLY),
                (Tcl_VarTraceProc*) ItkTraceClassDestroy, (ClientData)cdefn);
            Tcl_PopCallFrame(interp);
        }
    }
    else {
        optTable = (ItkClassOptTable*)Tcl_GetHashValue(entry);
    }
    return optTable;
}


/*
 * ------------------------------------------------------------------------
 *  Itk_FindClassOptTable()
 *
 *  Looks for an option table containing all of the class-based
 *  configuration options for a mega-widget.  These are the options
 *  included in a class definition which add new behavior to the
 *  mega-widget.
 *
 *  Returns a pointer to an option table which will contain pointers to
 *  Itk_ClassOption records.  If a table does not exist for this class,
 *  this returns NULL.
 * ------------------------------------------------------------------------
 */
ItkClassOptTable*
Itk_FindClassOptTable(cdefn)
    ItclClass *cdefn;          /* class definition */
{
    Tcl_HashTable *itkClasses;
    Tcl_HashEntry *entry;

    /*
     *  Look for the specified class definition in the table.
     */
    itkClasses = ItkGetClassesWithOptInfo(cdefn->interp);
    entry = Tcl_FindHashEntry(itkClasses, (char*)cdefn);
    if (entry) {
        return (ItkClassOptTable*)Tcl_GetHashValue(entry);
    }
    return NULL;
}


/*
 * ------------------------------------------------------------------------
 *  ItkTraceClassDestroy()
 *
 *  Invoked automatically whenever the "_itk_option_data" variable
 *  is destroyed within a class namespace.  This should be a signal
 *  that the namespace is being destroyed.
 *
 *  Releases any option data that exists for the class.
 *
 *  Returns NULL on success, or a pointer to a string describing any
 *  error that is encountered.
 * ------------------------------------------------------------------------
 */
/* ARGSUSED */
static char*
ItkTraceClassDestroy(cdata, interp, name1, name2, flags)
    ClientData cdata;          /* class definition data */
    Tcl_Interp *interp;        /* interpreter managing the class */
    CONST char *name1;               /* name of variable involved in trace */
    CONST char *name2;         /* name of array element within variable */
    int flags;                 /* flags describing trace */
{
    ItclClass *cdefn = (ItclClass*)cdata;

    Tcl_HashTable *itkClasses;
    Tcl_HashEntry *entry;
    ItkClassOptTable *optTable;
    Tcl_HashSearch place;
    ItkClassOption *opt;

    /*
     *  Look for the specified class definition in the table.
     *  If it is found, delete all the option records and tear
     *  down the table.
     */
    itkClasses = ItkGetClassesWithOptInfo(cdefn->interp);
    entry = Tcl_FindHashEntry(itkClasses, (char*)cdefn);
    if (entry) {
        optTable = (ItkClassOptTable*)Tcl_GetHashValue(entry);
        Tcl_DeleteHashEntry(entry);

        entry = Tcl_FirstHashEntry(&optTable->options, &place);
        while (entry) {
            opt = (ItkClassOption*)Tcl_GetHashValue(entry);
            Itk_DelClassOption(opt);
            entry = Tcl_NextHashEntry(&place);
        }
        Tcl_DeleteHashTable(&optTable->options);
        Itk_OptListFree(&optTable->order);
        ckfree((char*)optTable);
    }
    return NULL;
}


/*
 * ------------------------------------------------------------------------
 *  Itk_CreateClassOption()
 *
 *  Creates the data representing a configuration option for an
 *  Archetype mega-widget.  This record represents an option included
 *  in the class definition.  It adds new behavior to the mega-widget
 *  class.
 *
 *  If successful, returns TCL_OK along with a pointer to the option
 *  record.  Returns TCL_ERROR (along with an error message in the
 *  interpreter) if anything goes wrong.
 * ------------------------------------------------------------------------
 */
int
Itk_CreateClassOption(interp, cdefn, switchName, resName, resClass,
    defVal, config, optPtr)

    Tcl_Interp *interp;            /* interpreter managing the class */
    ItclClass *cdefn;              /* class containing this option */
    char *switchName;              /* name of command-line switch */
    char *resName;                 /* resource name in X11 database */
    char *resClass;                /* resource class name in X11 database */
    char *defVal;                  /* last-resort default value */
    char *config;                  /* configuration code */
    ItkClassOption **optPtr;       /* returns: option record */
{
    ItkClassOption *opt;
    ItclMemberCode *mcode;

    /*
     *  If this option has any "config" code, then try to create
     *  an implementation for it.
     */
    if (config) {
        if (Itcl_CreateMemberCode(interp, cdefn, (char*)NULL, config,
            &mcode) != TCL_OK) {

            return TCL_ERROR;
        }
        Itcl_PreserveData((ClientData)mcode);
        Itcl_EventuallyFree((ClientData)mcode,
		(Tcl_FreeProc*) Itcl_DeleteMemberCode);
    }
    else {
        mcode = NULL;
    }

    /*
     *  Create the record to represent this option.
     */
    opt = (ItkClassOption*)ckalloc(sizeof(ItkClassOption));
    opt->member = Itcl_CreateMember(interp, cdefn, switchName);
    opt->member->code = mcode;

    opt->resName = (char*)ckalloc((unsigned)(strlen(resName)+1));
    strcpy(opt->resName, resName);

    opt->resClass = (char*)ckalloc((unsigned)(strlen(resClass)+1));
    strcpy(opt->resClass, resClass);

    opt->init = (char*)ckalloc((unsigned)(strlen(defVal)+1));
    strcpy(opt->init, defVal);

    *optPtr = opt;
    return TCL_OK;
}

/*
 * ------------------------------------------------------------------------
 *  Itk_FindClassOption()
 *
 *  Searches for a class-based configuration option for an Archetype
 *  mega-widget.   The specified name is treated as the "switch" name
 *  (e.g., "-option"), but this procedure will recognize it even without
 *  the leading "-".
 *
 *  If an option is found that was defined in the specified class,
 *  then this procedure returns a pointer to the option definition.
 *  Otherwise, it returns NULL.
 * ------------------------------------------------------------------------
 */
ItkClassOption*
Itk_FindClassOption(cdefn, switchName)
    ItclClass *cdefn;              /* class containing this option */
    char *switchName;              /* name of command-line switch */
{
    ItkClassOption *opt = NULL;

    Tcl_DString buffer;
    ItkClassOptTable *optTable;
    Tcl_HashEntry *entry;

    /*
     *  If the switch does not have a leading "-", add it on.
     */
    Tcl_DStringInit(&buffer);
    if (*switchName != '-') {
        Tcl_DStringAppend(&buffer, "-", -1);
        Tcl_DStringAppend(&buffer, switchName, -1);
        switchName = Tcl_DStringValue(&buffer);
    }

    /*
     *  Look for the option table for the specified class, and check
     *  for the requested switch.
     */
    optTable = Itk_FindClassOptTable(cdefn);
    if (optTable) {
        entry = Tcl_FindHashEntry(&optTable->options, switchName);
        if (entry) {
            opt = (ItkClassOption*)Tcl_GetHashValue(entry);
        }
    }
    Tcl_DStringFree(&buffer);
    return opt;
}

/*
 * ------------------------------------------------------------------------
 *  Itk_DelClassOption()
 *
 *  Destroys a configuration option previously created by
 *  Itk_CreateClassOption().
 * ------------------------------------------------------------------------
 */
void
Itk_DelClassOption(opt)
    ItkClassOption *opt;  /* pointer to option data */
{
    Itcl_DeleteMember(opt->member);
    ckfree(opt->resName);
    ckfree(opt->resClass);
    ckfree(opt->init);

    ckfree((char*)opt);
}


/*
 * ------------------------------------------------------------------------
 *  ItkGetClassesWithOptInfo()
 *
 *  Returns a pointer to a hash table containing the list of registered
 *  classes in the specified interpreter.  If the hash table does not
 *  already exist, it is created.
 * ------------------------------------------------------------------------
 */
static Tcl_HashTable*
ItkGetClassesWithOptInfo(interp)
    Tcl_Interp *interp;  /* interpreter handling this registration */
{
    Tcl_HashTable* classesTable;

    /*
     *  If the registration table does not yet exist, then create it.
     */
    classesTable = (Tcl_HashTable*)Tcl_GetAssocData(interp,
        "itk_classesWithOptInfo", (Tcl_InterpDeleteProc**)NULL);

    if (!classesTable) {
        classesTable = (Tcl_HashTable*)ckalloc(sizeof(Tcl_HashTable));
        Tcl_InitHashTable(classesTable, TCL_ONE_WORD_KEYS);
        Tcl_SetAssocData(interp, "itk_classesWithOptInfo",
            ItkFreeClassesWithOptInfo, (ClientData)classesTable);
    }
    return classesTable;
}

/*
 * ------------------------------------------------------------------------
 *  ItkFreeClassesWithOptInfo()
 *
 *  When an interpreter is deleted, this procedure is called to
 *  free up the associated data created by ItkGetClassesWithOptInfo.
 * ------------------------------------------------------------------------
 */
static void
ItkFreeClassesWithOptInfo(clientData, interp)
    ClientData clientData;       /* associated data */
    Tcl_Interp *interp;          /* interpreter being freed */
{
    Tcl_HashTable *tablePtr = (Tcl_HashTable*)clientData;
    Tcl_HashSearch place, place2;
    Tcl_HashEntry *entry, *entry2;
    ItkClassOptTable *optTable;
    ItkClassOption *opt;

    entry = Tcl_FirstHashEntry(tablePtr, &place);
    while (entry) {
        optTable = (ItkClassOptTable*)Tcl_GetHashValue(entry);

        entry2 = Tcl_FirstHashEntry(&optTable->options, &place2);
        while (entry2) {
            opt = (ItkClassOption*)Tcl_GetHashValue(entry2);
            Itk_DelClassOption(opt);
            entry2 = Tcl_NextHashEntry(&place2);
        }
        Tcl_DeleteHashTable(&optTable->options);
        Itk_OptListFree(&optTable->order);
        ckfree((char*)optTable);

        entry = Tcl_NextHashEntry(&place);
    }

    Tcl_DeleteHashTable(tablePtr);
    ckfree((char*)tablePtr);
}
