/*
 * ------------------------------------------------------------------------
 *      PACKAGE:  [incr Tk]
 *  DESCRIPTION:  Building mega-widgets with [incr Tcl]
 *
 *  [incr Tk] provides a framework for building composite "mega-widgets"
 *  using [incr Tcl] classes.  It defines a set of base classes that are
 *  specialized to create all other widgets.
 *
 *  This part adds C implementations for some of the methods in the
 *  base class itk::Archetype.
 *
 *    Itk_ArchComponentCmd   <=> itk_component
 *    Itk_ArchOptionCmd      <=> itk_option
 *    Itk_ArchInitCmd        <=> itk_initialize
 *    Itk_ArchCompAccessCmd  <=> component
 *    Itk_ArchConfigureCmd   <=> configure
 *    Itk_ArchCgetCmd        <=> cget
 *
 *    Itk_ArchInitOptsCmd    <=> _initOptionInfo (used to set things up)
 *    Itk_ArchDeleteOptsCmd  <=> _deleteOptionInfo (used to clean things up)
 *
 * ========================================================================
 *  AUTHOR:  Michael J. McLennan
 *           Bell Labs Innovations for Lucent Technologies
 *           mmclennan@lucent.com
 *           http://www.tcltk.com/itcl
 *
 *     RCS:  $Id: itk_archetype.c,v 1.12 2007/05/24 22:12:55 hobbs Exp $
 * ========================================================================
 *           Copyright (c) 1993-1998  Lucent Technologies, Inc.
 * ------------------------------------------------------------------------
 * See the file "license.terms" for information on usage and redistribution
 * of this file, and for a DISCLAIMER OF ALL WARRANTIES.
 */
#include <assert.h>
#include "itk.h"

/*
 *  Info associated with each Archetype mega-widget:
 */
typedef struct ArchInfo {
    ItclObject *itclObj;        /* object containing this info */
    Tk_Window tkwin;            /* window representing this mega-widget */
    Tcl_HashTable components;   /* list of all mega-widget components */
    Tcl_HashTable options;      /* list of all mega-widget options */
    ItkOptList order;           /* gives ordering of options */
} ArchInfo;

/*
 *  Each component widget in an Archetype mega-widget:
 */
typedef struct ArchComponent {
    ItclMember *member;         /* contains protection level for this comp */
    Tcl_Command accessCmd;      /* access command for component widget */
    Tk_Window tkwin;            /* Tk window for this component widget */
    char *pathName;             /* Tk path name for this component widget.
                                   We can't use the tkwin pointer after
                                   the window has been destroyed so we
                                   need to save a copy for use in
                                   Itk_ArchCompDeleteCmd() */
} ArchComponent;

/*
 *  Each option in an Archetype mega-widget:
 */
typedef struct ArchOption {
    char *switchName;           /* command-line switch for this option */
    char *resName;              /* resource name in X11 database */
    char *resClass;             /* resource class name in X11 database */
    char *init;                 /* initial value for option */
    int flags;                  /* flags representing option state */
    Itcl_List parts;            /* parts relating to this option */
} ArchOption;

/*
 *  Flag bits for ArchOption state:
 */
#define ITK_ARCHOPT_INIT  0x01  /* option has been initialized */

/*
 *  Various parts of a composite option in an Archetype mega-widget:
 */
typedef int (Itk_ConfigOptionPartProc) _ANSI_ARGS_((Tcl_Interp *interp,
    ItclObject *contextObj, ClientData cdata, CONST char* newVal));

typedef struct ArchOptionPart {
    ClientData clientData;                 /* data associated with this part */
    Itk_ConfigOptionPartProc *configProc;  /* update when new vals arrive */
    Tcl_CmdDeleteProc *deleteProc;         /* clean up after clientData */

    ClientData from;                       /* token that indicates who
                                            * contributed this option part */
} ArchOptionPart;


/*
 *  Info kept by the itk::option-parser namespace and shared by
 *  all option processing commands:
 */
typedef struct ArchMergeInfo {
    Tcl_HashTable usualCode;      /* usual option handling code for the
                                   * various widget classes */

    ArchInfo *archInfo;           /* internal option info for mega-widget */
    ArchComponent *archComp;      /* component being merged into mega-widget */
    Tcl_HashTable *optionTable;   /* table of valid configuration options
                                   * for component being merged */
} ArchMergeInfo;

/*
 *  Used to capture component widget configuration options when a
 *  new component is being merged into a mega-widget:
 */
typedef struct GenericConfigOpt {
    char *switchName;             /* command-line switch for this option */
    char *resName;                /* resource name in X11 database */
    char *resClass;               /* resource class name in X11 database */
    char *init;                   /* initial value for this option */
    char *value;                  /* current value for this option */
    char **storage;               /* storage for above strings */

    ArchOption *integrated;       /* integrated into this mega-widget option */
    ArchOptionPart *optPart;      /* integrated as this option part */
} GenericConfigOpt;

/*
 *  Options that are propagated by a "configure" method:
 */
typedef struct ConfigCmdline {
    Tcl_Obj *objv[4];           /* objects representing "configure" command */
} ConfigCmdline;


/*
 *  FORWARD DECLARATIONS
 */
static void Itk_DelMergeInfo _ANSI_ARGS_((char* cdata));

static int Itk_ArchInitOptsCmd _ANSI_ARGS_((ClientData cdata,
    Tcl_Interp *interp, int objc, Tcl_Obj *CONST objv[]));
static void Itk_DelArchInfo _ANSI_ARGS_((ClientData cdata));
static int Itk_ArchDeleteOptsCmd _ANSI_ARGS_((ClientData cdata,
    Tcl_Interp *interp, int objc, Tcl_Obj *CONST objv[]));

static int Itk_ArchComponentCmd _ANSI_ARGS_((ClientData cdata,
    Tcl_Interp *interp, int objc, Tcl_Obj *CONST objv[]));
static int Itk_ArchCompAddCmd _ANSI_ARGS_((ClientData cdata,
    Tcl_Interp *interp, int objc, Tcl_Obj *CONST objv[]));
static int Itk_ArchCompDeleteCmd _ANSI_ARGS_((ClientData cdata,
    Tcl_Interp *interp, int objc, Tcl_Obj *CONST objv[]));
static int Itk_ArchOptKeepCmd _ANSI_ARGS_((ClientData cdata,
    Tcl_Interp *interp, int objc, Tcl_Obj *CONST objv[]));
static int Itk_ArchOptIgnoreCmd _ANSI_ARGS_((ClientData cdata,
    Tcl_Interp *interp, int objc, Tcl_Obj *CONST objv[]));
static int Itk_ArchOptRenameCmd _ANSI_ARGS_((ClientData cdata,
    Tcl_Interp *interp, int objc, Tcl_Obj *CONST objv[]));
static int Itk_ArchOptUsualCmd _ANSI_ARGS_((ClientData cdata,
    Tcl_Interp *interp, int objc, Tcl_Obj *CONST objv[]));

static int Itk_ArchInitCmd _ANSI_ARGS_((ClientData cdata,
    Tcl_Interp *interp, int objc, Tcl_Obj *CONST objv[]));
static int Itk_ArchOptionCmd _ANSI_ARGS_((ClientData cdata,
    Tcl_Interp *interp, int objc, Tcl_Obj *CONST objv[]));
static int Itk_ArchOptionAddCmd _ANSI_ARGS_((ClientData cdata,
    Tcl_Interp *interp, int objc, Tcl_Obj *CONST objv[]));
static int Itk_ArchOptionRemoveCmd _ANSI_ARGS_((ClientData cdata,
    Tcl_Interp *interp, int objc, Tcl_Obj *CONST objv[]));

static int Itk_ArchCompAccessCmd _ANSI_ARGS_((ClientData cdata,
    Tcl_Interp *interp, int objc, Tcl_Obj *CONST objv[]));
static int Itk_ArchConfigureCmd _ANSI_ARGS_((ClientData cdata,
    Tcl_Interp *interp, int objc, Tcl_Obj *CONST objv[]));
static int Itk_ArchCgetCmd _ANSI_ARGS_((ClientData cdata,
    Tcl_Interp *interp, int objc, Tcl_Obj *CONST objv[]));
static int Itk_PropagateOption _ANSI_ARGS_((Tcl_Interp *interp,
    ItclObject *contextObj, ClientData cdata, CONST char *newval));
static int Itk_PropagatePublicVar _ANSI_ARGS_((Tcl_Interp *interp,
    ItclObject *contextObj, ClientData cdata, CONST char *newval));

static int Itk_ArchSetOption _ANSI_ARGS_((Tcl_Interp *interp,
    ArchInfo *info, CONST char *name, CONST char *value));
static int Itk_ArchConfigOption _ANSI_ARGS_((Tcl_Interp *interp,
    ArchInfo *info, char *name, char *value));
static void Itk_ArchOptConfigError _ANSI_ARGS_((Tcl_Interp *interp,
    ArchInfo *info, ArchOption *archOpt));
static void Itk_ArchOptAccessError _ANSI_ARGS_((Tcl_Interp *interp,
    ArchInfo *info, ArchOption *archOpt));

static int Itk_GetArchInfo _ANSI_ARGS_((Tcl_Interp *interp,
    ItclObject* contextObj, ArchInfo **infoPtr));

static ArchComponent* Itk_CreateArchComponent _ANSI_ARGS_((
    Tcl_Interp *interp, ArchInfo *info, char *name,
    ItclClass *cdefn, Tcl_Command accessCmd));
static void Itk_DelArchComponent _ANSI_ARGS_((ArchComponent *archComp));

static int Itk_GetArchOption _ANSI_ARGS_((Tcl_Interp *interp,
    ArchInfo *info, char *switchName, char *resName, char *resClass,
    CONST char *defVal, char *currVal, ArchOption **aoPtr));
static void Itk_InitArchOption _ANSI_ARGS_((Tcl_Interp *interp,
    ArchInfo *info, ArchOption *archOpt, CONST char *defVal,
    char *currVal));
static void Itk_DelArchOption _ANSI_ARGS_((ArchOption *archOpt));

static ArchOptionPart* Itk_CreateOptionPart _ANSI_ARGS_((
    Tcl_Interp *interp, ClientData cdata, Itk_ConfigOptionPartProc* cproc,
    Tcl_CmdDeleteProc *dproc, ClientData from));
static int Itk_AddOptionPart _ANSI_ARGS_((Tcl_Interp *interp,
    ArchInfo *info, char *switchName, char *resName, char *resClass,
    CONST char *defVal, char *currVal, ArchOptionPart *optPart,
    ArchOption **raOpt));
static ArchOptionPart* Itk_FindArchOptionPart _ANSI_ARGS_((
    ArchInfo *info, char *switchName, ClientData from));
static int Itk_RemoveArchOptionPart _ANSI_ARGS_((ArchInfo *info,
    char *switchName, ClientData from));
static int Itk_IgnoreArchOptionPart _ANSI_ARGS_((ArchInfo *info,
    GenericConfigOpt *opt));
static void Itk_DelOptionPart _ANSI_ARGS_((ArchOptionPart *optPart));

static ConfigCmdline* Itk_CreateConfigCmdline _ANSI_ARGS_((
    Tcl_Interp *interp, Tcl_Command accessCmd, char *switchName));
static void Itk_DeleteConfigCmdline _ANSI_ARGS_((ClientData cdata));

static Tcl_HashTable* Itk_CreateGenericOptTable _ANSI_ARGS_((Tcl_Interp *interp,
    char *options));
static void Itk_DelGenericOptTable _ANSI_ARGS_((Tcl_HashTable *tPtr));

static GenericConfigOpt* Itk_CreateGenericOpt _ANSI_ARGS_((Tcl_Interp *interp,
    char *switchName, Tcl_Command accessCmd));
static void Itk_DelGenericOpt _ANSI_ARGS_((GenericConfigOpt* opt));

static Tcl_HashTable* ItkGetObjsWithArchInfo _ANSI_ARGS_((Tcl_Interp *interp));
static void ItkFreeObjsWithArchInfo _ANSI_ARGS_((ClientData cdata,
    Tcl_Interp *interp));


/*
 * ------------------------------------------------------------------------
 *  Itk_ArchetypeInit()
 *
 *  Invoked by Itk_Init() whenever a new interpreter is created to
 *  declare the procedures used in the itk::Archetype base class.
 * ------------------------------------------------------------------------
 */
int
Itk_ArchetypeInit(interp)
    Tcl_Interp *interp;  /* interpreter to be updated */
{
    ArchMergeInfo *mergeInfo;
    Tcl_Namespace *parserNs;

    /*
     *  Declare all of the C routines that are integrated into
     *  the Archetype base class.
     */
    if (Itcl_RegisterObjC(interp,
            "Archetype-init", Itk_ArchInitOptsCmd,
            (ClientData)NULL, (Tcl_CmdDeleteProc*)NULL) != TCL_OK ||

        Itcl_RegisterObjC(interp,
            "Archetype-delete", Itk_ArchDeleteOptsCmd,
            (ClientData)NULL, (Tcl_CmdDeleteProc*)NULL) != TCL_OK ||

        Itcl_RegisterObjC(interp,
            "Archetype-itk_component", Itk_ArchComponentCmd,
            (ClientData)NULL, (Tcl_CmdDeleteProc*)NULL) != TCL_OK ||

        Itcl_RegisterObjC(interp,
            "Archetype-itk_option", Itk_ArchOptionCmd,
            (ClientData)NULL, (Tcl_CmdDeleteProc*)NULL) != TCL_OK ||

        Itcl_RegisterObjC(interp,
            "Archetype-itk_initialize", Itk_ArchInitCmd,
            (ClientData)NULL, (Tcl_CmdDeleteProc*)NULL) != TCL_OK ||

        Itcl_RegisterObjC(interp,
            "Archetype-component", Itk_ArchCompAccessCmd,
            (ClientData)NULL, (Tcl_CmdDeleteProc*)NULL) != TCL_OK ||

        Itcl_RegisterObjC(interp,
            "Archetype-configure",Itk_ArchConfigureCmd,
            (ClientData)NULL, (Tcl_CmdDeleteProc*)NULL) != TCL_OK ||

        Itcl_RegisterObjC(interp,
            "Archetype-cget",Itk_ArchCgetCmd,
            (ClientData)NULL, (Tcl_CmdDeleteProc*)NULL) != TCL_OK) {

        return TCL_ERROR;
    }

    /*
     *  Create the namespace containing the option parser commands.
     */
    mergeInfo = (ArchMergeInfo*)ckalloc(sizeof(ArchMergeInfo));
    Tcl_InitHashTable(&mergeInfo->usualCode, TCL_STRING_KEYS);
    mergeInfo->archInfo    = NULL;
    mergeInfo->archComp    = NULL;
    mergeInfo->optionTable = NULL;

    parserNs = Tcl_CreateNamespace(interp, "::itk::option-parser",
        (ClientData)mergeInfo, Itcl_ReleaseData);

    if (!parserNs) {
        Itk_DelMergeInfo((char*)mergeInfo);
        Tcl_AddErrorInfo(interp, "\n    (while initializing itk)");
        return TCL_ERROR;
    }
    Itcl_PreserveData((ClientData)mergeInfo);
    Itcl_EventuallyFree((ClientData)mergeInfo, Itk_DelMergeInfo);

    Tcl_CreateObjCommand(interp, "::itk::option-parser::keep",
        Itk_ArchOptKeepCmd,
        (ClientData)mergeInfo, (Tcl_CmdDeleteProc*)NULL);

    Tcl_CreateObjCommand(interp, "::itk::option-parser::ignore",
        Itk_ArchOptIgnoreCmd,
        (ClientData)mergeInfo, (Tcl_CmdDeleteProc*)NULL);

    Tcl_CreateObjCommand(interp, "::itk::option-parser::rename",
        Itk_ArchOptRenameCmd,
        (ClientData)mergeInfo, (Tcl_CmdDeleteProc*)NULL);

    Tcl_CreateObjCommand(interp, "::itk::option-parser::usual",
        Itk_ArchOptUsualCmd,
        (ClientData)mergeInfo, (Tcl_CmdDeleteProc*)NULL);

    /*
     *  Add the "itk::usual" command to register option handling code.
     */
    Tcl_CreateObjCommand(interp, "::itk::usual", Itk_UsualCmd,
        (ClientData)mergeInfo, Itcl_ReleaseData);
    Itcl_PreserveData((ClientData)mergeInfo);

    return TCL_OK;
}


/*
 * ------------------------------------------------------------------------
 *  Itk_DelMergeInfo()
 *
 *  Destroys the "merge" info record shared by commands in the
 *  itk::option-parser namespace.  Invoked automatically when the
 *  namespace containing the parsing commands is destroyed and there
 *  are no more uses of the data.
 * ------------------------------------------------------------------------
 */
static void
Itk_DelMergeInfo(cdata)
    char* cdata;  /* data to be destroyed */
{
    ArchMergeInfo *mergeInfo = (ArchMergeInfo*)cdata;

    Tcl_HashEntry *entry;
    Tcl_HashSearch place;
    Tcl_Obj *codePtr;

    assert(mergeInfo->optionTable == NULL);

    entry = Tcl_FirstHashEntry(&mergeInfo->usualCode, &place);
    while (entry) {
        codePtr = (Tcl_Obj*)Tcl_GetHashValue(entry);
        Tcl_DecrRefCount(codePtr);
        entry = Tcl_NextHashEntry(&place);
    }
    Tcl_DeleteHashTable(&mergeInfo->usualCode);

    ckfree((char*)mergeInfo);
}


/*
 * ------------------------------------------------------------------------
 *  Itk_ArchInitOptsCmd()
 *
 *  Invoked by [incr Tcl] to handle the itk::Archetype::_initOptionInfo
 *  method.  This method should be called out in the constructor for
 *  each object, to initialize the object so that it can be used with
 *  the other access methods in this file.  Allocates some extra
 *  data associated with the object at the C-language level.
 *
 *  Returns TCL_OK/TCL_ERROR to indicate success/failure.
 * ------------------------------------------------------------------------
 */
/* ARGSUSED */
static int
Itk_ArchInitOptsCmd(dummy, interp, objc, objv)
    ClientData dummy;        /* unused */
    Tcl_Interp *interp;      /* current interpreter */
    int objc;                /* number of arguments */
    Tcl_Obj *CONST objv[];   /* argument objects */
{
    int newEntry, result;
    ArchInfo *info;
    ItclClass *contextClass;
    ItclObject *contextObj;
    Tcl_HashTable *objsWithArchInfo;
    Tcl_HashEntry *entry;
    Command *cmdPtr;

    if (objc != 1) {
        Tcl_WrongNumArgs(interp, 1, objv, "");
        return TCL_ERROR;
    }

    if (Itcl_GetContext(interp, &contextClass, &contextObj) != TCL_OK ||
        !contextObj) {

        char *token = Tcl_GetStringFromObj(objv[0], (int*)NULL);
        Tcl_ResetResult(interp);
        Tcl_AppendResult(interp,
            "cannot use \"", token, "\" without an object context",
            (char*)NULL);
        return TCL_ERROR;
    }

    /*
     *  Create some archetype info for the current object and
     *  register it on the list of all known objects.
     */
    objsWithArchInfo = ItkGetObjsWithArchInfo(interp);

    info = (ArchInfo*)ckalloc(sizeof(ArchInfo));
    info->itclObj = contextObj;
    info->tkwin = NULL;  /* not known yet */
    Tcl_InitHashTable(&info->components, TCL_STRING_KEYS);
    Tcl_InitHashTable(&info->options, TCL_STRING_KEYS);
    Itk_OptListInit(&info->order, &info->options);

    entry = Tcl_CreateHashEntry(objsWithArchInfo, (char*)contextObj, &newEntry);
    if (!newEntry) {
        Itk_DelArchInfo( Tcl_GetHashValue(entry) );
    }
    Tcl_SetHashValue(entry, (ClientData)info);

    /*
     *  Make sure that the access command for this object
     *  resides in the global namespace.  If need be, move
     *  the command.
     */
    result = TCL_OK;
    cmdPtr = (Command*)contextObj->accessCmd;

    if (cmdPtr->nsPtr != (Namespace*)Tcl_GetGlobalNamespace(interp)) {
        Tcl_Obj *oldNamePtr, *newNamePtr;

        oldNamePtr = Tcl_NewStringObj((char*)NULL, 0);
        Tcl_GetCommandFullName(interp, contextObj->accessCmd, oldNamePtr);
        Tcl_IncrRefCount(oldNamePtr);

        newNamePtr = Tcl_NewStringObj("::", -1);
        Tcl_AppendToObj(newNamePtr,
            Tcl_GetCommandName(interp, contextObj->accessCmd), -1);
        Tcl_IncrRefCount(newNamePtr);

        result = TclRenameCommand(interp,
            Tcl_GetStringFromObj(oldNamePtr, (int*)NULL),
            Tcl_GetStringFromObj(newNamePtr, (int*)NULL));

        Tcl_DecrRefCount(oldNamePtr);
        Tcl_DecrRefCount(newNamePtr);
    }

    return result;
}


/*
 * ------------------------------------------------------------------------
 *  Itk_DelArchInfo()
 *
 *  Invoked when the option info associated with an itk::Archetype
 *  widget is no longer needed.  This usually happens when a widget
 *  is destroyed.  Frees the given bundle of data and removes it
 *  from the global list of Archetype objects.
 * ------------------------------------------------------------------------
 */
static void
Itk_DelArchInfo(cdata)
    ClientData cdata;    /* client data for Archetype objects */
{
    ArchInfo *info = (ArchInfo*)cdata;

    Tcl_HashEntry *entry;
    Tcl_HashSearch place;
    ArchOption *archOpt;
    ArchComponent *archComp;

    /*
     *  Destroy all component widgets.
     */
    entry = Tcl_FirstHashEntry(&info->components, &place);
    while (entry) {
        archComp = (ArchComponent*)Tcl_GetHashValue(entry);
        Itk_DelArchComponent(archComp);
        entry = Tcl_NextHashEntry(&place);
    }
    Tcl_DeleteHashTable(&info->components);

    /*
     *  Destroy all information associated with configuration options.
     */
    entry = Tcl_FirstHashEntry(&info->options, &place);
    while (entry) {
        archOpt = (ArchOption*)Tcl_GetHashValue(entry);
        Itk_DelArchOption(archOpt);
        entry = Tcl_NextHashEntry(&place);
    }
    Tcl_DeleteHashTable(&info->options);
    Itk_OptListFree(&info->order);

    ckfree((char*)info);
}


/*
 * ------------------------------------------------------------------------
 *  Itk_ArchDeleteOptsCmd()
 *
 *  Invoked by [incr Tcl] to handle the itk::Archetype::_deleteOptionInfo
 *  method.  This method should be called out in the destructor for each
 *  object, to clean up data allocated by Itk_ArchInitOptsCmd().
 *
 *  Returns TCL_OK/TCL_ERROR to indicate success/failure.
 * ------------------------------------------------------------------------
 */
/* ARGSUSED */
static int
Itk_ArchDeleteOptsCmd(dummy, interp, objc, objv)
    ClientData dummy;        /* unused */
    Tcl_Interp *interp;      /* current interpreter */
    int objc;                /* number of arguments */
    Tcl_Obj *CONST objv[];   /* argument objects */
{
    ItclClass *contextClass;
    ItclObject *contextObj;
    Tcl_HashTable *objsWithArchInfo;
    Tcl_HashEntry *entry;

    if (objc != 1) {
        Tcl_WrongNumArgs(interp, 1, objv, "");
        return TCL_ERROR;
    }
    if (Itcl_GetContext(interp, &contextClass, &contextObj) != TCL_OK ||
        !contextObj) {

        char *token = Tcl_GetStringFromObj(objv[0], (int*)NULL);
        Tcl_ResetResult(interp);
        Tcl_AppendResult(interp,
            "cannot use \"", token, "\" without an object context",
            (char*)NULL);
        return TCL_ERROR;
    }

    /*
     *  Find the info associated with this object.
     *  Destroy the data and remove it from the global list.
     */
    objsWithArchInfo = ItkGetObjsWithArchInfo(interp);
    entry = Tcl_FindHashEntry(objsWithArchInfo, (char*)contextObj);

    if (entry) {
        Itk_DelArchInfo( Tcl_GetHashValue(entry) );
        Tcl_DeleteHashEntry(entry);
    }
    return TCL_OK;
}


/*
 * ------------------------------------------------------------------------
 *  Itk_ArchComponentCmd()
 *
 *  Invoked by [incr Tcl] to handle the itk::Archetype::itk_component
 *  method.  Handles the following options:
 *
 *      itk_component add ?-protected? ?-private? ?--? <name> \
 *          <createCmds> ?<optionCmds>?
 *
 *      itk_component delete <name> ?<name>...?
 *
 *  Returns TCL_OK/TCL_ERROR to indicate success/failure.
 * ------------------------------------------------------------------------
 */
/* ARGSUSED */
static int
Itk_ArchComponentCmd(dummy, interp, objc, objv)
    ClientData dummy;        /* unused */
    Tcl_Interp *interp;      /* current interpreter */
    int objc;                /* number of arguments */
    Tcl_Obj *CONST objv[];   /* argument objects */
{
    char *cmd, *token, c;
    int length;

    /*
     *  Check arguments and handle the various options...
     */
    if (objc < 2) {
        cmd = Tcl_GetStringFromObj(objv[0], (int*)NULL);
        Tcl_AppendResult(interp,
            "wrong # args: should be one of...\n",
            "  ", cmd, " add ?-protected? ?-private? ?--? name createCmds ?optionCmds?\n",
            "  ", cmd, " delete name ?name name...?",
            (char*)NULL);
        return TCL_ERROR;
    }

    token = Tcl_GetStringFromObj(objv[1], (int*)NULL);
    c = *token;
    length = strlen(token);

    /*
     *  Handle:  itk_component add...
     */
    if (c == 'a' && strncmp(token, "add", length) == 0) {
        if (objc < 4) {
            Tcl_WrongNumArgs(interp, 1, objv,
                "add ?-protected? ?-private? ?--? name createCmds ?optionCmds?");
            return TCL_ERROR;
        }
        return Itk_ArchCompAddCmd(dummy, interp, objc-1, objv+1);
    }

    /*
     *  Handle:  itk_component delete...
     */
    else if (c == 'd' && strncmp(token, "delete", length) == 0) {
        if (objc < 3) {
            Tcl_WrongNumArgs(interp, 1, objv, "delete name ?name name...?");
            return TCL_ERROR;
        }
        return Itk_ArchCompDeleteCmd(dummy, interp, objc-1, objv+1);
    }

    /*
     *  Flag any errors.
     */
    cmd = Tcl_GetStringFromObj(objv[0], (int*)NULL);
    Tcl_AppendResult(interp,
        "bad option \"", token,
        "\": should be one of...\n",
        "  ", cmd, " add name createCmds ?optionCmds?\n",
        "  ", cmd, " delete name ?name name...?",
        (char*)NULL);
    return TCL_ERROR;
}


/*
 * ------------------------------------------------------------------------
 *  Itk_ArchCompAddCmd()
 *
 *  Invoked by [incr Tcl] to handle the itk::Archetype::itk_component
 *  method.  Adds a new component widget into the mega-widget,
 *  integrating its configuration options into the master list.
 *
 *      itk_component add ?-protected? ?-private? ?--? <name> \
 *          <createCmds> <optionCmds>
 *
 *  Returns TCL_OK/TCL_ERROR to indicate success/failure.
 * ------------------------------------------------------------------------
 */
/* ARGSUSED */
static int
Itk_ArchCompAddCmd(dummy, interp, objc, objv)
    ClientData dummy;        /* unused */
    Tcl_Interp *interp;      /* current interpreter */
    int objc;                /* number of arguments */
    Tcl_Obj *CONST objv[];   /* argument objects */
{
    Tcl_HashEntry *entry = NULL;
    char *path = NULL;
    ArchComponent *archComp = NULL;
    ArchMergeInfo *mergeInfo = NULL;
    Tcl_Obj *objNamePtr = NULL;
    Tcl_Obj *tmpNamePtr = NULL;
    Tcl_Obj *winNamePtr = NULL;
    Tcl_Obj *hullNamePtr = NULL;
    int pLevel = ITCL_PUBLIC;

    int newEntry, result;
    CONST char *cmd, *token, *resultStr;
    char *name;
    Tcl_Namespace *parserNs;
    ItclClass *contextClass, *ownerClass;
    ItclObject *contextObj;
    ArchInfo *info;
    Itcl_CallFrame frame, *uplevelFramePtr, *oldFramePtr;
    Tcl_Command accessCmd;
    Tcl_Obj *objPtr;
    Tcl_DString buffer;

    /*
     *  Get the Archetype info associated with this widget.
     */
    if (Itcl_GetContext(interp, &contextClass, &contextObj) != TCL_OK ||
        !contextObj) {

        Tcl_ResetResult(interp);
        Tcl_AppendResult(interp,
            "cannot access components without an object context",
            (char*)NULL);
        return TCL_ERROR;
    }

    if (Itk_GetArchInfo(interp, contextObj, &info) != TCL_OK) {
        return TCL_ERROR;
    }

    /*
     *  Look for options like "-protected" or "-private".
     */
    cmd = Tcl_GetStringFromObj(objv[0], (int*)NULL);

    while (objc > 1) {
        token = Tcl_GetStringFromObj(objv[1], (int*)NULL);
        if (*token != '-') {
            break;
        }
        else if (strcmp(token,"-protected") == 0) {
            pLevel = ITCL_PROTECTED;
        }
        else if (strcmp(token,"-private") == 0) {
            pLevel = ITCL_PRIVATE;
        }
        else if (strcmp(token,"--") == 0) {
            objc--;
            objv++;
            break;
        }
        else {
            Tcl_AppendResult(interp,
                "bad option \"", token,
                "\": should be -private, -protected or --",
                (char*)NULL);
            return TCL_ERROR;
        }
        objc--;
        objv++;
    }

    if (objc < 3 || objc > 4) {
        Tcl_AppendResult(interp,
            "wrong # args: should be \"", cmd,
            " ?-protected? ?-private? ?--? name createCmds ?optionCmds?",
            (char*)NULL);
        return TCL_ERROR;
    }

    /*
     *  See if a component already exists with the symbolic name.
     */
    name = Tcl_GetStringFromObj(objv[1], (int*)NULL);
    entry = Tcl_CreateHashEntry(&info->components, name, &newEntry);
    if (!newEntry) {
        Tcl_AppendResult(interp,
            "component \"", name, "\" already defined",
            (char*)NULL);
        return TCL_ERROR;
    }

    /*
     *  If this component is the "hull" for the mega-widget, then
     *  move the object access command out of the way before
     *  creating the component, so it is not accidentally deleted.
     */
    Tcl_DStringInit(&buffer);

    objNamePtr = Tcl_NewStringObj((char*)NULL, 0);
    Tcl_GetCommandFullName(contextObj->classDefn->interp,
        contextObj->accessCmd, objNamePtr);
    Tcl_IncrRefCount(objNamePtr);

    if (strcmp(name, "hull") == 0) {
        tmpNamePtr = Tcl_NewStringObj((char*)NULL, 0);
        Tcl_GetCommandFullName(contextObj->classDefn->interp,
            contextObj->accessCmd, tmpNamePtr);
        Tcl_AppendToObj(tmpNamePtr, "-widget-", -1);
        Tcl_IncrRefCount(tmpNamePtr);
        
        result = TclRenameCommand(interp,
            Tcl_GetStringFromObj(objNamePtr, (int*)NULL),
            Tcl_GetStringFromObj(tmpNamePtr, (int*)NULL));

        if (result != TCL_OK) {
            goto compFail;
        }
    }

    /*
     *  Execute the <createCmds> to create the component widget.
     *  Do this one level up, in the scope of the calling routine.
     */
    uplevelFramePtr = _Tcl_GetCallFrame(interp, 1);
    oldFramePtr = _Tcl_ActivateCallFrame(interp, uplevelFramePtr);

    if (Tcl_EvalObj(interp, objv[2]) != TCL_OK) {
        goto compFail;
    }

    /*
     *  Take the result from the widget creation commands as the
     *  path name for the new component.  Make a local copy of
     *  this, since the interpreter will get used in the mean time.
     */
    resultStr = Tcl_GetStringResult(interp);
    path = (char*)ckalloc((unsigned)(strlen(resultStr)+1));
    strcpy(path, resultStr);

    /*
     *  Look for the access command token in the context of the
     *  calling namespace.  By-pass any protection at this point.
     */
    accessCmd = Tcl_FindCommand(interp, path, (Tcl_Namespace*)NULL,
        /* flags */ 0);

    if (!accessCmd) {
        Tcl_ResetResult(interp);
        Tcl_AppendResult(interp,
           "cannot find component access command \"",
            path, "\" for component \"", name, "\"",
            (char*)NULL);
        goto compFail;
    }

    winNamePtr = Tcl_NewStringObj((char*)NULL, 0);
    Tcl_GetCommandFullName(interp, accessCmd, winNamePtr);
    Tcl_IncrRefCount(winNamePtr);

    (void) _Tcl_ActivateCallFrame(interp, oldFramePtr);

    /*
     *  Create the component record.  Set the protection level
     *  according to the "-protected" or "-private" option.
     */
    ownerClass = contextClass;
    uplevelFramePtr = _Tcl_GetCallFrame(interp, 1);
    if (uplevelFramePtr && Itcl_IsClassNamespace(uplevelFramePtr->nsPtr)) {
        ownerClass = (ItclClass*)uplevelFramePtr->nsPtr->clientData;
    }

    archComp = Itk_CreateArchComponent(interp, info, name, ownerClass,
        accessCmd);

    if (!archComp) {
        goto compFail;
    }

    Tcl_SetHashValue(entry, (ClientData)archComp);
    archComp->member->protection = pLevel;

    /*
     *  If this component is the "hull" for the mega-widget, then
     *  move the hull widget access command to a different name,
     *  and move the object access command back into place.  This
     *  way, when the widget name is used as a command, the object
     *  access command will handle all requests.
     */
    if (strcmp(name, "hull") == 0) {
        hullNamePtr = Tcl_NewStringObj((char*)NULL, 0);
        Tcl_GetCommandFullName(interp, accessCmd, hullNamePtr);
        Tcl_AppendToObj(hullNamePtr, "-itk_hull", -1);
        Tcl_IncrRefCount(hullNamePtr);

        result = TclRenameCommand(interp,
            Tcl_GetStringFromObj(winNamePtr, (int*)NULL),
            Tcl_GetStringFromObj(hullNamePtr, (int*)NULL));

        if (result != TCL_OK) {
            goto compFail;
        }

        Tcl_DecrRefCount(winNamePtr);  /* winNamePtr keeps current name */
        winNamePtr = hullNamePtr;
        hullNamePtr = NULL;

        result = TclRenameCommand(interp,
            Tcl_GetStringFromObj(tmpNamePtr, (int*)NULL),
            Tcl_GetStringFromObj(objNamePtr, (int*)NULL));

        if (result != TCL_OK) {
            goto compFail;
        }
    }

    /*
     *  Add a binding onto the new component, so that when its
     *  window is destroyed, it will automatically remove itself
     *  from its parent's component list.  Avoid doing these things
     *  for the "hull" component, since it is a special case and
     *  these things are not really necessary.
     */
    else {
        Tcl_DStringSetLength(&buffer, 0);
        Tcl_DStringAppend(&buffer, "bindtags ", -1);
        Tcl_DStringAppend(&buffer, path, -1);
        if (Tcl_Eval(interp, Tcl_DStringValue(&buffer)) != TCL_OK) {
            goto compFail;
        }

        Tcl_DStringSetLength(&buffer, 0);
        Tcl_DStringAppend(&buffer, "bind itk-destroy-", -1);
        Tcl_DStringAppend(&buffer, path, -1);
        Tcl_DStringAppend(&buffer, " <Destroy> [itcl::code ", -1);

        Tcl_DStringAppend(&buffer,
            Tcl_GetStringFromObj(objNamePtr,(int*)NULL), -1);

        Tcl_DStringAppend(&buffer, " itk_component delete ", -1);
        Tcl_DStringAppend(&buffer, name, -1);
        Tcl_DStringAppend(&buffer, "]\n", -1);
        Tcl_DStringAppend(&buffer, "bindtags ", -1);
        Tcl_DStringAppend(&buffer, path, -1);
        Tcl_DStringAppend(&buffer, " {itk-destroy-", -1);
        Tcl_DStringAppend(&buffer, path, -1);
        Tcl_DStringAppend(&buffer, " ", -1);
        Tcl_DStringAppend(&buffer, Tcl_GetStringResult(interp), -1);
        Tcl_DStringAppend(&buffer, "}", -1);
        if (Tcl_Eval(interp, Tcl_DStringValue(&buffer)) != TCL_OK) {
            goto compFail;
        }
    }

    /*
     *  Query the list of configuration options for this widget,
     *  so we will know which ones are valid.  Build an option
     *  table to represent these, so they can be found quickly
     *  by the option parsing commands in "itk::option-parser".
     */
    Tcl_DStringTrunc(&buffer, 0);
    Tcl_DStringAppendElement(&buffer,
        Tcl_GetStringFromObj(winNamePtr, (int*)NULL));
    Tcl_DStringAppendElement(&buffer, "configure");

    result = Tcl_Eval(interp, Tcl_DStringValue(&buffer));

    if (result != TCL_OK) {
        goto compFail;
    }
    Tcl_DStringSetLength(&buffer, 0);
    Tcl_DStringAppend(&buffer, Tcl_GetStringResult(interp), -1);

    /*
     *  Find the "itk::option-parser" namespace and get the data
     *  record shared by all of the parsing commands.
     */
    parserNs = Tcl_FindNamespace(interp, "::itk::option-parser",
        (Tcl_Namespace*)NULL, TCL_LEAVE_ERR_MSG);

    if (!parserNs) {
        goto compFail;
    }
    mergeInfo = (ArchMergeInfo*)parserNs->clientData;
    assert(mergeInfo);

    /*
     *  Initialize the data record used by the option parsing commands.
     *  Store a table of valid configuration options, along with the
     *  info for the mega-widget that is being updated.
     */
    mergeInfo->optionTable = Itk_CreateGenericOptTable(interp,
        Tcl_DStringValue(&buffer));

    if (!mergeInfo->optionTable) {
        goto compFail;
    }
    mergeInfo->archInfo = info;
    mergeInfo->archComp = archComp;

    /*
     *  Execute the option-handling commands in the "itk::option-parser"
     *  namespace.  If there are no option-handling commands, invoke
     *  the "usual" command instead.
     */
    if (objc != 4) {
        objPtr = Tcl_NewStringObj("usual", -1);
        Tcl_IncrRefCount(objPtr);
    } else {
        objPtr = objv[3];
    }

    result = Tcl_PushCallFrame(interp, (Tcl_CallFrame *) &frame,
        parserNs, /* isProcCallFrame */ 0);

    if (result == TCL_OK) {
        result = Tcl_EvalObj(interp, objPtr);
        Tcl_PopCallFrame(interp);
    }

    if (objPtr != objv[3]) {
        Tcl_DecrRefCount(objPtr);
    }
    if (result != TCL_OK) {
        goto compFail;
    }

    Itk_DelGenericOptTable(mergeInfo->optionTable);
    mergeInfo->optionTable = NULL;
    mergeInfo->archInfo    = NULL;
    mergeInfo->archComp    = NULL;

    ckfree(path);

    Tcl_DStringFree(&buffer);
    if (objNamePtr) {
        Tcl_DecrRefCount(objNamePtr);
    }
    if (tmpNamePtr) {
        Tcl_DecrRefCount(tmpNamePtr);
    }
    if (winNamePtr) {
        Tcl_DecrRefCount(winNamePtr);
    }
    if (hullNamePtr) {
        Tcl_DecrRefCount(hullNamePtr);
    }

    Tcl_SetResult(interp, name, TCL_VOLATILE);
    return TCL_OK;

    /*
     *  If any errors were encountered, clean up and return.
     */
compFail:
    if (archComp) {
        Itk_DelArchComponent(archComp);
    }
    if (entry) {
        Tcl_DeleteHashEntry(entry);
    }
    if (path) {
        ckfree(path);
    }
    if (mergeInfo && mergeInfo->optionTable) {
        Itk_DelGenericOptTable(mergeInfo->optionTable);
        mergeInfo->optionTable = NULL;
        mergeInfo->archInfo    = NULL;
        mergeInfo->archComp    = NULL;
    }

    Tcl_DStringFree(&buffer);
    if (objNamePtr) {
        Tcl_DecrRefCount(objNamePtr);
    }
    if (tmpNamePtr) {
        Tcl_DecrRefCount(tmpNamePtr);
    }
    if (winNamePtr) {
        Tcl_DecrRefCount(winNamePtr);
    }
    if (hullNamePtr) {
        Tcl_DecrRefCount(hullNamePtr);
    }

    /*
     *  Add error info and return.
     */
    objPtr = Tcl_NewStringObj((char*)NULL, 0);
    Tcl_AppendToObj(objPtr, "\n    (while creating component \"", -1);
    Tcl_AppendToObj(objPtr, name, -1);
    Tcl_AppendToObj(objPtr, "\" for widget \"", -1);
    Tcl_GetCommandFullName(contextObj->classDefn->interp,
        contextObj->accessCmd, objPtr);
    Tcl_AppendToObj(objPtr, "\")", -1);
    Tcl_IncrRefCount(objPtr);

    Tcl_AddErrorInfo(interp, Tcl_GetStringFromObj(objPtr, (int*)NULL));
    Tcl_DecrRefCount(objPtr);


    return TCL_ERROR;
}


/*
 * ------------------------------------------------------------------------
 *  Itk_ArchCompDeleteCmd()
 *
 *  Invoked by [incr Tcl] to handle the itk::Archetype::itk_component
 *  method.  Removes an existing component widget from a mega-widget,
 *  and removes any configuration options associated with it.
 *
 *      itk_component delete <name> ?<name> <name>...?
 *
 *  Returns TCL_OK/TCL_ERROR to indicate success/failure.
 * ------------------------------------------------------------------------
 */
/* ARGSUSED */
static int
Itk_ArchCompDeleteCmd(dummy, interp, objc, objv)
    ClientData dummy;        /* unused */
    Tcl_Interp *interp;      /* current interpreter */
    int objc;                /* number of arguments */
    Tcl_Obj *CONST objv[];   /* argument objects */
{
    int i;
    char *token;
    ItclClass *contextClass;
    ItclObject *contextObj;
    ArchInfo *info;
    Tcl_HashEntry *entry;
    Tcl_HashSearch place;
    Itcl_ListElem *elem;
    ArchComponent *archComp;
    ArchOption *archOpt;
    ArchOptionPart *optPart;
    Itcl_List delOptList;
    Tcl_DString buffer;

    /*
     *  Get the Archetype info associated with this widget.
     */
    if (Itcl_GetContext(interp, &contextClass, &contextObj) != TCL_OK ||
        !contextObj) {

        Tcl_ResetResult(interp);
        Tcl_AppendResult(interp,
            "cannot access components without an object context",
            (char*)NULL);
        return TCL_ERROR;
    }
    if (Itk_GetArchInfo(interp, contextObj, &info) != TCL_OK) {
        return TCL_ERROR;
    }

    /*
     *  Scan through the list of component names and delete each
     *  one.  Make sure that each component exists.
     */
    for (i=1; i < objc; i++) {
        token = Tcl_GetStringFromObj(objv[i], (int*)NULL);
        entry = Tcl_FindHashEntry(&info->components, token);
        if (!entry) {
            Tcl_AppendResult(interp,
                "name \"", token, "\" is not a component",
                (char*)NULL);
            return TCL_ERROR;
        }
        archComp = (ArchComponent*)Tcl_GetHashValue(entry);

       /*
        *  Clean up the binding tag that causes the widget to
        *  call this method automatically when destroyed.
        *  Ignore errors if anything goes wrong.
        */
        Tcl_DStringInit(&buffer);
        Tcl_DStringAppend(&buffer, "itk::remove_destroy_hook ", -1);
        Tcl_DStringAppend(&buffer, archComp->pathName, -1);
        (void) Tcl_Eval(interp, Tcl_DStringValue(&buffer));
        Tcl_ResetResult(interp);
        Tcl_DStringFree(&buffer);

        Tcl_UnsetVar2(interp, "itk_component", token, 0);
        Tcl_DeleteHashEntry(entry);

        /*
         *  Clean up the options that belong to the component.  Do this
         *  by scanning through all available options and looking for
         *  those that belong to the component.  If we remove them as
         *  we go, we'll mess up Tcl_NextHashEntry.  So instead, we
         *  build up a list of options to remove, and then remove the
         *  options below.
         */
        Itcl_InitList(&delOptList);
        entry = Tcl_FirstHashEntry(&info->options, &place);
        while (entry) {
            archOpt = (ArchOption*)Tcl_GetHashValue(entry);
            elem = Itcl_FirstListElem(&archOpt->parts);
            while (elem) {
                optPart = (ArchOptionPart*)Itcl_GetListValue(elem);
                if (optPart->from == (ClientData)archComp) {
                    Itcl_AppendList(&delOptList, (ClientData)entry);
                }
                elem = Itcl_NextListElem(elem);
            }
            entry = Tcl_NextHashEntry(&place);
        }

        /*
         *  Now that we've figured out which options to delete,
         *  go through the list and remove them.
         */
        elem = Itcl_FirstListElem(&delOptList);
        while (elem) {
            entry = (Tcl_HashEntry*)Itcl_GetListValue(elem);
            token = Tcl_GetHashKey(&info->options, entry);

            Itk_RemoveArchOptionPart(info, token, (ClientData)archComp);

            elem = Itcl_NextListElem(elem);
        }
        Itcl_DeleteList(&delOptList);

        Itk_DelArchComponent(archComp);
    }
    return TCL_OK;
}


/*
 * ------------------------------------------------------------------------
 *  Itk_ArchOptKeepCmd()
 *
 *  Invoked by [incr Tcl] to handle the "keep" command in the itk
 *  option parser.  Integrates a list of component configuration options
 *  into a mega-widget, so that whenever the mega-widget is updated,
 *  the component will be updated as well.
 *
 *  Handles the following syntax:
 *
 *      keep <option> ?<option>...?
 *
 *  Returns TCL_OK/TCL_ERROR to indicate success/failure.
 * ------------------------------------------------------------------------
 */
/* ARGSUSED */
static int
Itk_ArchOptKeepCmd(clientData, interp, objc, objv)
    ClientData clientData;   /* option merging info record */
    Tcl_Interp *interp;      /* current interpreter */
    int objc;                /* number of arguments */
    Tcl_Obj *CONST objv[];   /* argument objects */
{
    ArchMergeInfo *mergeInfo = (ArchMergeInfo*)clientData;
    int result = TCL_OK;

    int i;
    char *token;
    Tcl_HashEntry *entry;
    GenericConfigOpt *opt;
    ArchOption *archOpt;
    ArchOptionPart *optPart;
    ConfigCmdline *cmdlinePtr;

    if (objc < 2) {
        Tcl_WrongNumArgs(interp, 1, objv, "option ?option...?");
        return TCL_ERROR;
    }

    /*
     *  Make sure that this command is being accessed in the
     *  proper context.  The merge info record should be set up
     *  properly.
     */
    if (!mergeInfo->archInfo || !mergeInfo->optionTable) {
        token = Tcl_GetStringFromObj(objv[0], (int*)NULL);
        Tcl_AppendResult(interp,
            "improper usage: \"", token,
            "\" should only be accessed via itk_component",
            (char*)NULL);
        return TCL_ERROR;
    }

    /*
     *  Scan through all of the options on the list, and make
     *  sure that they are valid options for this component.
     *  Integrate them into the option info for the mega-widget.
     */
    for (i=1; i < objc; i++) {
        token = Tcl_GetStringFromObj(objv[i], (int*)NULL);
        entry = Tcl_FindHashEntry(mergeInfo->optionTable, token);
        if (!entry) {
            Tcl_AppendResult(interp,
                "option not recognized: ", token,
                (char*)NULL);
            result = TCL_ERROR;
            break;
        }
        opt = (GenericConfigOpt*)Tcl_GetHashValue(entry);

        /*
         *  If this option has already been integrated, then
         *  remove it and start again.
         */
        Itk_IgnoreArchOptionPart(mergeInfo->archInfo, opt);

        /*
         *  Build a command prefix that can be used to apply changes
         *  to this option for this component.
         */
        cmdlinePtr = Itk_CreateConfigCmdline(interp,
            mergeInfo->archComp->accessCmd, token);

        optPart = Itk_CreateOptionPart(interp, (ClientData)cmdlinePtr,
            Itk_PropagateOption, Itk_DeleteConfigCmdline,
            (ClientData)mergeInfo->archComp);

        result = Itk_AddOptionPart(interp, mergeInfo->archInfo,
            opt->switchName, opt->resName, opt->resClass,
            opt->init, opt->value, optPart, &archOpt);

        if (result == TCL_OK) {
            opt->integrated = archOpt;
            opt->optPart    = optPart;
        } else {
            Itk_DelOptionPart(optPart);
            result = TCL_ERROR;
            break;
        }
    }
    return result;
}


/*
 * ------------------------------------------------------------------------
 *  Itk_ArchOptIgnoreCmd()
 *
 *  Invoked by [incr Tcl] to handle the "ignore" command in the itk
 *  option parser.  Removes a list of component configuration options
 *  from a mega-widget.  This negates the action of previous "keep"
 *  and "rename" commands.
 *
 *  Handles the following syntax:
 *
 *      ignore <option> ?<option>...?
 *
 *  Returns TCL_OK/TCL_ERROR to indicate success/failure.
 * ------------------------------------------------------------------------
 */
/* ARGSUSED */
static int
Itk_ArchOptIgnoreCmd(clientData, interp, objc, objv)
    ClientData clientData;   /* option merging info record */
    Tcl_Interp *interp;      /* current interpreter */
    int objc;                /* number of arguments */
    Tcl_Obj *CONST objv[];   /* argument objects */
{
    ArchMergeInfo *mergeInfo = (ArchMergeInfo*)clientData;

    int i;
    char *token;
    Tcl_HashEntry *entry;
    GenericConfigOpt *opt;

    if (objc < 2) {
        Tcl_WrongNumArgs(interp, 1, objv, "option ?option...?");
        return TCL_ERROR;
    }

    /*
     *  Make sure that this command is being accessed in the
     *  proper context.  The merge info record should be set up
     *  properly.
     */
    if (!mergeInfo->archInfo || !mergeInfo->optionTable) {
        token = Tcl_GetStringFromObj(objv[0], (int*)NULL);
        Tcl_AppendResult(interp,
            "improper usage: \"", token,
            "\" should only be accessed via itk_component",
            (char*)NULL);
        return TCL_ERROR;
    }

    /*
     *  Scan through all of the options on the list, and make
     *  sure that they are valid options for this component.
     *  Remove them from the mega-widget.
     */
    for (i=1; i < objc; i++) {
        token = Tcl_GetStringFromObj(objv[i], (int*)NULL);
        entry = Tcl_FindHashEntry(mergeInfo->optionTable, token);
        if (!entry) {
            Tcl_AppendResult(interp, "option not recognized: ", token,
                (char*)NULL);
            return TCL_ERROR;
        }
        opt = (GenericConfigOpt*)Tcl_GetHashValue(entry);

        /*
         *  If this option has already been integrated, then
         *  remove it.  Otherwise, ignore it.
         */
        Itk_IgnoreArchOptionPart(mergeInfo->archInfo, opt);
    }
    return TCL_OK;
}


/*
 * ------------------------------------------------------------------------
 *  Itk_ArchOptRenameCmd()
 *
 *  Invoked by [incr Tcl] to handle the "rename" command in the itk
 *  option parser.  Integrates one configuration option into a
 *  mega-widget, using a different name for the option.  Whenever the
 *  mega-widget option is updated, the renamed option will be updated
 *  as well.  Handles the following syntax:
 *
 *      rename <oldSwitch> <newSwitch> <resName> <resClass>
 *
 *  Returns TCL_OK/TCL_ERROR to indicate success/failure.
 * ------------------------------------------------------------------------
 */
/* ARGSUSED */
static int
Itk_ArchOptRenameCmd(clientData, interp, objc, objv)
    ClientData clientData;   /* option merging info record */
    Tcl_Interp *interp;      /* current interpreter */
    int objc;                /* number of arguments */
    Tcl_Obj *CONST objv[];   /* argument objects */
{
    ArchMergeInfo *mergeInfo = (ArchMergeInfo*)clientData;

    int result;
    char *oldSwitch, *newSwitch, *resName, *resClass;
    Tcl_HashEntry *entry;
    GenericConfigOpt *opt;
    ArchOption *archOpt;
    ArchOptionPart *optPart;
    ConfigCmdline *cmdlinePtr;

    if (objc != 5) {
        Tcl_WrongNumArgs(interp, 1, objv,
            "oldSwitch newSwitch resourceName resourceClass");
        return TCL_ERROR;
    }

    /*
     *  Make sure that this command is being accessed in the
     *  proper context.  The merge info record should be set up
     *  properly.
     */
    if (!mergeInfo->archInfo || !mergeInfo->optionTable) {
        char *token = Tcl_GetStringFromObj(objv[0], (int*)NULL);
        Tcl_AppendResult(interp,
            "improper usage: \"", token,
            "\" should only be accessed via itk_component",
            (char*)NULL);
        return TCL_ERROR;
    }

    oldSwitch = Tcl_GetStringFromObj(objv[1], (int*)NULL);
    newSwitch = Tcl_GetStringFromObj(objv[2], (int*)NULL);
    resName   = Tcl_GetStringFromObj(objv[3], (int*)NULL);
    resClass  = Tcl_GetStringFromObj(objv[4], (int*)NULL);

    /*
     *  Make sure that the resource name and resource class look good.
     */
    if (!islower((int)*resName)) {
        Tcl_AppendResult(interp,
            "bad resource name \"", resName,
            "\": should start with a lower case letter",
            (char*)NULL);
        return TCL_ERROR;
    }
    if (!isupper((int)*resClass)) {
        Tcl_AppendResult(interp,
            "bad resource class \"", resClass,
            "\": should start with an upper case letter",
            (char*)NULL);
        return TCL_ERROR;
    }

    /*
     *  Make sure that the specified switch exists in the widget.
     */
    entry = Tcl_FindHashEntry(mergeInfo->optionTable, oldSwitch);
    if (!entry) {
        Tcl_AppendResult(interp,
            "option not recognized: ", oldSwitch,
            (char*)NULL);
        return TCL_ERROR;
    }
    opt = (GenericConfigOpt*)Tcl_GetHashValue(entry);

    /*
     *  If this option has already been integrated, then
     *  remove it and start again.
     */
    Itk_IgnoreArchOptionPart(mergeInfo->archInfo, opt);

    /*
     *  Build a command prefix that can be used to apply changes
     *  to this option for this component.
     */
    cmdlinePtr = Itk_CreateConfigCmdline(interp,
        mergeInfo->archComp->accessCmd, oldSwitch);

    optPart = Itk_CreateOptionPart(interp, (ClientData)cmdlinePtr,
        Itk_PropagateOption, Itk_DeleteConfigCmdline,
        (ClientData)mergeInfo->archComp);

    /*
     *  Merge this option into the mega-widget with a new name.
     */
    result = Itk_AddOptionPart(interp, mergeInfo->archInfo, newSwitch,
        resName, resClass, opt->init, opt->value, optPart,
        &archOpt);

    if (result == TCL_OK) {
        opt->integrated = archOpt;
        opt->optPart    = optPart;
    } else {
        Itk_DelOptionPart(optPart);
        result = TCL_ERROR;
    }
    return result;
}


/*
 * ------------------------------------------------------------------------
 *  Itk_ArchOptUsualCmd()
 *
 *  Invoked by [incr Tcl] to handle the "usual" command in the itk
 *  option parser.  Looks for a set of "usual" option-handling commands
 *  associated with the given tag or component class and then evaluates
 *  the commands in the option parser namespace.  This keeps the user
 *  from having to type a bunch of "keep" and "rename" commands for
 *  each component widget.
 *
 *  Handles the following syntax:
 *
 *      usual ?<tag>?
 *
 *  If the <tag> is not specified, then the class name for the
 *  component is used as the tag name.
 *
 *  Returns TCL_OK/TCL_ERROR to indicate success/failure.
 * ------------------------------------------------------------------------
 */
/* ARGSUSED */
static int
Itk_ArchOptUsualCmd(clientData, interp, objc, objv)
    ClientData clientData;   /* option merging info record */
    Tcl_Interp *interp;      /* current interpreter */
    int objc;                /* number of arguments */
    Tcl_Obj *CONST objv[];   /* argument objects */
{
    ArchMergeInfo *mergeInfo = (ArchMergeInfo*)clientData;

    CONST char *tag;
    Tcl_HashEntry *entry;
    Tcl_Obj *codePtr;

    if (objc > 2) {
        Tcl_WrongNumArgs(interp, 1, objv, "?tag?");
        return TCL_ERROR;
    }

    /*
     *  Make sure that this command is being accessed in the
     *  proper context.  The merge info record should be set up
     *  properly.
     */
    if (!mergeInfo->archInfo || !mergeInfo->optionTable) {
        char *token = Tcl_GetStringFromObj(objv[0], (int*)NULL);
        Tcl_AppendResult(interp,
            "improper usage: \"", token,
            "\" should only be accessed via itk_component",
            (char*)NULL);
        return TCL_ERROR;
    }

    /*
     *  If a tag name was specified, then use this to look up
     *  the "usual" code.  Otherwise, use the class name for
     *  the component widget.
     */
    if (objc == 2) {
        tag = Tcl_GetStringFromObj(objv[1], (int*)NULL);
    } else {
        tag = Tk_Class(mergeInfo->archComp->tkwin);
    }

    /*
     *  Look for some code associated with the tag and evaluate
     *  it in the current context.
     */
    entry = Tcl_FindHashEntry(&mergeInfo->usualCode, tag);
    if (entry) {
        codePtr = (Tcl_Obj*)Tcl_GetHashValue(entry);
        return Tcl_EvalObj(interp, codePtr);
    }

    Tcl_AppendResult(interp,
        "can't find usual code for tag \"", tag, "\"",
        (char*)NULL);
    return TCL_ERROR;
}


/*
 * ------------------------------------------------------------------------
 *  Itk_UsualCmd()
 *
 *  Invoked by [incr Tcl] to handle the "usual" command in the ::itk
 *  namespace.  Used to query or set the option-handling code associated
 *  with a widget class or arbitrary tag name.  This code is later
 *  used by the "usual" command in the "itk::option-parser" namespace.
 *
 *  Handles the following syntax:
 *
 *      usual ?<tag>? ?<code>?
 *
 *  If the <tag> is not specified, then this returns a list of all
 *  known tags.  If the <code> is not specified, then this returns
 *  the current code associated with <tag>, or an empty string if
 *  <tag> is not recognized.  Otherwise, it sets the code fragment
 *  for <tag> to <code>.
 *
 *  Returns TCL_OK/TCL_ERROR to indicate success/failure.
 * ------------------------------------------------------------------------
 */
/* ARGSUSED */
int
Itk_UsualCmd(clientData, interp, objc, objv)
    ClientData clientData;   /* option merging info record */
    Tcl_Interp *interp;      /* current interpreter */
    int objc;                /* number of arguments */
    Tcl_Obj *CONST objv[];   /* argument objects */
{
    ArchMergeInfo *mergeInfo = (ArchMergeInfo*)clientData;

    int newEntry;
    char *tag, *token;
    Tcl_HashEntry *entry;
    Tcl_HashSearch place;
    Tcl_Obj *codePtr;

    if (objc > 3) {
        Tcl_WrongNumArgs(interp, 1, objv, "?tag? ?commands?");
        return TCL_ERROR;
    }

    /*
     *  If no arguments were specified, then return a list of
     *  all known tags.
     */
    if (objc == 1) {
        entry = Tcl_FirstHashEntry(&mergeInfo->usualCode, &place);
        while (entry) {
            tag = Tcl_GetHashKey(&mergeInfo->usualCode, entry);
            Tcl_AppendElement(interp, tag);
            entry = Tcl_NextHashEntry(&place);
        }
        return TCL_OK;
    }

    /*
     *  If a code fragment was specified, then save it in the
     *  hash table for "usual" code.
     */
    else if (objc == 3) {
        token = Tcl_GetStringFromObj(objv[1], (int*)NULL);
        entry = Tcl_CreateHashEntry(&mergeInfo->usualCode, token, &newEntry);
        if (!newEntry) {
            codePtr = (Tcl_Obj*)Tcl_GetHashValue(entry);
            Tcl_DecrRefCount(codePtr);
        }

        codePtr = objv[2];
        Tcl_IncrRefCount(codePtr);
        Tcl_SetHashValue(entry, (ClientData)codePtr);

        return TCL_OK;
    }

    /*
     *  Otherwise, look for a code fragment with the specified tag.
     */
    token = Tcl_GetStringFromObj(objv[1], (int*)NULL);
    entry = Tcl_FindHashEntry(&mergeInfo->usualCode, token);
    if (entry) {
        codePtr = (Tcl_Obj*)Tcl_GetHashValue(entry);
        Tcl_SetObjResult(interp, codePtr);
    }
    return TCL_OK;
}


/*
 * ------------------------------------------------------------------------
 *  Itk_ArchInitCmd()
 *
 *  Invoked by [incr Tcl] to handle the itk::Archetype::itk_initialize
 *  method.  This method should be called out in the constructor for
 *  each mega-widget class, to build the composite option list at
 *  each class level.  Handles the following syntax:
 *
 *      itk_initialize ?-option val -option val...?
 *
 *  Integrates any class-based options into the composite option list,
 *  handles option settings from the command line, and then configures
 *  all options to have the proper initial value.
 *
 *  Returns TCL_OK/TCL_ERROR to indicate success/failure.
 * ------------------------------------------------------------------------
 */
/* ARGSUSED */
static int
Itk_ArchInitCmd(dummy, interp, objc, objv)
    ClientData dummy;        /* unused */
    Tcl_Interp *interp;      /* current interpreter */
    int objc;                /* number of arguments */
    Tcl_Obj *CONST objv[];   /* argument objects */
{
    ItclClass *contextClass, *cdefn;
    ItclObject *contextObj;
    ArchInfo *info;

    int i, result;
    CONST char *val;
    char *token;
    Itcl_CallFrame *framePtr;
    ItkClassOption *opt;
    ItkClassOptTable *optTable;
    Itcl_ListElem *part;
    ArchOption *archOpt;
    ArchOptionPart *optPart;
    ItclHierIter hier;
    ItclVarDefn *vdefn;
    Tcl_HashSearch place;
    Tcl_HashEntry *entry;

    if (Itcl_GetContext(interp, &contextClass, &contextObj) != TCL_OK ||
        !contextObj) {

        token = Tcl_GetStringFromObj(objv[0], (int*)NULL);
        Tcl_ResetResult(interp);
        Tcl_AppendResult(interp,
            "improper usage: should be \"object ",
            token, " ?-option value -option value...?\"",
            (char*)NULL);
        return TCL_ERROR;
    }

    if (Itk_GetArchInfo(interp, contextObj, &info) != TCL_OK) {
        return TCL_ERROR;
    }

    /*
     *  See what class is being initialized by getting the namespace
     *  for the calling context.
     */
    framePtr = _Tcl_GetCallFrame(interp, 1);
    if (framePtr && Itcl_IsClassNamespace(framePtr->nsPtr)) {
        contextClass = (ItclClass*)framePtr->nsPtr->clientData;
    }

    /*
     *  Integrate all public variables for the current class
     *  context into the composite option list.
     */
    Itcl_InitHierIter(&hier, contextClass);
    while ((cdefn=Itcl_AdvanceHierIter(&hier)) != NULL) {
        entry = Tcl_FirstHashEntry(&cdefn->variables, &place);
        while (entry) {
            vdefn = (ItclVarDefn*)Tcl_GetHashValue(entry);

            if (vdefn->member->protection == ITCL_PUBLIC) {
                optPart = Itk_FindArchOptionPart(info,
                    vdefn->member->name, (ClientData)vdefn);

                if (!optPart) {
                    optPart = Itk_CreateOptionPart(interp, (ClientData)vdefn,
                        Itk_PropagatePublicVar, (Tcl_CmdDeleteProc*)NULL,
                        (ClientData)vdefn);

                    val = Itcl_GetInstanceVar(interp, vdefn->member->fullname,
                        contextObj, contextObj->classDefn);

                    result = Itk_AddOptionPart(interp, info,
                        vdefn->member->name, (char*)NULL, (char*)NULL,
                        val, (char*)NULL, optPart, &archOpt);

                    if (result != TCL_OK) {
                        Itk_DelOptionPart(optPart);
                        return TCL_ERROR;
                    }
                }
            }
            entry = Tcl_NextHashEntry(&place);
        }
    }
    Itcl_DeleteHierIter(&hier);

    /*
     *  Integrate all class-based options for the current class
     *  context into the composite option list.
     */
    optTable = Itk_FindClassOptTable(contextClass);
    if (optTable) {
        for (i=0; i < optTable->order.len; i++) {
            opt = (ItkClassOption*)Tcl_GetHashValue(optTable->order.list[i]);

            optPart = Itk_FindArchOptionPart(info, opt->member->name,
                (ClientData)contextClass);

            if (!optPart) {
                optPart = Itk_CreateOptionPart(interp, (ClientData)opt,
                    Itk_ConfigClassOption, (Tcl_CmdDeleteProc*)NULL,
                    (ClientData)contextClass);

                result = Itk_AddOptionPart(interp, info,
                    opt->member->name, opt->resName, opt->resClass,
                    opt->init, (char*)NULL, optPart, &archOpt);

                if (result != TCL_OK) {
                    Itk_DelOptionPart(optPart);
                    return TCL_ERROR;
                }
            }
        }
    }

    /*
     *  If any option values were specified on the command line,
     *  override the current option settings.
     */
    if (objc > 1) {
        for (objc--,objv++; objc > 0; objc-=2, objv+=2) {
	    char *value;
            token = Tcl_GetStringFromObj(objv[0], (int*)NULL);
            if (objc < 2) {
	        /* Bug 227814
		 * Ensure that the interp result is unshared.
		 */

	        Tcl_ResetResult(interp);
                Tcl_AppendResult(interp,
                    "value for \"", token, "\" missing",
                    (char*)NULL);
                return TCL_ERROR;
            }

            value = Tcl_GetStringFromObj(objv[1], (int*)NULL);
            if (Itk_ArchConfigOption(interp, info, token, value) != TCL_OK) {
                return TCL_ERROR;
            }
        }
    }

    /*
     *  If this is most-specific class, then finish constructing
     *  the mega-widget:
     *
     *  Scan through all options in the composite list and
     *  look for any that have been set but not initialized.
     *  Invoke the parts of uninitialized options to propagate
     *  changes and update the widget.
     */
    if (contextObj->classDefn == contextClass) {
        for (i=0; i < info->order.len; i++) {
            archOpt = (ArchOption*)Tcl_GetHashValue(info->order.list[i]);

            if ((archOpt->flags & ITK_ARCHOPT_INIT) == 0) {
                val = Tcl_GetVar2(interp, "itk_option", archOpt->switchName, 0);

                if (!val) {
                    Itk_ArchOptAccessError(interp, info, archOpt);
                    return TCL_ERROR;
                }

                part = Itcl_FirstListElem(&archOpt->parts);
                while (part) {
                    optPart = (ArchOptionPart*)Itcl_GetListValue(part);
                    result  = (*optPart->configProc)(interp, contextObj,
                        optPart->clientData, val);

                    if (result != TCL_OK) {
                        Itk_ArchOptConfigError(interp, info, archOpt);
                        return result;
                    }
                    part = Itcl_NextListElem(part);
                }
                archOpt->flags |= ITK_ARCHOPT_INIT;
            }
        }
    }

    Tcl_ResetResult(interp);
    return TCL_OK;
}


/*
 * ------------------------------------------------------------------------
 *  Itk_ArchOptionCmd()
 *
 *  Invoked by [incr Tcl] to handle the itk::Archetype::itk_option
 *  method.  Handles the following options:
 *
 *      itk_option define <switch> <resName> <resClass> <init> ?<config>?
 *      itk_option add <name> ?<name>...?
 *      itk_option remove <name> ?<name>...?
 *
 *  These commands customize the options list of a specific widget.
 *  They are similar to the "itk_option" ensemble in the class definition
 *  parser, but manipulate a single instance instead of an entire class.
 *
 *  Returns TCL_OK/TCL_ERROR to indicate success/failure.
 * ------------------------------------------------------------------------
 */
/* ARGSUSED */
static int
Itk_ArchOptionCmd(dummy, interp, objc, objv)
    ClientData dummy;        /* unused */
    Tcl_Interp *interp;      /* current interpreter */
    int objc;                /* number of arguments */
    Tcl_Obj *CONST objv[];   /* argument objects */
{
    char *cmd, *token, c;
    int length;

    /*
     *  Check arguments and handle the various options...
     */
    if (objc < 2) {
        cmd = Tcl_GetStringFromObj(objv[0], (int*)NULL);
        Tcl_AppendResult(interp,
            "wrong # args: should be one of...\n",
            "  ", cmd, " add name ?name name...?\n",
            "  ", cmd, " define -switch resourceName resourceClass init ?config?\n",
            "  ", cmd, " remove name ?name name...?",
            (char*)NULL);
        return TCL_ERROR;
    }

    token = Tcl_GetStringFromObj(objv[1], (int*)NULL);
    c = *token;
    length = strlen(token);

    /*
     *  Handle:  itk_option add...
     */
    if (c == 'a' && strncmp(token, "add", length) == 0) {
        if (objc < 3) {
            Tcl_WrongNumArgs(interp, 1, objv, "add name ?name name...?");
            return TCL_ERROR;
        }
        return Itk_ArchOptionAddCmd(dummy, interp, objc-1, objv+1);
    }

    /*
     *  Handle:  itk_option remove...
     */
    else if (c == 'r' && strncmp(token, "remove", length) == 0) {
        if (objc < 3) {
            Tcl_WrongNumArgs(interp, 1, objv, "remove name ?name name...?");
            return TCL_ERROR;
        }
        return Itk_ArchOptionRemoveCmd(dummy, interp, objc-1, objv+1);
    }

    /*
     *  Handle:  itk_option define...
     */
    else if (c == 'd' && strncmp(token, "define", length) == 0) {
        Tcl_AppendResult(interp,
            "can only ", token, " options at the class level\n",
            "(move this command into the class definition)",
            (char*)NULL);
        return TCL_ERROR;
    }

    /*
     *  Flag any errors.
     */
    cmd = Tcl_GetStringFromObj(objv[0], (int*)NULL);
    Tcl_AppendResult(interp,
        "bad option \"", token,
        "\": should be one of...\n",
        "  ", cmd, " add name ?name name...?\n",
        "  ", cmd, " define -switch resourceName resourceClass init ?config?\n",
        "  ", cmd, " remove name ?name name...?",
        (char*)NULL);
    return TCL_ERROR;
}


/*
 * ------------------------------------------------------------------------
 *  Itk_ArchOptionAddCmd()
 *
 *  Invoked by [incr Tcl] to handle the itk::Archetype::itk_option add
 *  method.  Finds an option within a class definition or belonging to
 *  a component widget and adds it into the option list for this widget.
 *  If the option is already on the list, this method does nothing.
 *  Handles the following syntax:
 *
 *      itk_option add <name> ?<name> <name>...?
 *
 *      where <name> is one of:
 *        class::option
 *        component.option
 *
 *  Returns TCL_OK/TCL_ERROR to indicate success/failure.
 * ------------------------------------------------------------------------
 */
/* ARGSUSED */
static int
Itk_ArchOptionAddCmd(dummy, interp, objc, objv)
    ClientData dummy;        /* unused */
    Tcl_Interp *interp;      /* current interpreter */
    int objc;                /* number of arguments */
    Tcl_Obj *CONST objv[];   /* argument objects */
{
    ItclClass *contextClass, *cdefn;
    ItclObject *contextObj;
    ArchInfo *info;

    int i, result;
    char *token, *head, *tail, *sep, tmp;
    ItkClassOption *opt;
    GenericConfigOpt *generic;
    ArchOption *archOpt;
    ArchOptionPart *optPart;
    ArchComponent *archComp;
    ConfigCmdline *cmdlinePtr;
    Tcl_HashEntry *entry;
    Tcl_DString buffer;

    /*
     *  Get the Archetype info associated with this widget.
     */
    if (Itcl_GetContext(interp, &contextClass, &contextObj) != TCL_OK ||
        !contextObj) {

        Tcl_ResetResult(interp);
        Tcl_AppendResult(interp,
            "cannot access options without an object context",
            (char*)NULL);
        return TCL_ERROR;
    }

    if (Itk_GetArchInfo(interp, contextObj, &info) != TCL_OK) {
        return TCL_ERROR;
    }

    /*
     *  Scan through the list of options and locate each one.
     *  If it is not already on the option part list, add it.
     */
    for (i=1; i < objc; i++) {
        token = Tcl_GetStringFromObj(objv[i], (int*)NULL);
        Itcl_ParseNamespPath(token, &buffer, &head, &tail);

        /*
         *  HANDLE:  class::option
         */
        if (head) {
            cdefn = Itcl_FindClass(interp, head, /* autoload */ 1);
            if (!cdefn) {
                Tcl_DStringFree(&buffer);
                return TCL_ERROR;
            }

            opt = Itk_FindClassOption(cdefn, tail);
            if (!opt) {
                Tcl_AppendResult(interp,
                    "option \"", tail, "\" not defined in class \"",
                    cdefn->fullname, "\"",
                    (char*)NULL);
                Tcl_DStringFree(&buffer);
                return TCL_ERROR;
            }

            optPart = Itk_FindArchOptionPart(info, opt->member->name,
                (ClientData)cdefn);

            if (!optPart) {
                optPart = Itk_CreateOptionPart(interp, (ClientData)opt,
                    Itk_ConfigClassOption, (Tcl_CmdDeleteProc*)NULL,
                    (ClientData)cdefn);

                result = Itk_AddOptionPart(interp, info, opt->member->name,
                    opt->resName, opt->resClass, opt->init, (char*)NULL,
                    optPart, &archOpt);

                if (result != TCL_OK) {
                    Itk_DelOptionPart(optPart);
                    Tcl_DStringFree(&buffer);
                    return TCL_ERROR;
                }
            }
            Tcl_DStringFree(&buffer);
            continue;
        }

        Tcl_DStringFree(&buffer);

        /*
         *  HANDLE:  component.option
         */
        sep = strstr(token, ".");
        if (sep) {
            tmp = *sep;
            *sep = '\0';
            head = token;
            tail = sep+1;

            entry = Tcl_FindHashEntry(&info->components, head);
            if (!entry) {
                Tcl_AppendResult(interp,
                    "name \"", head, "\" is not a component",
                    (char*)NULL);
                *sep = tmp;
                return TCL_ERROR;
            }
            *sep = tmp;
            archComp = (ArchComponent*)Tcl_GetHashValue(entry);

            generic = Itk_CreateGenericOpt(interp, tail, archComp->accessCmd);
            if (!generic) {
                char msg[256];
                sprintf(msg, "\n    (while adding option \"%.100s\")", token);
                Tcl_AddErrorInfo(interp, msg);
                return TCL_ERROR;
            }

            optPart = Itk_FindArchOptionPart(info, generic->switchName,
                (ClientData)archComp);

            if (!optPart) {
                cmdlinePtr = Itk_CreateConfigCmdline(interp,
                    archComp->accessCmd, generic->switchName);

                optPart = Itk_CreateOptionPart(interp, (ClientData)cmdlinePtr,
                    Itk_PropagateOption, Itk_DeleteConfigCmdline,
                    (ClientData)archComp);

                result = Itk_AddOptionPart(interp, info,
                    generic->switchName, generic->resName, generic->resClass,
                    generic->init, generic->value, optPart, &archOpt);

                if (result != TCL_OK) {
                    Itk_DelOptionPart(optPart);
                    Itk_DelGenericOpt(generic);
                    return TCL_ERROR;
                }
            }
            Itk_DelGenericOpt(generic);
            continue;
        }

        /*
         *  Anything else is an error.
         */
        Tcl_AppendResult(interp,
            "bad option \"", token, "\": should be one of...\n",
            "  class::option\n",
            "  component.option",
            (char*)NULL);
        return TCL_ERROR;
    }

    return TCL_OK;
}


/*
 * ------------------------------------------------------------------------
 *  Itk_ArchOptionRemoveCmd()
 *
 *  Invoked by [incr Tcl] to handle the itk::Archetype::itk_option remove
 *  method.  Finds an option within a class definition or belonging to
 *  a component widget and removes it from the option list for this widget.
 *  If the option has already been removed from the list, this method does
 *  nothing.  Handles the following syntax:
 *
 *      itk_option remove <name> ?<name> <name>...?
 *
 *      where <name> is one of:
 *        class::option
 *        component.option
 *
 *  Returns TCL_OK/TCL_ERROR to indicate success/failure.
 * ------------------------------------------------------------------------
 */
/* ARGSUSED */
static int
Itk_ArchOptionRemoveCmd(dummy, interp, objc, objv)
    ClientData dummy;        /* unused */
    Tcl_Interp *interp;      /* current interpreter */
    int objc;                /* number of arguments */
    Tcl_Obj *CONST objv[];   /* argument objects */
{
    ItclClass *contextClass, *cdefn;
    ItclObject *contextObj;
    ArchInfo *info;

    int i;
    char *name, *head, *tail, *sep, tmp;
    ItkClassOption *opt;
    GenericConfigOpt *generic;
    ArchComponent *archComp;
    Tcl_HashEntry *entry;
    Tcl_DString buffer;

    /*
     *  Get the Archetype info associated with this widget.
     */
    if (Itcl_GetContext(interp, &contextClass, &contextObj) != TCL_OK ||
        !contextObj) {

        Tcl_ResetResult(interp);
        Tcl_AppendResult(interp,
            "cannot access options without an object context",
            (char*)NULL);
        return TCL_ERROR;
    }

    if (Itk_GetArchInfo(interp, contextObj, &info) != TCL_OK) {
        return TCL_ERROR;
    }

    /*
     *  Scan through the list of options and locate each one.
     *  If it is on the option list, remove it.
     */
    for (i=1; i < objc; i++) {
        name = Tcl_GetStringFromObj(objv[i], (int*)NULL);
        Itcl_ParseNamespPath(name, &buffer, &head, &tail);

        /*
         *  HANDLE:  class::option
         */
        if (head) {
            cdefn = Itcl_FindClass(interp, head, /* autoload */ 1);
            if (!cdefn) {
                Tcl_DStringFree(&buffer);
                return TCL_ERROR;
            }

            opt = Itk_FindClassOption(cdefn, tail);
            if (!opt) {
                Tcl_AppendResult(interp,
                    "option \"", tail, "\" not defined in class \"",
                    cdefn->fullname, "\"",
                    (char*)NULL);
                Tcl_DStringFree(&buffer);
                return TCL_ERROR;
            }

            Itk_RemoveArchOptionPart(info, opt->member->name,
                (ClientData)cdefn);

            Tcl_DStringFree(&buffer);
            continue;
        }
        Tcl_DStringFree(&buffer);

        /*
         *  HANDLE:  component.option
         */
        sep = strstr(name, ".");
        if (sep) {
            tmp = *sep;
            *sep = '\0';
            head = name;
            tail = sep+1;

            entry = Tcl_FindHashEntry(&info->components, head);
            if (!entry) {
                Tcl_AppendResult(interp,
                    "name \"", head, "\" is not a component",
                    (char*)NULL);
                *sep = tmp;
                return TCL_ERROR;
            }
            *sep = tmp;
            archComp = (ArchComponent*)Tcl_GetHashValue(entry);

            generic = Itk_CreateGenericOpt(interp, tail, archComp->accessCmd);
            if (!generic) {
                char msg[256];
                sprintf(msg, "\n    (while removing option \"%.100s\")",
                    name);
                Tcl_AddErrorInfo(interp, msg);
                return TCL_ERROR;
            }

            Itk_RemoveArchOptionPart(info, generic->switchName,
                (ClientData)archComp);

            Itk_DelGenericOpt(generic);
            continue;
        }

        /*
         *  Anything else is an error.
         */
        Tcl_AppendResult(interp,
            "bad option \"", name, "\": should be one of...\n",
            "  class::option\n",
            "  component.option",
            (char*)NULL);
        return TCL_ERROR;
    }

    return TCL_OK;
}


/*
 * ------------------------------------------------------------------------
 *  Itk_ArchCompAccessCmd()
 *
 *  Invoked by [incr Tcl] to handle the itk::Archetype::component method.
 *  Finds the requested component and invokes the <command> as a method
 *  on that component.
 *
 *  Handles the following syntax:
 *
 *      component
 *      component <name>
 *      component <name> <command> ?<arg> <arg>...?
 *
 *  With no arguments, this command returns the names of components
 *  that can be accessed from the current context.  Note that components
 *  respect public/protected/private declarations, so private and
 *  protected components may not be accessible from all namespaces.
 *
 *  If a component name is specified, then this command returns the
 *  window name for that component.
 *
 *  If a series of arguments follow the component name, they are treated
 *  as a method invocation, and dispatched to the component.
 *
 *  Returns TCL_OK/TCL_ERROR to indicate success/failure.
 * ------------------------------------------------------------------------
 */
/* ARGSUSED */
static int
Itk_ArchCompAccessCmd(dummy, interp, objc, objv)
    ClientData dummy;        /* unused */
    Tcl_Interp *interp;      /* current interpreter */
    int objc;                /* number of arguments */
    Tcl_Obj *CONST objv[];   /* argument objects */
{
    int i, result;
    char *token;
    CONST char *name, *val;
    Tcl_Namespace *callingNs;
    ItclClass *contextClass;
    ItclObject *contextObj;
    Itcl_CallFrame *framePtr;
    Tcl_HashEntry *entry;
    Tcl_HashSearch place;
    ArchInfo *info;
    ArchComponent *archComp;
    int cmdlinec;
    Tcl_Obj *objPtr, *cmdlinePtr, **cmdlinev;

    if (Itcl_GetContext(interp, &contextClass, &contextObj) != TCL_OK ||
        !contextObj) {

        token = Tcl_GetStringFromObj(objv[0], (int*)NULL);
        Tcl_ResetResult(interp);
        Tcl_AppendResult(interp,
            "improper usage: should be \"object ",
            token, " ?name option arg arg...?\"",
            (char*)NULL);
        return TCL_ERROR;
    }

    if (Itk_GetArchInfo(interp, contextObj, &info) != TCL_OK) {
        return TCL_ERROR;
    }

    framePtr = _Tcl_GetCallFrame(interp, 1);
    if (framePtr) {
        callingNs = framePtr->nsPtr;
    } else {
        callingNs = Tcl_GetGlobalNamespace(interp);
    }

    /*
     *  With no arguments, return a list of components that can be
     *  accessed from the calling scope.
     */
    if (objc == 1) {
        entry = Tcl_FirstHashEntry(&info->components, &place);
        while (entry) {
            archComp = (ArchComponent*)Tcl_GetHashValue(entry);
            if (Itcl_CanAccess(archComp->member, callingNs)) {
                name = Tcl_GetHashKey(&info->components, entry);
                Tcl_AppendElement(interp, (CONST84 char *)name);
            }
            entry = Tcl_NextHashEntry(&place);
        }
        return TCL_OK;
    }

    /*
     *  Make sure the requested component exists.
     */
    token = Tcl_GetStringFromObj(objv[1], (int*)NULL);
    entry = Tcl_FindHashEntry(&info->components, token);
    if (entry) {
        archComp = (ArchComponent*)Tcl_GetHashValue(entry);
    } else {
        archComp = NULL;
    }

    if (archComp == NULL) {
        Tcl_AppendResult(interp,
            "name \"", token, "\" is not a component",
            (char*)NULL);
        return TCL_ERROR;
    }

    if (!Itcl_CanAccess(archComp->member, callingNs)) {
        Tcl_AppendResult(interp,
            "can't access component \"", token, "\" from context \"",
            callingNs->fullName, "\"",
            (char*)NULL);
        return TCL_ERROR;
    }

    /*
     *  If only the component name is specified, then return the
     *  window name for this component.
     */
    if (objc == 2) {
        val = Tcl_GetVar2(interp, "itk_component", token, 0);
        if (!val) {
            Tcl_ResetResult(interp);
            Tcl_AppendResult(interp,
                "internal error: cannot access itk_component(", token, ")",
                (char*)NULL);

            if (contextObj->accessCmd) {
                Tcl_Obj *resultPtr = Tcl_GetObjResult(interp);
                Tcl_AppendToObj(resultPtr, " in widget \"", -1);
                Tcl_GetCommandFullName(contextObj->classDefn->interp,
                    contextObj->accessCmd, resultPtr);
                Tcl_AppendToObj(resultPtr, "\"", -1);
            }
            return TCL_ERROR;
        }
	/*
	 * Casting away CONST is safe because TCL_VOLATILE guarantees
	 * CONST treatment.
	 */
        Tcl_SetResult(interp, (char *) val, TCL_VOLATILE);
        return TCL_OK;
    }

    /*
     *  Otherwise, treat the rest of the command line as a method
     *  invocation on the requested component.  Invoke the remaining
     *  command-line arguments as a method for that component.
     */
    cmdlinePtr = Tcl_NewListObj(0, (Tcl_Obj**)NULL);
    Tcl_IncrRefCount(cmdlinePtr);

    objPtr = Tcl_NewStringObj((char*)NULL, 0);
    Tcl_GetCommandFullName(interp, archComp->accessCmd, objPtr);
    Tcl_ListObjAppendElement((Tcl_Interp*)NULL, cmdlinePtr, objPtr);

    for (i=2; i < objc; i++) {
        Tcl_ListObjAppendElement((Tcl_Interp*)NULL, cmdlinePtr, objv[i]);
    }

    (void) Tcl_ListObjGetElements((Tcl_Interp*)NULL, cmdlinePtr,
        &cmdlinec, &cmdlinev);

    result = Itcl_EvalArgs(interp, cmdlinec, cmdlinev);

    Tcl_DecrRefCount(cmdlinePtr);

    return result;
}


/*
 * ------------------------------------------------------------------------
 *  Itk_ArchConfigureCmd()
 *
 *  Invoked by [incr Tcl] to handle the itk::Archetype::configure method.
 *  Mimics the usual Tk "configure" method for Archetype mega-widgets.
 *
 *      configure
 *      configure -name
 *      configure -name value ?-name value ...?
 *
 *  Returns TCL_OK/TCL_ERROR to indicate success/failure.
 * ------------------------------------------------------------------------
 */
/* ARGSUSED */
static int
Itk_ArchConfigureCmd(dummy, interp, objc, objv)
    ClientData dummy;        /* unused */
    Tcl_Interp *interp;      /* current interpreter */
    int objc;                /* number of arguments */
    Tcl_Obj *CONST objv[];   /* argument objects */
{
    int i;
    CONST char *val;
    char *token;
    ItclClass *contextClass;
    ItclObject *contextObj;
    ArchInfo *info;
    Tcl_HashEntry *entry;
    ArchOption *archOpt;
    Tcl_DString buffer;

    if (Itcl_GetContext(interp, &contextClass, &contextObj) != TCL_OK ||
        !contextObj) {

        token = Tcl_GetStringFromObj(objv[0], (int*)NULL);
        Tcl_ResetResult(interp);
        Tcl_AppendResult(interp,
            "improper usage: should be \"object ",
            token, " ?-option? ?value -option value...?\"",
            (char*)NULL);
        return TCL_ERROR;
    }

    if (Itk_GetArchInfo(interp, contextObj, &info) != TCL_OK) {
        return TCL_ERROR;
    }

    /*
     *  If there are no extra arguments, then return a list of all
     *  known configuration options.  Each option has the form:
     *    {name resName resClass init value}
     */
    if (objc == 1) {
        Tcl_DStringInit(&buffer);

        for (i=0; i < info->order.len; i++) {
            archOpt = (ArchOption*)Tcl_GetHashValue(info->order.list[i]);
            val = Tcl_GetVar2(interp, "itk_option", archOpt->switchName, 0);
            if (!val) {
                Itk_ArchOptAccessError(interp, info, archOpt);
                Tcl_DStringFree(&buffer);
                return TCL_ERROR;
            }

            Tcl_DStringStartSublist(&buffer);
            Tcl_DStringAppendElement(&buffer, archOpt->switchName);
            Tcl_DStringAppendElement(&buffer,
                (archOpt->resName) ? archOpt->resName : "");
            Tcl_DStringAppendElement(&buffer,
                (archOpt->resClass) ? archOpt->resClass : "");
            Tcl_DStringAppendElement(&buffer,
                (archOpt->init) ? archOpt->init : "");
            Tcl_DStringAppendElement(&buffer, val);
            Tcl_DStringEndSublist(&buffer);
        }
        Tcl_DStringResult(interp, &buffer);
        Tcl_DStringFree(&buffer);
        return TCL_OK;
    }

    /*
     *  If there is just one argument, then query the information
     *  for that one argument and return:
     *    {name resName resClass init value}
     */
    else if (objc == 2) {
        token = Tcl_GetStringFromObj(objv[1], (int*)NULL);
        entry = Tcl_FindHashEntry(&info->options, token);
        if (!entry) {
            Tcl_AppendResult(interp,
                "unknown option \"", token, "\"",
                (char*)NULL);
            return TCL_ERROR;
        }

        archOpt = (ArchOption*)Tcl_GetHashValue(entry);
        val = Tcl_GetVar2(interp, "itk_option", archOpt->switchName, 0);
        if (!val) {
            Itk_ArchOptAccessError(interp, info, archOpt);
            return TCL_ERROR;
        }

        Tcl_AppendElement(interp, archOpt->switchName);
        Tcl_AppendElement(interp,
            (archOpt->resName) ? archOpt->resName : "");
        Tcl_AppendElement(interp,
            (archOpt->resClass) ? archOpt->resClass : "");
        Tcl_AppendElement(interp,
            (archOpt->init) ? archOpt->init : "");
        Tcl_AppendElement(interp, (CONST84 char *)val);

        return TCL_OK;
    }

    /*
     *  Otherwise, it must be a series of "-option value" assignments.
     *  Look up each option and assign the new value.
     */
    for (objc--,objv++; objc > 0; objc-=2, objv+=2) {
	char *value;
        token = Tcl_GetStringFromObj(objv[0], (int*)NULL);
        if (objc < 2) {
            Tcl_AppendResult(interp,
                "value for \"", token, "\" missing",
                (char*)NULL);
            return TCL_ERROR;
        }
        value = Tcl_GetStringFromObj(objv[1], (int*)NULL);

        if (Itk_ArchConfigOption(interp, info, token, value) != TCL_OK) {
            return TCL_ERROR;
        }
    }

    Tcl_ResetResult(interp);
    return TCL_OK;
}


/*
 * ------------------------------------------------------------------------
 *  Itk_ArchCgetCmd()
 *
 *  Invoked by [incr Tcl] to handle the itk::Archetype::cget method.
 *  Mimics the usual Tk "cget" method for Archetype mega-widgets.
 *
 *      cget -name
 *
 *  Returns TCL_OK/TCL_ERROR to indicate success/failure.
 * ------------------------------------------------------------------------
 */
/* ARGSUSED */
static int
Itk_ArchCgetCmd(dummy, interp, objc, objv)
    ClientData dummy;        /* unused */
    Tcl_Interp *interp;      /* current interpreter */
    int objc;                /* number of arguments */
    Tcl_Obj *CONST objv[];   /* argument objects */
{
    CONST char *token, *val;
    ItclClass *contextClass;
    ItclObject *contextObj;
    ArchInfo *info;
    Tcl_HashEntry *entry;
    ArchOption *archOpt;

    if (Itcl_GetContext(interp, &contextClass, &contextObj) != TCL_OK ||
        !contextObj) {

        token = Tcl_GetStringFromObj(objv[0], (int*)NULL);
        Tcl_ResetResult(interp);
        Tcl_AppendResult(interp,
            "improper usage: should be \"object ", token, " -option\"",
            (char*)NULL);
        return TCL_ERROR;
    }

    if (Itk_GetArchInfo(interp, contextObj, &info) != TCL_OK) {
        return TCL_ERROR;
    }

    if (objc != 2) {
        Tcl_WrongNumArgs(interp, 1, objv, "option");
        return TCL_ERROR;
    }

    /*
     *  Look up the specified option and get its current value.
     */
    token = Tcl_GetStringFromObj(objv[1], (int*)NULL);
    entry = Tcl_FindHashEntry(&info->options, token);
    if (!entry) {
        Tcl_AppendResult(interp,
            "unknown option \"", token, "\"",
            (char*)NULL);
        return TCL_ERROR;
    }

    archOpt = (ArchOption*)Tcl_GetHashValue(entry);
    val = Tcl_GetVar2(interp, "itk_option", archOpt->switchName, 0);
    if (!val) {
        Itk_ArchOptAccessError(interp, info, archOpt);
        return TCL_ERROR;
    }

    /*
     * Casting away CONST is safe because TCL_VOLATILE guarantees
     * CONST treatment.
     */
    Tcl_SetResult(interp, (char *) val, TCL_VOLATILE);
    return TCL_OK;
}


/*
 * ------------------------------------------------------------------------
 *  Itk_PropagateOption()
 *
 *  Invoked whenever a widget-based configuration option has been
 *  configured with a new value.  Propagates the new value down to
 *  the widget by invoking the "configure" method on the widget.
 *  This causes the widget to bring itself up to date automatically.
 *
 *  Returns TCL_OK on success, or TCL_ERROR (along with an error
 *  message in the interpreter) if anything goes wrong.
 * ------------------------------------------------------------------------
 */
/* ARGSUSED */
static int
Itk_PropagateOption(interp, contextObj, cdata, newval)
    Tcl_Interp *interp;        /* interpreter managing the class */
    ItclObject *contextObj;    /* itcl object being configured */
    ClientData cdata;          /* command prefix to use for configuration */
    CONST char *newval;        /* new value for this option */
{
    ConfigCmdline *cmdlinePtr = (ConfigCmdline*)cdata;
    int result;
    Tcl_Obj *objPtr;

    objPtr = Tcl_NewStringObj((CONST84 char *)newval, -1);
    Tcl_IncrRefCount(objPtr);

    cmdlinePtr->objv[3] = objPtr;
    result = Itcl_EvalArgs(interp, 4, cmdlinePtr->objv);

    Tcl_DecrRefCount(objPtr);
    return result;
}


/*
 * ------------------------------------------------------------------------
 *  Itk_PropagatePublicVar()
 *
 *  Invoked whenever a mega-widget configuration option containing
 *  a public variable part has been configured with a new value.
 *  Updates the public variable with the new value and invokes any
 *  "config" code associated with it.
 *
 *  Returns TCL_OK on success, or TCL_ERROR (along with an error
 *  message in the interpreter) if anything goes wrong.
 * ------------------------------------------------------------------------
 */
/* ARGSUSED */
static int
Itk_PropagatePublicVar(interp, contextObj, cdata, newval)
    Tcl_Interp *interp;        /* interpreter managing the class */
    ItclObject *contextObj;    /* itcl object being configured */
    ClientData cdata;          /* command prefix to use for configuration */
    CONST char *newval;        /* new value for this option */
{
    ItclVarDefn *vdefn = (ItclVarDefn*)cdata;

    int result;
    CONST char *val;
    ItclContext context;
    ItclMemberCode *mcode;
    Itcl_CallFrame *uplevelFramePtr, *oldFramePtr;

    /*
     *  Update the public variable with the new option value.
     *  There should already be a call frame installed for handling
     *  instance variables, but make sure that the namespace context
     *  is the most-specific class, so that the public variable can
     *  be found.
     */
    result = Itcl_PushContext(interp, (ItclMember*)NULL,
        contextObj->classDefn, contextObj, &context);

    if (result == TCL_OK) {
	/*
	 * Casting away CONST of newval only to satisfy Tcl 8.3 and
	 * earlier headers.
	 */
        val = Tcl_SetVar2(interp, vdefn->member->fullname, (char *) NULL,
            (char *) newval, TCL_LEAVE_ERR_MSG);

        if (!val) {
            result = TCL_ERROR;
        }
        Itcl_PopContext(interp, &context);
    }

    if (result != TCL_OK) {
        char msg[256];
        sprintf(msg, "\n    (error in configuration of public variable \"%.100s\")", vdefn->member->fullname);
        Tcl_AddErrorInfo(interp, msg);
        return TCL_ERROR;
    }

    /*
     *  If this variable has some "config" code, invoke it now.
     *
     *  NOTE:  Invoke the "config" code in the class scope
     *    containing the data member.
     */
    mcode = vdefn->member->code;
    if (mcode && mcode->procPtr->bodyPtr) {

        uplevelFramePtr = _Tcl_GetCallFrame(interp, 1);
        oldFramePtr = _Tcl_ActivateCallFrame(interp, uplevelFramePtr);

        result = Itcl_EvalMemberCode(interp, (ItclMemberFunc*)NULL,
            vdefn->member, contextObj, 0, (Tcl_Obj**)NULL);

        (void) _Tcl_ActivateCallFrame(interp, oldFramePtr);

        if (result == TCL_OK) {
            Tcl_ResetResult(interp);
        } else {
            char msg[256];
            sprintf(msg, "\n    (error in configuration of public variable \"%.100s\")", vdefn->member->fullname);
            Tcl_AddErrorInfo(interp, msg);
        }
    }

    return result;
}


/*
 * ------------------------------------------------------------------------
 *  Itk_ArchSetOption()
 *
 *  Sets a configuration option within an Archetype mega-widget.
 *  Changes the "itk_option" array to reflect the new value, but
 *  unlike Itk_ArchConfigOption(), this procedure does not update
 *  the widget by propagating changes or invoking any "config" code.
 *  It merely sets the widget state.  It is useful when a widget is
 *  first being constructed, to initialize option values.
 *
 *  NOTE:  This procedure assumes that there is a valid object context
 *    and a call frame supporting object data member access.  It is
 *    usually called from within the methods of the Archetype base
 *    class, so this is a good assumption.  If it is called anywhere
 *    else, the caller is responsible for installing the object context
 *    and setting up a call frame.
 *
 *  Returns TCL_OK on success, or TCL_ERROR (along with an error
 *  message in the interpreter) if anything goes wrong.
 * ------------------------------------------------------------------------
 */
static int
Itk_ArchSetOption(interp, info, name, value)
    Tcl_Interp *interp;        /* interpreter managing this widget */
    ArchInfo *info;            /* Archetype info */
    CONST char *name;          /* name of configuration option */
    CONST char *value;               /* new value for configuration option */
{
    Tcl_HashEntry *entry;
    ArchOption *archOpt;

    entry = Tcl_FindHashEntry(&info->options, name);
    if (!entry) {
        Tcl_AppendResult(interp,
            "unknown option \"", name, "\"",
            (char*)NULL);
        return TCL_ERROR;
    }
    archOpt = (ArchOption*)Tcl_GetHashValue(entry);

    if (!Tcl_SetVar2(interp, "itk_option", archOpt->switchName,
	    (CONST84 char *)value, 0)) {
        Itk_ArchOptAccessError(interp, info, archOpt);
        return TCL_ERROR;
    }
    return TCL_OK;
}


/*
 * ------------------------------------------------------------------------
 *  Itk_ArchConfigOption()
 *
 *  Sets a configuration option within an Archetype mega-widget.
 *  Changes the "itk_option" array to reflect the new value, and then
 *  invokes any option parts to handle the new setting or propagate
 *  the value down to component parts.
 *
 *  NOTE:  This procedure assumes that there is a valid object context
 *    and a call frame supporting object data member access.  It is
 *    usually called from within the methods of the Archetype base
 *    class, so this is a good assumption.  If it is called anywhere
 *    else, the caller is responsible for installing the object context
 *    and setting up a call frame.
 *
 *  Returns TCL_OK on success, or TCL_ERROR (along with an error
 *  message in the interpreter) if anything goes wrong.
 * ------------------------------------------------------------------------
 */
static int
Itk_ArchConfigOption(interp, info, name, value)
    Tcl_Interp *interp;        /* interpreter managing this widget */
    ArchInfo *info;            /* Archetype info */
    char *name;          /* name of configuration option */
    char *value;               /* new value for configuration option */
{
    int result;
    CONST char *v; 
    char *lastval;
    Tcl_HashEntry *entry;
    ArchOption *archOpt;
    Itcl_ListElem *part;
    ArchOptionPart *optPart;
    Itcl_InterpState istate;

    /*
     *  Query the "itk_option" array to get the current setting.
     */
    entry = Tcl_FindHashEntry(&info->options, name);
    if (!entry) {
        /* Bug 227876
	 * Ensure that the interp result is unshared.
	 */

        Tcl_ResetResult (interp);
        Tcl_AppendResult(interp,
            "unknown option \"", name, "\"",
            (char*)NULL);
        return TCL_ERROR;
    }
    archOpt = (ArchOption*)Tcl_GetHashValue(entry);

    v = Tcl_GetVar2(interp, "itk_option", archOpt->switchName, 0);
    if (v) {
        lastval = (char*)ckalloc((unsigned)(strlen(v)+1));
        strcpy(lastval, v);
    } else {
        lastval = NULL;
    }

    /*
     *  Update the "itk_option" array with the new setting.
     */
    if (!Tcl_SetVar2(interp, "itk_option", archOpt->switchName, value, 0)) {
        Itk_ArchOptAccessError(interp, info, archOpt);
        result = TCL_ERROR;
        goto configDone;
    }

    /*
     *  Scan through all option parts to handle the new setting.
     */
    result = TCL_OK;
    part   = Itcl_FirstListElem(&archOpt->parts);

    while (part) {
        optPart = (ArchOptionPart*)Itcl_GetListValue(part);
        result  = (*optPart->configProc)(interp, info->itclObj,
            optPart->clientData, value);

        if (result != TCL_OK) {
            Itk_ArchOptConfigError(interp, info, archOpt);
            break;
        }
        part = Itcl_NextListElem(part);
    }

    /*
     *  If the option configuration failed, then set the option
     *  back to its previous settings.  Scan back through all of
     *  the option parts and sync them up with the old value.
     */
    if (result == TCL_ERROR) {
        istate = Itcl_SaveInterpState(interp, result);

        Tcl_SetVar2(interp, "itk_option", archOpt->switchName, lastval, 0);

        part = Itcl_FirstListElem(&archOpt->parts);
        while (part) {
            optPart = (ArchOptionPart*)Itcl_GetListValue(part);
            (*optPart->configProc)(interp, info->itclObj,
                optPart->clientData, lastval);

            part = Itcl_NextListElem(part);
        }
        result = Itcl_RestoreInterpState(interp, istate);
    }

    archOpt->flags |= ITK_ARCHOPT_INIT;  /* option has been set */

configDone:
    if (lastval) {
        ckfree(lastval);
    }
    return result;
}


/*
 * ------------------------------------------------------------------------
 *  Itk_ArchOptConfigError()
 *
 *  Simply utility which adds error information after a option
 *  configuration fails.  Adds traceback information to the given
 *  interpreter.
 * ------------------------------------------------------------------------
 */
static void
Itk_ArchOptConfigError(interp, info, archOpt)
    Tcl_Interp *interp;            /* interpreter handling this object */
    ArchInfo *info;                /* info associated with mega-widget */
    ArchOption *archOpt;           /* configuration option that failed */
{
    Tcl_Obj *objPtr;

    objPtr = Tcl_NewStringObj((char*)NULL, 0);
    Tcl_IncrRefCount(objPtr);

    Tcl_AppendToObj(objPtr, "\n    (while configuring option \"", -1);
    Tcl_AppendToObj(objPtr, archOpt->switchName, -1);
    Tcl_AppendToObj(objPtr, "\"", -1);

    if (info->itclObj && info->itclObj->accessCmd) {
        Tcl_AppendToObj(objPtr, " for widget \"", -1);
        Tcl_GetCommandFullName(interp, info->itclObj->accessCmd, objPtr);
        Tcl_AppendToObj(objPtr, "\")", -1);
    }
    Tcl_AddErrorInfo(interp, Tcl_GetStringFromObj(objPtr, (int*)NULL));
    Tcl_DecrRefCount(objPtr);
}


/*
 * ------------------------------------------------------------------------
 *  Itk_ArchOptAccessError()
 *
 *  Simply utility which adds error information after an option
 *  value access fails.  Adds traceback information to the given
 *  interpreter.
 * ------------------------------------------------------------------------
 */
static void
Itk_ArchOptAccessError(interp, info, archOpt)
    Tcl_Interp *interp;            /* interpreter handling this object */
    ArchInfo *info;                /* info associated with mega-widget */
    ArchOption *archOpt;           /* option that couldn't be accessed */
{
    Tcl_ResetResult(interp);

    Tcl_AppendResult(interp,
        "internal error: cannot access itk_option(", archOpt->switchName, ")",
        (char*)NULL);

    if (info->itclObj->accessCmd) {
        Tcl_Obj *resultPtr = Tcl_GetObjResult(interp);
        Tcl_AppendToObj(resultPtr, " in widget \"", -1);
        Tcl_GetCommandFullName(interp, info->itclObj->accessCmd, resultPtr);
        Tcl_AppendToObj(resultPtr, "\"", -1);
    }
}


/*
 * ------------------------------------------------------------------------
 *  Itk_GetArchInfo()
 *
 *  Finds the extra Archetype info associated with the given object.
 *  Returns TCL_OK and a pointer to the info if found.  Returns
 *  TCL_ERROR along with an error message in interp->result if not.
 * ------------------------------------------------------------------------
 */
static int
Itk_GetArchInfo(interp, contextObj, infoPtr)
    Tcl_Interp *interp;            /* interpreter handling this object */
    ItclObject *contextObj;        /* object with desired data */
    ArchInfo **infoPtr;            /* returns:  pointer to extra info */
{
    Tcl_HashTable *objsWithArchInfo;
    Tcl_HashEntry *entry;

    /*
     *  If there is any problem finding the info, return an error.
     */
    objsWithArchInfo = ItkGetObjsWithArchInfo(interp);
    entry = Tcl_FindHashEntry(objsWithArchInfo, (char*)contextObj);

    if (!entry) {
        Tcl_AppendResult(interp,
            "internal error: no Archetype information for widget",
            (char*)NULL);

        if (contextObj->accessCmd) {
            Tcl_Obj *resultPtr = Tcl_GetObjResult(interp);
            Tcl_AppendToObj(resultPtr, " \"", -1);
            Tcl_GetCommandFullName(interp, contextObj->accessCmd, resultPtr);
            Tcl_AppendToObj(resultPtr, "\"", -1);
        }
        return TCL_ERROR;
    }

    /*
     *  Otherwise, return the requested info.
     */
    *infoPtr = (ArchInfo*)Tcl_GetHashValue(entry);
    return TCL_OK;
}


/*
 * ------------------------------------------------------------------------
 *  Itk_CreateArchComponent()
 *
 *  Creates the data representing a component widget within an Archetype
 *  mega-widget.  Each component has an access command that is used to
 *  communicate with it.  Each component is registered by its symbolic
 *  name in the "itk_component" array.
 *
 *  Returns a pointer to the new record.  If anything goes wrong,
 *  this returns NULL, along with an error message in the interpreter.
 * ------------------------------------------------------------------------
 */
static ArchComponent*
Itk_CreateArchComponent(interp, info, name, cdefn, accessCmd)
    Tcl_Interp *interp;            /* interpreter managing the object */
    ArchInfo *info;                /* info associated with mega-widget */
    char *name;                    /* symbolic name for this component */
    ItclClass *cdefn;              /* component created in this class */
    Tcl_Command accessCmd;         /* access command for component */
{
    CONST char *init;
    CONST char *wname;
    ArchComponent *archComp;
    ArchOption *archOpt;
    Tk_Window tkwin;
    Tcl_HashEntry *entry;
    Tcl_HashSearch place;
    ItclMember *memPtr;

    /*
     *  Save this component in the itk_component() array.
     */
    wname = Tcl_GetCommandName(interp, accessCmd);
    Tcl_SetVar2(interp, "itk_component", name, (char *)wname, 0);

    /*
     *  If the symbolic name for the component is "hull", then this
     *  is the toplevel or frame that embodies a mega-widget.  Update
     *  the Archtype info to include the window token.
     */
    tkwin = Tk_NameToWindow(interp, (char *)wname, Tk_MainWindow(interp));

    if (strcmp(name, "hull") == 0) {
        if (tkwin == NULL) {
            Tcl_AppendResult(interp,
                "cannot find hull window with access command \"", wname, "\"",
                (char*)NULL);
            return NULL;
        }
        info->tkwin = tkwin;

        /*
         *  We are now in a position to query configuration options
         *  relative to this window.  Scan through all existing options
         *  and update the initial values according to the X11 resource
         *  database.
         */
        entry = Tcl_FirstHashEntry(&info->options, &place);
        while (entry) {
            archOpt = (ArchOption*)Tcl_GetHashValue(entry);

            init = NULL;
            if (archOpt->resName && archOpt->resClass) {
                init = Tk_GetOption(tkwin, archOpt->resName, archOpt->resClass);
            }

            if (init && (!archOpt->init || strcmp(init, archOpt->init) != 0)) {
                if (!archOpt->init) {
                    ckfree(archOpt->init);
                }
                archOpt->init = (char*)ckalloc((unsigned)(strlen(init)+1));
                strcpy(archOpt->init, init);

                if (Itk_ArchSetOption(interp, info,
                    archOpt->switchName, init) != TCL_OK) {
                    return NULL;
                }
            }
            entry = Tcl_NextHashEntry(&place);
        }
    }

    /*
     *  Create the record to represent this component.
     */
    archComp = (ArchComponent*)ckalloc(sizeof(ArchComponent));

    memPtr = (ItclMember*)ckalloc(sizeof(ItclMember));
    memPtr->interp      = interp;
    memPtr->classDefn   = cdefn;
    memPtr->name        = NULL;
    memPtr->fullname    = NULL;
    memPtr->flags       = 0;
    memPtr->protection  = ITCL_PUBLIC;
    memPtr->code        = NULL;

    archComp->member     = memPtr;
    archComp->accessCmd  = accessCmd;
    archComp->tkwin      = tkwin;
    archComp->pathName   = (char *) ckalloc((unsigned)(strlen(wname)+1));
    strcpy(archComp->pathName, wname);

    return archComp;
}


/*
 * ------------------------------------------------------------------------
 *  Itk_DelArchComponent()
 *
 *  Destroys an Archetype component record previously created by
 *  Itk_CreateArchComponent().
 * ------------------------------------------------------------------------
 */
static void
Itk_DelArchComponent(archComp)
    ArchComponent *archComp;  /* pointer to component data */
{
    ckfree((char*)archComp->member);
    ckfree((char*)archComp->pathName);
    ckfree((char*)archComp);
}


/*
 * ------------------------------------------------------------------------
 *  Itk_GetArchOption()
 *
 *  Finds or creates the data representing a composite configuration
 *  option for an Archetype mega-widget.  Each option acts as a single
 *  entity, but is composed of several parts which propagate changes
 *  down to the component widgets.  If the option already exists, then
 *  the specified resource name and resource class must match the
 *  existing definition.
 *
 *  If the option is created, an initial value for is determined by
 *  querying the X11 resource database, and if this fails, the
 *  hard-wired default value is used.
 *
 *  If successful, returns TCL_OK along with a pointer to the option
 *  record.  Returns TCL_ERROR (along with an error message in the
 *  interpreter) if anything goes wrong.
 * ------------------------------------------------------------------------
 */
static int
Itk_GetArchOption(interp, info, switchName, resName, resClass,
    defVal, currVal, aoPtr)

    Tcl_Interp *interp;            /* interpreter managing the object */
    ArchInfo *info;                /* info for Archetype mega-widget */
    char *switchName;              /* name of command-line switch */
    char *resName;                 /* resource name in X11 database */
    char *resClass;                /* resource class name in X11 database */
    CONST char *defVal;            /* last-resort default value */
    char *currVal;                 /* current option value */
    ArchOption **aoPtr;            /* returns: option record */
{
    int result = TCL_OK;

    int newEntry;
    char *name;
    ArchOption *archOpt;
    Tcl_HashEntry *entry;

    /*
     *  If the switch does not have a leading "-", add it on.
     */
    if (*switchName != '-') {
        name = ckalloc((unsigned)(strlen(switchName)+2));
        *name = '-';
        strcpy(name+1, switchName);
    } else {
        name = switchName;
    }

    /*
     *  See if an option already exists with the switch name.
     *  If it does, then make sure that the given resource name
     *  and resource class match the existing definition.
     */
    entry = Tcl_CreateHashEntry(&info->options, name, &newEntry);
    if (!newEntry) {
        archOpt = (ArchOption*)Tcl_GetHashValue(entry);

        if (resName && !archOpt->resName) {
            archOpt->resName = (char*)ckalloc((unsigned)(strlen(resName)+1));
            strcpy(archOpt->resName, resName);
        }
        else if (resName && strcmp(archOpt->resName, resName) != 0) {
            Tcl_AppendResult(interp,
                "bad resource name \"", resName, "\" for option \"",
                name, "\": should be \"", archOpt->resName, "\"",
                (char*)NULL);
            result = TCL_ERROR;
            goto getArchOptionDone;
        }

        if (resClass && !archOpt->resClass) {
            archOpt->resClass = (char*)ckalloc((unsigned)(strlen(resClass)+1));
            strcpy(archOpt->resClass, resClass);
        }
        else if (resClass && strcmp(archOpt->resClass, resClass) != 0) {
            Tcl_AppendResult(interp,
                "bad resource class \"", resClass, "\" for option \"",
                name, "\": should be \"", archOpt->resClass, "\"",
                (char*)NULL);
            result = TCL_ERROR;
            goto getArchOptionDone;
        }

        if (!archOpt->init) {
            Itk_InitArchOption(interp, info, archOpt, defVal, currVal);
        }
        *aoPtr = archOpt;

        result = TCL_OK;
        goto getArchOptionDone;
    }

    /*
     *  Create the record to represent this option, and save it
     *  in the option table.
     */
    archOpt = (ArchOption*)ckalloc(sizeof(ArchOption));

    archOpt->switchName = (char*)ckalloc((unsigned)(strlen(name)+1));
    strcpy(archOpt->switchName, name);

    if (resName) {
        archOpt->resName = (char*)ckalloc((unsigned)(strlen(resName)+1));
        strcpy(archOpt->resName, resName);
    }
    else {
        archOpt->resName = NULL;
    }

    if (resClass) {
        archOpt->resClass = (char*)ckalloc((unsigned)(strlen(resClass)+1));
        strcpy(archOpt->resClass, resClass);
    }
    else {
        archOpt->resClass = NULL;
    }

    archOpt->flags = 0;
    Itcl_InitList(&archOpt->parts);

    archOpt->init = NULL;
    Itk_InitArchOption(interp,info,archOpt,defVal,currVal);

    Tcl_SetHashValue(entry, (ClientData)archOpt);
    Itk_OptListAdd(&info->order, entry);

    *aoPtr = archOpt;

getArchOptionDone:
    if (name != switchName) {
        ckfree(name);
    }
    return result;
}

/*
 * ------------------------------------------------------------------------
 *  Itk_InitArchOption()
 *
 *  Sets the initial value for a composite configuration option for
 *  an Archetype mega-widget.  This is usually invoked when an option
 *  is first created by Itk_GetArchOption().  It queries the X11
 *  resource database for an initial value, and if nothing is found,
 *  falls back on a last-resort value.  It stores the initial value
 *  in the "itk_option" array, adds a copy to the option info, and
 *  returns.
 *
 *  If successful, returns TCL_OK along with a pointer to the option
 *  record.  Returns TCL_ERROR (along with an error message in the
 *  interpreter) if anything goes wrong.
 * ------------------------------------------------------------------------
 */
static void
Itk_InitArchOption(interp, info, archOpt, defVal, currVal)
    Tcl_Interp *interp;            /* interpreter managing the object */
    ArchInfo *info;                /* info for Archetype mega-widget */
    ArchOption *archOpt;           /* option to initialize */
    CONST char *defVal;            /* last-resort default value */
    char *currVal;                 /* current option value */
{
    CONST char *init = NULL;

    int result;
    CONST char *ival;
    char c;
    ItclContext context;

    /*
     *  If the option is already initialized, then abort.
     */
    if (archOpt->init) {
        return;
    }

    /*
     *  If this widget has a Tk window, query the X11 resource
     *  database for an initial option value.  If all else fails,
     *  use the hard-wired default value.
     */
    if (archOpt->resName && archOpt->resClass && info->tkwin != NULL) {
        init = Tk_GetOption(info->tkwin, archOpt->resName, archOpt->resClass);
    }
    if (init == NULL) {
        init = defVal;
    }

    /*
     *  Normally, the initial value for the itk_option array is
     *  the same as the initial value for the option.  Watch
     *  out for the fixed Tk options (-class, -colormap, -screen
     *  and -visual).  Since these cannot be modified later,
     *  they must be set to their current value.
     */
    c = *(archOpt->switchName+1);

    if ((c == 'c' && strcmp(archOpt->switchName,"-class") == 0) ||
        (c == 'c' && strcmp(archOpt->switchName,"-colormap") == 0) ||
        (c == 's' && strcmp(archOpt->switchName,"-screen") == 0) ||
        (c == 'v' && strcmp(archOpt->switchName,"-visual") == 0)) {
        ival = currVal;
    }
    else {
        ival = init;
    }

    /*
     *  Set the initial value in the itk_option array.
     *  Since this might be called from the itk::option-parser
     *  namespace, reinstall the object context.
     */
    result = Itcl_PushContext(interp, (ItclMember*)NULL,
        info->itclObj->classDefn, info->itclObj, &context);

    if (result == TCL_OK) {
	/*
	 * Casting away CONST of ival only to satisfy Tcl 8.3 and
	 * earlier headers.
	 */
        Tcl_SetVar2(interp, "itk_option", archOpt->switchName,
            (char *)((ival) ? ival : ""), 0);
        Itcl_PopContext(interp, &context);
    }

    if (ival) {
        archOpt->init = (char*)ckalloc((unsigned)(strlen(ival)+1));
        strcpy(archOpt->init, ival);
    }
}

/*
 * ------------------------------------------------------------------------
 *  Itk_DelArchOption()
 *
 *  Destroys an Archetype configuration option previously created by
 *  Itk_CreateArchOption().
 * ------------------------------------------------------------------------
 */
static void
Itk_DelArchOption(archOpt)
    ArchOption *archOpt;  /* pointer to option data */
{
    Itcl_ListElem *elem;
    ArchOptionPart *optPart;

    /*
     *  Delete all "parts" relating to component widgets.
     */
    elem = Itcl_FirstListElem(&archOpt->parts);
    while (elem) {
        optPart = (ArchOptionPart*)Itcl_GetListValue(elem);
        Itk_DelOptionPart(optPart);
        elem = Itcl_DeleteListElem(elem);
    }

    /*
     *  Free any remaining data.
     */
    ckfree(archOpt->switchName);
    if (archOpt->resName) {
        ckfree(archOpt->resName);
    }
    if (archOpt->resClass) {
        ckfree(archOpt->resClass);
    }
    if (archOpt->init) {
        ckfree(archOpt->init);
    }
    ckfree((char*)archOpt);
}


/*
 * ------------------------------------------------------------------------
 *  Itk_CreateOptionPart()
 *
 *  Creates the data representing a part within a configuration option
 *  for an Archetype mega-widget.  Each part has a bit of code used to
 *  apply configuration changes to some part of the mega-widget.
 *  This is characterized by a bit of ClientData, and a "config"
 *  procedure that knows how to execute it.  The ClientData is
 *  automatically disposed of by the delete proc when this option
 *  part is destroyed.
 *
 *  Option parts typically come from two sources:  Options defined
 *  in the class definition, and options propagated upward from
 *  component parts.
 *
 *  Returns a pointer to the new option part.
 * ------------------------------------------------------------------------
 */
static ArchOptionPart*
Itk_CreateOptionPart(interp, cdata, cproc, dproc, from)
    Tcl_Interp *interp;              /* interpreter handling this request */
    ClientData cdata;                /* data representing this part */
    Itk_ConfigOptionPartProc *cproc; /* proc used to apply config changes */
    Tcl_CmdDeleteProc *dproc;        /* proc used to clean up ClientData */
    ClientData from;                 /* who contributed this option */
{
    ArchOptionPart *optPart;

    /*
     *  Create the record to represent this part of the option.
     */
    optPart = (ArchOptionPart*)ckalloc(sizeof(ArchOptionPart));
    optPart->clientData = cdata;
    optPart->configProc = cproc;
    optPart->deleteProc = dproc;
    optPart->from       = from;

    return optPart;
}


/*
 * ------------------------------------------------------------------------
 *  Itk_AddOptionPart()
 *
 *  Integrates an option part into a composite configuration option
 *  for an Archetype mega-widget.  If a composite option does not
 *  yet exist with the specified switch name, it is created automatically.
 *
 *  Adds the option part onto the composite list, and reconfigures
 *  the widget to update this option properly.
 *
 *  Returns TCL_OK on success, or TCL_ERROR (along with an error message
 *  in the interpreter) if anything goes wrong.
 * ------------------------------------------------------------------------
 */
static int
Itk_AddOptionPart(interp, info, switchName, resName, resClass,
    defVal, currVal, optPart, raOpt)

    Tcl_Interp *interp;              /* interpreter handling this request */
    ArchInfo *info;                  /* info for Archetype mega-widget */
    char *switchName;                /* name of command-line switch */
    char *resName;                   /* resource name in X11 database */
    char *resClass;                  /* resource class name in X11 database */
    CONST char *defVal;              /* last-resort default value */
    char *currVal;                   /* current value (or NULL) */
    ArchOptionPart *optPart;         /* part to be added in */
    ArchOption **raOpt;              /* returns: option containing new part */
{
    CONST char *init = NULL;

    int result;
    ArchOption *archOpt;
    ItclContext context;

    *raOpt = NULL;

    /*
     *  Find or create a composite option for the mega-widget.
     */
    result = Itk_GetArchOption(interp, info, switchName, resName, resClass,
        defVal, currVal, &archOpt);

    if (result != TCL_OK) {
        return TCL_ERROR;
    }

    /*
     *  Add the option part to the composite option.  If the
     *  composite option has already been configured, then
     *  simply update this part to the current value.  Otherwise,
     *  leave the configuration to Itk_ArchInitCmd().
     */
    Itcl_AppendList(&archOpt->parts, (ClientData)optPart);

    if ((archOpt->flags & ITK_ARCHOPT_INIT) != 0) {

        result = Itcl_PushContext(interp, (ItclMember*)NULL,
            info->itclObj->classDefn, info->itclObj, &context);

        if (result == TCL_OK) {
            init = Tcl_GetVar2(interp, "itk_option", archOpt->switchName, 0);
            Itcl_PopContext(interp, &context);
        }

        if (!init) {
            Itk_ArchOptAccessError(interp, info, archOpt);
            return TCL_ERROR;
        }

        if (!currVal || (strcmp(init,currVal) != 0)) {
            result  = (*optPart->configProc)(interp, info->itclObj,
                optPart->clientData, init);

            if (result != TCL_OK) {
                Itk_ArchOptConfigError(interp, info, archOpt);
                return TCL_ERROR;
            }
        }
    }

    *raOpt = archOpt;
    return TCL_OK;
}


/*
 * ------------------------------------------------------------------------
 *  Itk_FindArchOptionPart()
 *
 *  Searches for a specific piece of a composite configuration option
 *  for an Archetype mega-widget.  The specified name is treated as the
 *  "switch" name (e.g., "-option"), but this procedure will recognize
 *  it even without the leading "-".
 *
 *  Returns a pointer to the option with the matching switch name and
 *  source, or NULL if the option is not recognized.
 * ------------------------------------------------------------------------
 */
static ArchOptionPart*
Itk_FindArchOptionPart(info, switchName, from)
    ArchInfo *info;                /* info for Archetype mega-widget */
    char *switchName;              /* name of command-line switch */
    ClientData from;               /* who contributed this option */
{
    ArchOptionPart *optPart = NULL;

    char *name;
    Tcl_HashEntry *entry;
    ArchOption *archOpt;
    ArchOptionPart *op;
    Itcl_ListElem *elem;

    /*
     *  If the switch does not have a leading "-", add it on.
     */
    if (*switchName != '-') {
        name = ckalloc((unsigned)(strlen(switchName)+2));
        *name = '-';
        strcpy(name+1, switchName);
    } else {
        name = switchName;
    }

    /*
     *  Look for a composite option, and then for a part with the
     *  matching source.
     */
    entry = Tcl_FindHashEntry(&info->options, name);

    if (entry) {
        archOpt = (ArchOption*)Tcl_GetHashValue(entry);
        elem = Itcl_FirstListElem(&archOpt->parts);
        while (elem) {
            op = (ArchOptionPart*)Itcl_GetListValue(elem);
            if (op->from == from) {
                optPart = op;
                break;
            }
            elem = Itcl_NextListElem(elem);
        }
    }

    if (name != switchName) {
        ckfree(name);
    }
    return optPart;
}


/*
 * ------------------------------------------------------------------------
 *  Itk_RemoveArchOptionPart()
 *
 *  Searches for a specific piece of a composite configuration option
 *  for an Archetype mega-widget.  The specified name is treated as the
 *  "switch" name (e.g., "-option"), but this procedure will recognize
 *  it even without the leading "-".  If an option part with the
 *  specified name and source is found on the list, it is removed.
 *
 *  NOTE:  This procedure assumes that there is a valid object context
 *    and a call frame supporting object data member access.  It is
 *    usually called from within the methods of the Archetype base
 *    class, so this is a good assumption.  If it is called anywhere
 *    else, the caller is responsible for installing the object context
 *    and setting up a call frame.
 *
 *  Returns non-zero if the part was found and removed, and 0 otherwise.
 * ------------------------------------------------------------------------
 */
static int
Itk_RemoveArchOptionPart(info, switchName, from)
    ArchInfo *info;                /* info for Archetype mega-widget */
    char *switchName;              /* name of command-line switch */
    ClientData from;               /* who contributed this option */
{
    int result = 0;

    char *name;
    Tcl_HashEntry *entry;
    ArchOption *archOpt;
    ArchOptionPart *op;
    Itcl_ListElem *elem;


    /*
     *  If the switch does not have a leading "-", add it on.
     */
    if (*switchName != '-') {
        name = ckalloc((unsigned)(strlen(switchName)+2));
        *name = '-';
        strcpy(name+1, switchName);
    } else {
        name = switchName;
    }

    /*
     *  Look for a composite option, and then for a part with the
     *  matching source.  If found, remove it.
     */
    entry = Tcl_FindHashEntry(&info->options, name);

    if (entry) {
        archOpt = (ArchOption*)Tcl_GetHashValue(entry);
        elem = Itcl_FirstListElem(&archOpt->parts);
        while (elem) {
            op = (ArchOptionPart*)Itcl_GetListValue(elem);
            if (op->from == from) {
                Itk_DelOptionPart(op);
                result = 1;
                elem = Itcl_DeleteListElem(elem);
            }
            else {
                elem = Itcl_NextListElem(elem);
            }
        }

        /*
         *  If this option is now dead (no parts left), then
         *  remove it from the widget.  Be careful to delete it
         *  from the "itk_option" array as well.
         */
        if (Itcl_GetListLength(&archOpt->parts) == 0) {
            Tcl_UnsetVar2(info->itclObj->classDefn->interp,
                "itk_option", archOpt->switchName, 0);

            Itk_DelArchOption(archOpt);
            Itk_OptListRemove(&info->order, entry);
            Tcl_DeleteHashEntry(entry);
        }
    }

    if (name != switchName) {
        ckfree(name);
    }
    return result;
}


/*
 * ------------------------------------------------------------------------
 *  Itk_IgnoreArchOptionPart()
 *
 *  Removes the specified part from a composite configuration option
 *  for an Archetype mega-widget.  This is usually called before
 *  keeping or renaming an option, to make sure that the option
 *  is not already integrated elsewhere on the composite list.
 *  This also handles the action of "ignoring" a configuration option.
 *
 *  NOTE:  This procedure assumes that there is a valid object context
 *    and a call frame supporting object data member access.  It is
 *    usually called from within the methods of the Archetype base
 *    class, so this is a good assumption.  If it is called anywhere
 *    else, the caller is responsible for installing the object context
 *    and setting up a call frame.
 *
 *  Returns non-zero if the part was found and removed, and 0 otherwise.
 * ------------------------------------------------------------------------
 */
static int
Itk_IgnoreArchOptionPart(info, opt)
    ArchInfo *info;                /* info for Archetype mega-widget */
    GenericConfigOpt *opt;         /* part to be ignored */
{
    int result = 0;

    Tcl_HashEntry *entry;
    ArchOptionPart *op;
    Itcl_ListElem *elem;

    /*
     *  If the part is not integrated, then do nothing.
     *  Otherwise, find the missing part and remove it.
     */
    if (opt->integrated) {
        elem = Itcl_FirstListElem(&opt->integrated->parts);
        while (elem) {
            op = (ArchOptionPart*)Itcl_GetListValue(elem);
            if (op == opt->optPart) {
                Itk_DelOptionPart(op);
                result = 1;
                elem = Itcl_DeleteListElem(elem);
            }
            else {
                elem = Itcl_NextListElem(elem);
            }
        }

        /*
         *  If this option is now dead (no parts left), then
         *  remove it from the widget.  Be careful to delete it
         *  from the "itk_option" array as well.
         */
        if (Itcl_GetListLength(&opt->integrated->parts) == 0) {
            Tcl_UnsetVar2(info->itclObj->classDefn->interp,
                "itk_option", opt->integrated->switchName, 0);

            entry = Tcl_FindHashEntry(&info->options,
                opt->integrated->switchName);

            if (entry) {
                Itk_OptListRemove(&info->order, entry);
                Tcl_DeleteHashEntry(entry);
            }
            Itk_DelArchOption(opt->integrated);
        }

        /*
         *  Forget that this part was ever integrated.
         */
        opt->integrated = NULL;
        opt->optPart = NULL;
    }
    return result;
}


/*
 * ------------------------------------------------------------------------
 *  Itk_DelOptionPart()
 *
 *  Destroys part of an Archetype configuration option created by
 *  Itk_CreateOptionPart().
 * ------------------------------------------------------------------------
 */
static void
Itk_DelOptionPart(optPart)
    ArchOptionPart *optPart;  /* option part data to be destroyed */
{
    if (optPart->clientData && optPart->deleteProc) {
        (*optPart->deleteProc)(optPart->clientData);
    }
    ckfree((char*)optPart);
}


/*
 * ------------------------------------------------------------------------
 *  Itk_CreateConfigCmdline()
 *
 *  Creates the data representing a command line for a "configure"
 *  operation.  Each "configure" command has the following form:
 *
 *      <object> configure -<option> <value>
 *
 *  The first three arguments are created in this procedure.  The
 *  <value> argument is reinitialized each time the command is
 *  executed.
 *
 *  Returns a pointer to the new command record.
 * ------------------------------------------------------------------------
 */
static ConfigCmdline*
Itk_CreateConfigCmdline(interp, accessCmd, switchName)
    Tcl_Interp *interp;              /* interpreter handling this request */
    Tcl_Command accessCmd;           /* command for <object> being config'd */
    char *switchName;                /* switch name of option being config'd */
{
    int i;
    ConfigCmdline *cmdlinePtr;
    Tcl_Obj *objPtr;

    /*
     *  Create the record to represent this part of the option.
     */
    cmdlinePtr = (ConfigCmdline*)ckalloc(sizeof(ConfigCmdline));

    objPtr = Tcl_NewStringObj((char*)NULL, 0);
    Tcl_GetCommandFullName(interp, accessCmd, objPtr);
    cmdlinePtr->objv[0] = objPtr;
    cmdlinePtr->objv[1] = Tcl_NewStringObj("configure", -1);
    cmdlinePtr->objv[2] = Tcl_NewStringObj(switchName, -1);

    for (i=0; i < 3; i++) {
        Tcl_IncrRefCount(cmdlinePtr->objv[i]);
    }
    return cmdlinePtr;
}

/*
 * ------------------------------------------------------------------------
 *  Itk_DeleteConfigCmdline()
 *
 *  Deletes the data created by Itk_CreateConfigCmdline.  Called
 *  when an option part is deleted to free up the memory associated
 *  with the configure command.
 * ------------------------------------------------------------------------
 */
static void
Itk_DeleteConfigCmdline(cdata)
    ClientData cdata;                /* command to be freed */
{
    ConfigCmdline *cmdlinePtr = (ConfigCmdline*)cdata;
    int i;

    /*
     *  TRICKY NOTE:  Decrement the reference counts for only the
     *    first three arguments on the command line.  The fourth
     *    argument is released after each configure operation.
     */
    for (i=0; i < 3; i++) {
        Tcl_DecrRefCount(cmdlinePtr->objv[i]);
    }
    ckfree((char*)cmdlinePtr);
}


/*
 * ------------------------------------------------------------------------
 *  Itk_CreateGenericOptTable()
 *
 *  Parses a string describing a widget's configuration options (of the
 *  form returned by the usual widget "configure" method) and creates
 *  a hash table for easy lookup of option information.  Entries in
 *  the hash table are indexed by switch names like "-background".
 *  Values are GenericConfigOpt records.  Alias options like "-bg" are
 *  ignored.
 *
 *  This table is used by option parsing commands in "itk::option-parser"
 *  to validate widget options.
 *
 *  Returns a pointer to a new hash table, which should later be freed
 *  via Itk_DelGenericOptTable().  Returns NULL if an error is found in
 *  the configuration list.
 * ------------------------------------------------------------------------
 */
static Tcl_HashTable*
Itk_CreateGenericOptTable(interp, options)
    Tcl_Interp *interp;          /* interpreter handling this request */
    char *options;               /* string description of config options */
{
    int confc;
    char **confv = NULL;
    int optc;
    char **optv = NULL;

    int i, newEntry;
    Tcl_HashTable *tPtr;
    Tcl_HashEntry *entry;
    GenericConfigOpt *info;

    tPtr = (Tcl_HashTable*)ckalloc(sizeof(Tcl_HashTable));
    Tcl_InitHashTable(tPtr, TCL_STRING_KEYS);

    /*
     *  Split the list of options and store each one in the table.
     *  Only consider options with all 5 required components.  Avoid
     *  aliases like "-bg".
     */
    if (Tcl_SplitList(interp, options, &confc, &confv) != TCL_OK) {
        goto tableFail;
    }
    for (i=0; i < confc; i++) {
        if (Tcl_SplitList(interp, confv[i], &optc, &optv) != TCL_OK) {
            goto tableFail;
        }
        if (optc == 5) {    /* avoid aliased options */
            entry = Tcl_CreateHashEntry(tPtr, optv[0], &newEntry);
            if (newEntry) {
                info = (GenericConfigOpt*)ckalloc(sizeof(GenericConfigOpt));
                info->switchName = optv[0];
                info->resName    = optv[1];
                info->resClass   = optv[2];
                info->init       = optv[3];
                info->value      = optv[4];
                info->storage    = optv;
                info->integrated = NULL;
                info->optPart    = NULL;
                Tcl_SetHashValue(entry, (ClientData)info);
            }
        }
        else {
            ckfree((char*)optv);
        }
    }

    ckfree((char*)confv);
    return tPtr;

tableFail:
    if (confv) {
        ckfree((char*)confv);
    }
    Itk_DelGenericOptTable(tPtr);
    return NULL;
}


/*
 * ------------------------------------------------------------------------
 *  Itk_DelGenericOptTable()
 *
 *  Destroys an option table previously created by
 *  Itk_CreateGenericOptTable() and frees all memory associated with it.
 *  Should be called whenever a table is no longer needed, to free up
 *  resources.
 * ------------------------------------------------------------------------
 */
static void
Itk_DelGenericOptTable(tPtr)
    Tcl_HashTable *tPtr;  /* option table to be destroyed */
{
    Tcl_HashEntry *entry;
    Tcl_HashSearch place;
    GenericConfigOpt *info;

    /*
     *  Scan through all options in the table and free entries.
     */
    entry = Tcl_FirstHashEntry(tPtr, &place);
    while (entry) {
        info = (GenericConfigOpt*)Tcl_GetHashValue(entry);
        ckfree((char*)info->storage);
        ckfree((char*)info);
        entry = Tcl_NextHashEntry(&place);
    }

    Tcl_DeleteHashTable(tPtr);
    ckfree((char*)tPtr);
}


/*
 * ------------------------------------------------------------------------
 *  Itk_CreateGenericOpt()
 *
 *  Parses a string describing a widget's configuration option (of the
 *  form returned by the usual widget "configure" method) and creates
 *  a representation for one option.  Similar to
 *  Itk_CreateGenericOptTable(), but only handles one option at a
 *  time.
 *
 *  Returns a pointer to the option info, which should later be freed
 *  via Itk_DelGenericOpt().  Returns NULL (along with an error
 *  message in the interpreter) if an error is found.
 *
 *  SIDE EFFECT:  Resets the interpreter result.
 * ------------------------------------------------------------------------
 */
static GenericConfigOpt*
Itk_CreateGenericOpt(interp, switchName, accessCmd)
    Tcl_Interp *interp;          /* interpreter handling this request */
    char *switchName;            /* command-line switch for option */
    Tcl_Command accessCmd;       /* access command for component */
{
    GenericConfigOpt *genericOpt = NULL;
    Tcl_Obj *codePtr = NULL;

    int optc, result;
    char **optv;
    char *name, *info;
    Tcl_Obj *resultPtr;

    /*
     *  If the switch does not have a leading "-", add it on.
     */
    if (*switchName != '-') {
        name = ckalloc((unsigned)(strlen(switchName)+2));
        *name = '-';
        strcpy(name+1, switchName);
    } else {
        name = switchName;
    }

    /*
     *  Build a "configure" command to query info for the requested
     *  option.  Evaluate the command and get option info.
     */
    codePtr = Tcl_NewStringObj((char*)NULL, 0);
    Tcl_IncrRefCount(codePtr);

    Tcl_GetCommandFullName(interp, accessCmd, codePtr);
    Tcl_AppendToObj(codePtr, " configure ", -1);
    Tcl_AppendToObj(codePtr, name, -1);

    if (Tcl_EvalObj(interp, codePtr) != TCL_OK) {
        goto optionDone;
    }

    /*
     *  Only consider options with all 5 required components.  Avoid
     *  aliases like "-bg".
     */
    resultPtr = Tcl_GetObjResult(interp);
    Tcl_IncrRefCount(resultPtr);
    info = Tcl_GetStringFromObj(resultPtr, (int*)NULL);

    result = Tcl_SplitList(interp, info, &optc, &optv);

    Tcl_DecrRefCount(resultPtr);

    if (result != TCL_OK) {
        goto optionDone;
    }
    if (optc == 5) {    /* avoid aliased options */
        genericOpt = (GenericConfigOpt*)ckalloc(sizeof(GenericConfigOpt));
        genericOpt->switchName = optv[0];
        genericOpt->resName    = optv[1];
        genericOpt->resClass   = optv[2];
        genericOpt->init       = optv[3];
        genericOpt->value      = optv[4];
        genericOpt->storage    = optv;
        genericOpt->integrated = NULL;
        genericOpt->optPart    = NULL;
    }
    else {
        ckfree((char*)optv);
    }

optionDone:
    if (name != switchName) {
        ckfree(name);
    }
    if (codePtr) {
        Tcl_DecrRefCount(codePtr);
    }
    if (genericOpt) {
        Tcl_ResetResult(interp);
    }
    return genericOpt;
}


/*
 * ------------------------------------------------------------------------
 *  Itk_DelGenericOpt()
 *
 *  Destroys a generic option previously created by Itk_CreateGenericOpt()
 *  and frees all memory associated with it.  Should be called whenever
 *  an option representation is no longer needed, to free up resources.
 * ------------------------------------------------------------------------
 */
static void
Itk_DelGenericOpt(opt)
    GenericConfigOpt *opt;  /* option info to be destroyed */
{
    ckfree((char*)opt->storage);
    ckfree((char*)opt);
}


/*
 * ------------------------------------------------------------------------
 *  ItkGetObjsWithArchInfo()
 *
 *  Returns a pointer to a hash table containing the list of registered
 *  objects in the specified interpreter.  If the hash table does not
 *  already exist, it is created.
 * ------------------------------------------------------------------------
 */
static Tcl_HashTable*
ItkGetObjsWithArchInfo(interp)
    Tcl_Interp *interp;  /* interpreter handling this registration */
{
    Tcl_HashTable* objTable;

    /*
     *  If the registration table does not yet exist, then create it.
     */
    objTable = (Tcl_HashTable*)Tcl_GetAssocData(interp,
        "itk_objsWithArchInfo", (Tcl_InterpDeleteProc**)NULL);

    if (!objTable) {
        objTable = (Tcl_HashTable*)ckalloc(sizeof(Tcl_HashTable));
        Tcl_InitHashTable(objTable, TCL_ONE_WORD_KEYS);
        Tcl_SetAssocData(interp, "itk_objsWithArchInfo",
            ItkFreeObjsWithArchInfo, (ClientData)objTable);
    }
    return objTable;
}

/*
 * ------------------------------------------------------------------------
 *  ItkFreeObjsWithArchInfo()
 *
 *  When an interpreter is deleted, this procedure is called to
 *  free up the associated data created by ItkGetObjsWithArchInfo.
 * ------------------------------------------------------------------------
 */
static void
ItkFreeObjsWithArchInfo(clientData, interp)
    ClientData clientData;       /* associated data */
    Tcl_Interp *interp;          /* interpreter being freed */
{
    Tcl_HashTable *tablePtr = (Tcl_HashTable*)clientData;
    Tcl_HashSearch place;
    Tcl_HashEntry *entry;

    entry = Tcl_FirstHashEntry(tablePtr, &place);
    while (entry) {
        Itk_DelArchInfo( Tcl_GetHashValue(entry) );
        entry = Tcl_NextHashEntry(&place);
    }

    Tcl_DeleteHashTable(tablePtr);
    ckfree((char*)tablePtr);
}
