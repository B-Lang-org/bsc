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
 *  This part handles ensembles, which support compound commands in Tcl.
 *  The usual "info" command is an ensemble with parts like "info body"
 *  and "info globals".  Extension developers can extend commands like
 *  "info" by adding their own parts to the ensemble.
 *
 * ========================================================================
 *  AUTHOR:  Michael J. McLennan
 *           Bell Labs Innovations for Lucent Technologies
 *           mmclennan@lucent.com
 *           http://www.tcltk.com/itcl
 *
 *     RCS:  $Id: itcl_ensemble.c,v 1.12 2007/05/24 22:12:55 hobbs Exp $
 * ========================================================================
 *           Copyright (c) 1993-1998  Lucent Technologies, Inc.
 * ------------------------------------------------------------------------
 * See the file "license.terms" for information on usage and redistribution
 * of this file, and for a DISCLAIMER OF ALL WARRANTIES.
 */
#include "itclInt.h"

/*
 *  Data used to represent an ensemble:
 */
struct Ensemble;
typedef struct EnsemblePart {
    char *name;                 /* name of this part */
    int minChars;               /* chars needed to uniquely identify part */
    Command *cmdPtr;            /* command handling this part */
    char *usage;                /* usage string describing syntax */
    struct Ensemble* ensemble;  /* ensemble containing this part */
} EnsemblePart;

/*
 *  Data used to represent an ensemble:
 */
typedef struct Ensemble {
    Tcl_Interp *interp;         /* interpreter containing this ensemble */
    EnsemblePart **parts;       /* list of parts in this ensemble */
    int numParts;               /* number of parts in part list */
    int maxParts;               /* current size of parts list */
    Tcl_Command cmd;            /* command representing this ensemble */
    EnsemblePart* parent;       /* parent part for sub-ensembles
                                 * NULL => toplevel ensemble */
} Ensemble;

/*
 *  Data shared by ensemble access commands and ensemble parser:
 */
typedef struct EnsembleParser {
    Tcl_Interp* master;           /* master interp containing ensembles */
    Tcl_Interp* parser;           /* slave interp for parsing */
    Ensemble* ensData;            /* add parts to this ensemble */
} EnsembleParser;

/*
 *  Declarations for local procedures to this file:
 */
static void FreeEnsInvocInternalRep _ANSI_ARGS_((Tcl_Obj *objPtr));
static void DupEnsInvocInternalRep _ANSI_ARGS_((Tcl_Obj *objPtr,
    Tcl_Obj *copyPtr));
static void UpdateStringOfEnsInvoc _ANSI_ARGS_((Tcl_Obj *objPtr));
static int SetEnsInvocFromAny _ANSI_ARGS_((Tcl_Interp *interp,
    Tcl_Obj *objPtr));

/*
 *  This structure defines a Tcl object type that takes the
 *  place of a part name during ensemble invocations.  When an
 *  error occurs and the caller tries to print objv[0], it will
 *  get a string that contains a complete path to the ensemble
 *  part.
 */
Tcl_ObjType itclEnsInvocType = {
    "ensembleInvoc",                    /* name */
    FreeEnsInvocInternalRep,            /* freeIntRepProc */
    DupEnsInvocInternalRep,             /* dupIntRepProc */
    UpdateStringOfEnsInvoc,             /* updateStringProc */
    SetEnsInvocFromAny                  /* setFromAnyProc */
};


/*
 *  Forward declarations for the procedures used in this file.
 */
static void GetEnsembleUsage _ANSI_ARGS_((Ensemble *ensData,
    Tcl_Obj *objPtr));

static void GetEnsemblePartUsage _ANSI_ARGS_((EnsemblePart *ensPart,
    Tcl_Obj *objPtr));

static int CreateEnsemble _ANSI_ARGS_((Tcl_Interp *interp,
    Ensemble *parentEnsData, char *ensName));

static int AddEnsemblePart _ANSI_ARGS_((Tcl_Interp *interp,
    Ensemble* ensData, CONST char* partName, CONST char* usageInfo,
    Tcl_ObjCmdProc *objProc, ClientData clientData,
    Tcl_CmdDeleteProc *deleteProc, EnsemblePart **rVal));

static void DeleteEnsemble _ANSI_ARGS_((ClientData clientData));

static int FindEnsemble _ANSI_ARGS_((Tcl_Interp *interp, char **nameArgv,
    int nameArgc, Ensemble** ensDataPtr));

static int CreateEnsemblePart _ANSI_ARGS_((Tcl_Interp *interp,
    Ensemble *ensData, CONST char* partName, EnsemblePart **ensPartPtr));

static void DeleteEnsemblePart _ANSI_ARGS_((EnsemblePart *ensPart));

static int FindEnsemblePart _ANSI_ARGS_((Tcl_Interp *interp,
    Ensemble *ensData, CONST char* partName, EnsemblePart **rensPart));

static int FindEnsemblePartIndex _ANSI_ARGS_((Ensemble *ensData,
    CONST char *partName, int *posPtr));

static void ComputeMinChars _ANSI_ARGS_((Ensemble *ensData, int pos));

static int HandleEnsemble _ANSI_ARGS_((ClientData clientData,
    Tcl_Interp *interp, int objc, Tcl_Obj *CONST objv[]));

static EnsembleParser* GetEnsembleParser _ANSI_ARGS_((Tcl_Interp *interp));

static void DeleteEnsParser _ANSI_ARGS_((ClientData clientData,
    Tcl_Interp* interp));



/*
 *----------------------------------------------------------------------
 *
 * Itcl_EnsembleInit --
 *
 *      Called when any interpreter is created to make sure that
 *      things are properly set up for ensembles.
 *
 * Results:
 *      Returns TCL_OK if successful, and TCL_ERROR if anything goes
 *      wrong.
 *
 * Side effects:
 *      On the first call, the "ensemble" object type is registered
 *      with the Tcl compiler.  If an error is encountered, an error
 *      is left as the result in the interpreter.
 *
 *----------------------------------------------------------------------
 */
	/* ARGSUSED */
int
Itcl_EnsembleInit(interp)
    Tcl_Interp *interp;         /* interpreter being initialized */
{
    if (Tcl_GetObjType(itclEnsInvocType.name) == NULL) {
        Tcl_RegisterObjType(&itclEnsInvocType);
    }

    Tcl_CreateObjCommand(interp, "::itcl::ensemble",
        Itcl_EnsembleCmd, (ClientData)NULL, (Tcl_CmdDeleteProc*)NULL);

    return TCL_OK;
}


/*
 *----------------------------------------------------------------------
 *
 * Itcl_CreateEnsemble --
 *
 *      Creates an ensemble command, or adds a sub-ensemble to an
 *      existing ensemble command.  The ensemble name is a space-
 *      separated list.  The first word in the list is the command
 *      name for the top-level ensemble.  Other names do not have
 *      commands associated with them; they are merely sub-ensembles
 *      within the ensemble.  So a name like "a::b::foo bar baz"
 *      represents an ensemble command called "foo" in the namespace
 *      "a::b" that has a sub-ensemble "bar", that has a sub-ensemble
 *      "baz".
 *
 *      If the name is a single word, then this procedure creates
 *      a top-level ensemble and installs an access command for it.
 *      If a command already exists with that name, it is deleted.
 *
 *      If the name has more than one word, then the leading words
 *      are treated as a path name for an existing ensemble.  The
 *      last word is treated as the name for a new sub-ensemble.
 *      If an part already exists with that name, it is an error.
 *
 * Results:
 *      Returns TCL_OK if successful, and TCL_ERROR if anything goes
 *      wrong.
 *
 * Side effects:
 *      If an error is encountered, an error is left as the result
 *      in the interpreter.
 *
 *----------------------------------------------------------------------
 */
int
Itcl_CreateEnsemble(interp, ensName)
    Tcl_Interp *interp;            /* interpreter to be updated */
    CONST char* ensName;           /* name of the new ensemble */
{
    char **nameArgv = NULL;
    int nameArgc;
    Ensemble *parentEnsData;
    Tcl_DString buffer;

    /*
     *  Split the ensemble name into its path components.
     */
    if (Tcl_SplitList(interp, (CONST84 char *)ensName, &nameArgc,
	    &nameArgv) != TCL_OK) {
        goto ensCreateFail;
    }
    if (nameArgc < 1) {
        Tcl_AppendResult(interp,
            "invalid ensemble name \"", ensName, "\"",
            (char*)NULL);
        goto ensCreateFail;
    }

    /*
     *  If there is more than one path component, then follow
     *  the path down to the last component, to find the containing
     *  ensemble.
     */
    parentEnsData = NULL;
    if (nameArgc > 1) {
        if (FindEnsemble(interp, nameArgv, nameArgc-1, &parentEnsData)
            != TCL_OK) {
            goto ensCreateFail;
        }

        if (parentEnsData == NULL) {
            char *pname = Tcl_Merge(nameArgc-1, nameArgv);
            Tcl_AppendResult(interp,
                "invalid ensemble name \"", pname, "\"",
                (char*)NULL);
            ckfree(pname);
            goto ensCreateFail;
        }
    }

    /*
     *  Create the ensemble.
     */
    if (CreateEnsemble(interp, parentEnsData, nameArgv[nameArgc-1])
        != TCL_OK) {
        goto ensCreateFail;
    }

    ckfree((char*)nameArgv);
    return TCL_OK;

ensCreateFail:
    if (nameArgv) {
        ckfree((char*)nameArgv);
    }
    Tcl_DStringInit(&buffer);
    Tcl_DStringAppend(&buffer, "\n    (while creating ensemble \"", -1);
    Tcl_DStringAppend(&buffer, ensName, -1);
    Tcl_DStringAppend(&buffer, "\")", -1);
    Tcl_AddObjErrorInfo(interp, Tcl_DStringValue(&buffer), -1);
    Tcl_DStringFree(&buffer);

    return TCL_ERROR;
}


/*
 *----------------------------------------------------------------------
 *
 * Itcl_AddEnsemblePart --
 *
 *      Adds a part to an ensemble which has been created by
 *      Itcl_CreateEnsemble.  Ensembles are addressed by name, as
 *      described in Itcl_CreateEnsemble.
 *
 *      If the ensemble already has a part with the specified name,
 *      this procedure returns an error.  Otherwise, it adds a new
 *      part to the ensemble.
 *
 *      Any client data specified is automatically passed to the
 *      handling procedure whenever the part is invoked.  It is
 *      automatically destroyed by the deleteProc when the part is
 *      deleted.
 *
 * Results:
 *      Returns TCL_OK if successful, and TCL_ERROR if anything goes
 *      wrong.
 *
 * Side effects:
 *      If an error is encountered, an error is left as the result
 *      in the interpreter.
 *
 *----------------------------------------------------------------------
 */
int
Itcl_AddEnsemblePart(interp, ensName, partName, usageInfo,
    objProc, clientData, deleteProc)

    Tcl_Interp *interp;            /* interpreter to be updated */
    CONST char* ensName;           /* ensemble containing this part */
    CONST char* partName;          /* name of the new part */
    CONST char* usageInfo;         /* usage info for argument list */
    Tcl_ObjCmdProc *objProc;       /* handling procedure for part */
    ClientData clientData;         /* client data associated with part */
    Tcl_CmdDeleteProc *deleteProc; /* procedure used to destroy client data */
{
    char **nameArgv = NULL;
    int nameArgc;
    Ensemble *ensData;
    EnsemblePart *ensPart;
    Tcl_DString buffer;

    /*
     *  Parse the ensemble name and look for a containing ensemble.
     */
    if (Tcl_SplitList(interp, (CONST84 char *)ensName, &nameArgc,
	    &nameArgv) != TCL_OK) {
        goto ensPartFail;
    }
    if (FindEnsemble(interp, nameArgv, nameArgc, &ensData) != TCL_OK) {
        goto ensPartFail;
    }

    if (ensData == NULL) {
        char *pname = Tcl_Merge(nameArgc, nameArgv);
        Tcl_AppendResult(interp,
            "invalid ensemble name \"", pname, "\"",
            (char*)NULL);
        ckfree(pname);
        goto ensPartFail;
    }

    /*
     *  Install the new part into the part list.
     */
    if (AddEnsemblePart(interp, ensData, partName, usageInfo,
        objProc, clientData, deleteProc, &ensPart) != TCL_OK) {
        goto ensPartFail;
    }

    ckfree((char*)nameArgv);
    return TCL_OK;

ensPartFail:
    if (nameArgv) {
        ckfree((char*)nameArgv);
    }
    Tcl_DStringInit(&buffer);
    Tcl_DStringAppend(&buffer, "\n    (while adding to ensemble \"", -1);
    Tcl_DStringAppend(&buffer, ensName, -1);
    Tcl_DStringAppend(&buffer, "\")", -1);
    Tcl_AddObjErrorInfo(interp, Tcl_DStringValue(&buffer), -1);
    Tcl_DStringFree(&buffer);

    return TCL_ERROR;
}


/*
 *----------------------------------------------------------------------
 *
 * Itcl_GetEnsemblePart --
 *
 *      Looks for a part within an ensemble, and returns information
 *      about it.
 *
 * Results:
 *      If the ensemble and its part are found, this procedure
 *      loads information about the part into the "infoPtr" structure
 *      and returns 1.  Otherwise, it returns 0.
 *
 * Side effects:
 *      None.
 *
 *----------------------------------------------------------------------
 */
int
Itcl_GetEnsemblePart(interp, ensName, partName, infoPtr)
    Tcl_Interp *interp;            /* interpreter to be updated */
    CONST char *ensName;           /* ensemble containing the part */
    CONST char *partName;          /* name of the desired part */
    Tcl_CmdInfo *infoPtr;          /* returns: info associated with part */
{
    char **nameArgv = NULL;
    int nameArgc;
    Ensemble *ensData;
    EnsemblePart *ensPart;
    Command *cmdPtr;
    Itcl_InterpState state;

    /*
     *  Parse the ensemble name and look for a containing ensemble.
     *  Save the interpreter state before we do this.  If we get any
     *  errors, we don't want them to affect the interpreter.
     */
    state = Itcl_SaveInterpState(interp, TCL_OK);

    if (Tcl_SplitList(interp, (CONST84 char *)ensName, &nameArgc,
	    &nameArgv) != TCL_OK) {
        goto ensGetFail;
    }
    if (FindEnsemble(interp, nameArgv, nameArgc, &ensData) != TCL_OK) {
        goto ensGetFail;
    }
    if (ensData == NULL) {
        goto ensGetFail;
    }

    /*
     *  Look for a part with the desired name.  If found, load
     *  its data into the "infoPtr" structure.
     */
    if (FindEnsemblePart(interp, ensData, partName, &ensPart)
        != TCL_OK || ensPart == NULL) {
        goto ensGetFail;
    }

    cmdPtr = ensPart->cmdPtr;
    infoPtr->isNativeObjectProc = (cmdPtr->objProc != TclInvokeStringCommand);
    infoPtr->objProc = cmdPtr->objProc;
    infoPtr->objClientData = cmdPtr->objClientData;
    infoPtr->proc = cmdPtr->proc;
    infoPtr->clientData = cmdPtr->clientData;
    infoPtr->deleteProc = cmdPtr->deleteProc;
    infoPtr->deleteData = cmdPtr->deleteData;
    infoPtr->namespacePtr = (Tcl_Namespace*)cmdPtr->nsPtr;

    Itcl_DiscardInterpState(state);
    return 1;

ensGetFail:
    Itcl_RestoreInterpState(interp, state);
    return 0;
}


/*
 *----------------------------------------------------------------------
 *
 * Itcl_IsEnsemble --
 *
 *      Determines whether or not an existing command is an ensemble.
 *
 * Results:
 *      Returns non-zero if the command is an ensemble, and zero
 *      otherwise.
 *
 * Side effects:
 *      None.
 *
 *----------------------------------------------------------------------
 */
int
Itcl_IsEnsemble(infoPtr)
    Tcl_CmdInfo* infoPtr;  /* command info from Tcl_GetCommandInfo() */
{
    if (infoPtr) {
        return (infoPtr->deleteProc == DeleteEnsemble);
    }
    return 0;
}


/*
 *----------------------------------------------------------------------
 *
 * Itcl_GetEnsembleUsage --
 *
 *      Returns a summary of all of the parts of an ensemble and
 *      the meaning of their arguments.  Each part is listed on
 *      a separate line.  Having this summary is sometimes useful
 *      when building error messages for the "@error" handler in
 *      an ensemble.
 *
 *      Ensembles are accessed by name, as described in
 *      Itcl_CreateEnsemble.
 *
 * Results:
 *      If the ensemble is found, its usage information is appended
 *      onto the object "objPtr", and this procedure returns
 *      non-zero.  It is the responsibility of the caller to
 *      initialize and free the object.  If anything goes wrong,
 *      this procedure returns 0.
 *
 * Side effects:
 *      Object passed in is modified.
 *
 *----------------------------------------------------------------------
 */
int
Itcl_GetEnsembleUsage(interp, ensName, objPtr)
    Tcl_Interp *interp;    /* interpreter containing the ensemble */
    CONST char *ensName;         /* name of the ensemble */
    Tcl_Obj *objPtr;       /* returns: summary of usage info */
{
    char **nameArgv = NULL;
    int nameArgc;
    Ensemble *ensData;
    Itcl_InterpState state;

    /*
     *  Parse the ensemble name and look for the ensemble.
     *  Save the interpreter state before we do this.  If we get
     *  any errors, we don't want them to affect the interpreter.
     */
    state = Itcl_SaveInterpState(interp, TCL_OK);

    if (Tcl_SplitList(interp, (CONST84 char *)ensName, &nameArgc,
	    &nameArgv) != TCL_OK) {
        goto ensUsageFail;
    }
    if (FindEnsemble(interp, nameArgv, nameArgc, &ensData) != TCL_OK) {
        goto ensUsageFail;
    }
    if (ensData == NULL) {
        goto ensUsageFail;
    }

    /*
     *  Add a summary of usage information to the return buffer.
     */
    GetEnsembleUsage(ensData, objPtr);

    Itcl_DiscardInterpState(state);
    return 1;

ensUsageFail:
    Itcl_RestoreInterpState(interp, state);
    return 0;
}


/*
 *----------------------------------------------------------------------
 *
 * Itcl_GetEnsembleUsageForObj --
 *
 *      Returns a summary of all of the parts of an ensemble and
 *      the meaning of their arguments.  This procedure is just
 *      like Itcl_GetEnsembleUsage, but it determines the desired
 *      ensemble from a command line argument.  The argument should
 *      be the first argument on the command line--the ensemble
 *      command or one of its parts.
 *
 * Results:
 *      If the ensemble is found, its usage information is appended
 *      onto the object "objPtr", and this procedure returns
 *      non-zero.  It is the responsibility of the caller to
 *      initialize and free the object.  If anything goes wrong,
 *      this procedure returns 0.
 *
 * Side effects:
 *      Object passed in is modified.
 *
 *----------------------------------------------------------------------
 */
int
Itcl_GetEnsembleUsageForObj(interp, ensObjPtr, objPtr)
    Tcl_Interp *interp;    /* interpreter containing the ensemble */
    Tcl_Obj *ensObjPtr;    /* argument representing ensemble */
    Tcl_Obj *objPtr;       /* returns: summary of usage info */
{
    Ensemble *ensData;
    Tcl_Obj *chainObj;
    Tcl_Command cmd;
    Command *cmdPtr;

    /*
     *  If the argument is an ensemble part, then follow the chain
     *  back to the command word for the entire ensemble.
     */
    chainObj = ensObjPtr;
    while (chainObj && chainObj->typePtr == &itclEnsInvocType) {
         chainObj = (Tcl_Obj*)chainObj->internalRep.twoPtrValue.ptr2;
    }

    if (chainObj) {
        cmd = Tcl_GetCommandFromObj(interp, chainObj);
        cmdPtr = (Command*)cmd;
        if (cmdPtr->deleteProc == DeleteEnsemble) {
            ensData = (Ensemble*)cmdPtr->objClientData;
            GetEnsembleUsage(ensData, objPtr);
            return 1;
        }
    }
    return 0;
}


/*
 *----------------------------------------------------------------------
 *
 * GetEnsembleUsage --
 *
 *      
 *      Returns a summary of all of the parts of an ensemble and
 *      the meaning of their arguments.  Each part is listed on
 *      a separate line.  This procedure is used internally to
 *      generate usage information for error messages.
 *
 * Results:
 *      Appends usage information onto the object in "objPtr".
 *
 * Side effects:
 *      None.
 *
 *----------------------------------------------------------------------
 */
static void
GetEnsembleUsage(ensData, objPtr)
    Ensemble *ensData;     /* ensemble data */
    Tcl_Obj *objPtr;       /* returns: summary of usage info */
{
    char *spaces = "  ";
    int isOpenEnded = 0;

    int i;
    EnsemblePart *ensPart;

    for (i=0; i < ensData->numParts; i++) {
        ensPart = ensData->parts[i];

        if (*ensPart->name == '@' && strcmp(ensPart->name,"@error") == 0) {
            isOpenEnded = 1;
        }
        else {
            Tcl_AppendToObj(objPtr, spaces, -1);
            GetEnsemblePartUsage(ensPart, objPtr);
            spaces = "\n  ";
        }
    }
    if (isOpenEnded) {
        Tcl_AppendToObj(objPtr,
            "\n...and others described on the man page", -1);
    }
}


/*
 *----------------------------------------------------------------------
 *
 * GetEnsemblePartUsage --
 *
 *      Determines the usage for a single part within an ensemble,
 *      and appends a summary onto a dynamic string.  The usage
 *      is a combination of the part name and the argument summary.
 *      It is the caller's responsibility to initialize and free
 *      the dynamic string.
 *
 * Results:
 *      Returns usage information in the object "objPtr".
 *
 * Side effects:
 *      None.
 *
 *----------------------------------------------------------------------
 */
static void
GetEnsemblePartUsage(ensPart, objPtr)
    EnsemblePart *ensPart;   /* ensemble part for usage info */
    Tcl_Obj *objPtr;         /* returns: usage information */
{
    EnsemblePart *part;
    Command *cmdPtr;
    char *name;
    Itcl_List trail;
    Itcl_ListElem *elem;
    Tcl_DString buffer;

    /*
     *  Build the trail of ensemble names leading to this part.
     */
    Tcl_DStringInit(&buffer);
    Itcl_InitList(&trail);
    for (part=ensPart; part; part=part->ensemble->parent) {
        Itcl_InsertList(&trail, (ClientData)part);
    }

    cmdPtr = (Command*)ensPart->ensemble->cmd;
    name = Tcl_GetHashKey(cmdPtr->hPtr->tablePtr, cmdPtr->hPtr);
    Tcl_DStringAppendElement(&buffer, name);

    for (elem=Itcl_FirstListElem(&trail); elem; elem=Itcl_NextListElem(elem)) {
        part = (EnsemblePart*)Itcl_GetListValue(elem);
        Tcl_DStringAppendElement(&buffer, part->name);
    }
    Itcl_DeleteList(&trail);

    /*
     *  If the part has usage info, use it directly.
     */
    if (ensPart->usage && *ensPart->usage != '\0') {
        Tcl_DStringAppend(&buffer, " ", 1);
        Tcl_DStringAppend(&buffer, ensPart->usage, -1);
    }

    /*
     *  If the part is itself an ensemble, summarize its usage.
     */
    else if (ensPart->cmdPtr &&
             ensPart->cmdPtr->deleteProc == DeleteEnsemble) {
        Tcl_DStringAppend(&buffer, " option ?arg arg ...?", 21);
    }

    Tcl_AppendToObj(objPtr, Tcl_DStringValue(&buffer),
        Tcl_DStringLength(&buffer));

    Tcl_DStringFree(&buffer);
}


/*
 *----------------------------------------------------------------------
 *
 * CreateEnsemble --
 *
 *      Creates an ensemble command, or adds a sub-ensemble to an
 *      existing ensemble command.  Works like Itcl_CreateEnsemble,
 *      except that the ensemble name is a single name, not a path.
 *      If a parent ensemble is specified, then a new ensemble is
 *      added to that parent.  If a part already exists with the
 *      same name, it is an error.  If a parent ensemble is not
 *      specified, then a top-level ensemble is created.  If a
 *      command already exists with the same name, it is deleted.
 *
 * Results:
 *      Returns TCL_OK if successful, and TCL_ERROR if anything goes
 *      wrong.
 *
 * Side effects:
 *      If an error is encountered, an error is left as the result
 *      in the interpreter.
 *
 *----------------------------------------------------------------------
 */
static int
CreateEnsemble(interp, parentEnsData, ensName)
    Tcl_Interp *interp;            /* interpreter to be updated */
    Ensemble *parentEnsData;       /* parent ensemble or NULL */
    char *ensName;                 /* name of the new ensemble */
{
    Ensemble *ensData;
    EnsemblePart *ensPart;
    Command *cmdPtr;
    Tcl_CmdInfo cmdInfo;

    /*
     *  Create the data associated with the ensemble.
     */
    ensData = (Ensemble*)ckalloc(sizeof(Ensemble));
    ensData->interp = interp;
    ensData->numParts = 0;
    ensData->maxParts = 10;
    ensData->parts = (EnsemblePart**)ckalloc(
        (unsigned)(ensData->maxParts*sizeof(EnsemblePart*))
    );
    ensData->cmd = NULL;
    ensData->parent = NULL;

    /*
     *  If there is no parent data, then this is a top-level
     *  ensemble.  Create the ensemble by installing its access
     *  command.
     *
     *  BE CAREFUL:  Set the string-based proc to the wrapper
     *    procedure TclInvokeObjectCommand.  Otherwise, the
     *    ensemble command may fail.  For example, it will fail
     *    when invoked as a hidden command.
     */
    if (parentEnsData == NULL) {
        ensData->cmd = Tcl_CreateObjCommand(interp, ensName,
            HandleEnsemble, (ClientData)ensData, DeleteEnsemble);

        if (Tcl_GetCommandInfo(interp, ensName, &cmdInfo)) {
            cmdInfo.proc = TclInvokeObjectCommand;
            Tcl_SetCommandInfo(interp, ensName, &cmdInfo);
        }
        return TCL_OK;
    }

    /*
     *  Otherwise, this ensemble is contained within another parent.
     *  Install the new ensemble as a part within its parent.
     */
    if (CreateEnsemblePart(interp, parentEnsData, ensName, &ensPart)
        != TCL_OK) {
        DeleteEnsemble((ClientData)ensData);
        return TCL_ERROR;
    }

    ensData->cmd		= parentEnsData->cmd;
    ensData->parent		= ensPart;

    /*
     * Initialize non-NULL data only.  This allows us to handle the
     * structure differences between versions better.
     */
    cmdPtr			= (Command *) ckalloc(sizeof(Command));
    memset((VOID *) cmdPtr, 0, sizeof(Command));
    cmdPtr->nsPtr		= ((Command *) ensData->cmd)->nsPtr;
    cmdPtr->objProc		= HandleEnsemble;
    cmdPtr->objClientData	= (ClientData)ensData;
    cmdPtr->deleteProc		= DeleteEnsemble;
    cmdPtr->deleteData		= cmdPtr->objClientData;

    ensPart->cmdPtr		= cmdPtr;

    return TCL_OK;
}


/*
 *----------------------------------------------------------------------
 *
 * AddEnsemblePart --
 *
 *      Adds a part to an existing ensemble.  Works like
 *      Itcl_AddEnsemblePart, but the part name is a single word,
 *      not a path.
 *
 *      If the ensemble already has a part with the specified name,
 *      this procedure returns an error.  Otherwise, it adds a new
 *      part to the ensemble.
 *
 *      Any client data specified is automatically passed to the
 *      handling procedure whenever the part is invoked.  It is
 *      automatically destroyed by the deleteProc when the part is
 *      deleted.
 *
 * Results:
 *      Returns TCL_OK if successful, along with a pointer to the
 *      new part.  Returns TCL_ERROR if anything goes wrong.
 *
 * Side effects:
 *      If an error is encountered, an error is left as the result
 *      in the interpreter.
 *
 *----------------------------------------------------------------------
 */
static int
AddEnsemblePart(interp, ensData, partName, usageInfo,
    objProc, clientData, deleteProc, rVal)

    Tcl_Interp *interp;            /* interpreter to be updated */
    Ensemble* ensData;             /* ensemble that will contain this part */
    CONST char* partName;          /* name of the new part */
    CONST char* usageInfo;         /* usage info for argument list */
    Tcl_ObjCmdProc *objProc;       /* handling procedure for part */
    ClientData clientData;         /* client data associated with part */
    Tcl_CmdDeleteProc *deleteProc; /* procedure used to destroy client data */
    EnsemblePart **rVal;           /* returns: new ensemble part */
{
    EnsemblePart *ensPart;
    Command *cmdPtr;

    /*
     *  Install the new part into the part list.
     */
    if (CreateEnsemblePart(interp, ensData, partName, &ensPart) != TCL_OK) {
        return TCL_ERROR;
    }

    if (usageInfo) {
        ensPart->usage = ckalloc((unsigned)(strlen(usageInfo)+1));
        strcpy(ensPart->usage, usageInfo);
    }

    /*
     * Initialize non-NULL data only.  This allows us to handle the
     * structure differences between versions better.
     */
    cmdPtr			= (Command *) ckalloc(sizeof(Command));
    memset((VOID *) cmdPtr, 0, sizeof(Command));
    cmdPtr->nsPtr		= ((Command *) ensData->cmd)->nsPtr;
    cmdPtr->objProc		= objProc;
    cmdPtr->objClientData	= (ClientData)clientData;
    cmdPtr->deleteProc		= deleteProc;
    cmdPtr->deleteData		= (ClientData)clientData;

    ensPart->cmdPtr		= cmdPtr;
    *rVal			= ensPart;

    return TCL_OK;
}


/*
 *----------------------------------------------------------------------
 *
 * DeleteEnsemble --
 *
 *      Invoked when the command associated with an ensemble is
 *      destroyed, to delete the ensemble.  Destroys all parts
 *      included in the ensemble, and frees all memory associated
 *      with it.
 *
 * Results:
 *      None.
 *
 * Side effects:
 *      None.
 *
 *----------------------------------------------------------------------
 */
static void
DeleteEnsemble(clientData)
    ClientData clientData;    /* ensemble data */
{
    Ensemble* ensData = (Ensemble*)clientData;

    /*
     *  BE CAREFUL:  Each ensemble part removes itself from the list.
     *    So keep deleting the first part until all parts are gone.
     */
    while (ensData->numParts > 0) {
        DeleteEnsemblePart(ensData->parts[0]);
    }
    ckfree((char*)ensData->parts);
    ckfree((char*)ensData);
}


/*
 *----------------------------------------------------------------------
 *
 * FindEnsemble --
 *
 *      Searches for an ensemble command and follows a path to
 *      sub-ensembles.
 *
 * Results:
 *      Returns TCL_OK if the ensemble was found, along with a
 *      pointer to the ensemble data in "ensDataPtr".  Returns
 *      TCL_ERROR if anything goes wrong.
 *
 * Side effects:
 *      If anything goes wrong, this procedure returns an error
 *      message as the result in the interpreter.
 *
 *----------------------------------------------------------------------
 */
static int
FindEnsemble(interp, nameArgv, nameArgc, ensDataPtr)
    Tcl_Interp *interp;            /* interpreter containing the ensemble */
    char **nameArgv;               /* path of names leading to ensemble */
    int nameArgc;                  /* number of strings in nameArgv */
    Ensemble** ensDataPtr;         /* returns: ensemble data */
{
    int i;
    Command* cmdPtr;
    Ensemble *ensData;
    EnsemblePart *ensPart;

    *ensDataPtr = NULL;  /* assume that no data will be found */

    /*
     *  If there are no names in the path, then return an error.
     */
    if (nameArgc < 1) {
        Tcl_AppendToObj(Tcl_GetObjResult(interp),
            "invalid ensemble name \"\"", -1);
        return TCL_ERROR;
    }

    /*
     *  Use the first name to find the command for the top-level
     *  ensemble.
     */
    cmdPtr = (Command*) Tcl_FindCommand(interp, nameArgv[0],
        (Tcl_Namespace*)NULL, TCL_LEAVE_ERR_MSG);

    if (cmdPtr == NULL || cmdPtr->deleteProc != DeleteEnsemble) {
        Tcl_AppendResult(interp,
            "command \"", nameArgv[0], "\" is not an ensemble",
            (char*)NULL);
        return TCL_ERROR;
    }
    ensData = (Ensemble*)cmdPtr->objClientData;

    /*
     *  Follow the trail of sub-ensemble names.
     */
    for (i=1; i < nameArgc; i++) {
        if (FindEnsemblePart(interp, ensData, nameArgv[i], &ensPart)
            != TCL_OK) {
            return TCL_ERROR;
        }
        if (ensPart == NULL) {
            char *pname = Tcl_Merge(i, nameArgv);
            Tcl_AppendResult(interp,
                "invalid ensemble name \"", pname, "\"",
                (char*)NULL);
            ckfree(pname);
            return TCL_ERROR;
        }

        cmdPtr = ensPart->cmdPtr;
        if (cmdPtr == NULL || cmdPtr->deleteProc != DeleteEnsemble) {
            Tcl_AppendResult(interp,
                "part \"", nameArgv[i], "\" is not an ensemble",
                (char*)NULL);
            return TCL_ERROR;
        }
        ensData = (Ensemble*)cmdPtr->objClientData;
    }
    *ensDataPtr = ensData;

    return TCL_OK;
}


/*
 *----------------------------------------------------------------------
 *
 * CreateEnsemblePart --
 *
 *      Creates a new part within an ensemble.
 *
 * Results:
 *      If successful, this procedure returns TCL_OK, along with a
 *      pointer to the new part in "ensPartPtr".  If a part with the
 *      same name already exists, this procedure returns TCL_ERROR.
 *
 * Side effects:
 *      If anything goes wrong, this procedure returns an error
 *      message as the result in the interpreter.
 *
 *----------------------------------------------------------------------
 */
static int
CreateEnsemblePart(interp, ensData, partName, ensPartPtr)
    Tcl_Interp *interp;          /* interpreter containing the ensemble */
    Ensemble *ensData;           /* ensemble being modified */
    CONST char* partName;        /* name of the new part */
    EnsemblePart **ensPartPtr;   /* returns: new ensemble part */
{
    int i, pos, size;
    EnsemblePart** partList;
    EnsemblePart* part;

    /*
     *  If a matching entry was found, then return an error.
     */
    if (FindEnsemblePartIndex(ensData, partName, &pos)) {
        Tcl_AppendResult(interp,
            "part \"", partName, "\" already exists in ensemble",
            (char*)NULL);
        return TCL_ERROR;
    }

    /*
     *  Otherwise, make room for a new entry.  Keep the parts in
     *  lexicographical order, so we can search them quickly
     *  later.
     */
    if (ensData->numParts >= ensData->maxParts) {
        size = ensData->maxParts*sizeof(EnsemblePart*);
        partList = (EnsemblePart**)ckalloc((unsigned)2*size);
        memcpy((VOID*)partList, (VOID*)ensData->parts, (size_t)size);
        ckfree((char*)ensData->parts);

        ensData->parts = partList;
        ensData->maxParts *= 2;
    }

    for (i=ensData->numParts; i > pos; i--) {
        ensData->parts[i] = ensData->parts[i-1];
    }
    ensData->numParts++;

    part = (EnsemblePart*)ckalloc(sizeof(EnsemblePart));
    part->name = (char*)ckalloc((unsigned)(strlen(partName)+1));
    strcpy(part->name, partName);
    part->cmdPtr   = NULL;
    part->usage    = NULL;
    part->ensemble = ensData;

    ensData->parts[pos] = part;

    /*
     *  Compare the new part against the one on either side of
     *  it.  Determine how many letters are needed in each part
     *  to guarantee that an abbreviated form is unique.  Update
     *  the parts on either side as well, since they are influenced
     *  by the new part.
     */
    ComputeMinChars(ensData, pos);
    ComputeMinChars(ensData, pos-1);
    ComputeMinChars(ensData, pos+1);

    *ensPartPtr = part;
    return TCL_OK;
}


/*
 *----------------------------------------------------------------------
 *
 * DeleteEnsemblePart --
 *
 *      Deletes a single part from an ensemble.  The part must have 
 *      been created previously by CreateEnsemblePart.
 *
 *      If the part has a delete proc, then it is called to free the
 *      associated client data.
 *
 * Results:
 *      None.
 *
 * Side effects:
 *      Delete proc is called.
 *
 *----------------------------------------------------------------------
 */
static void
DeleteEnsemblePart(ensPart)
    EnsemblePart *ensPart;     /* part being destroyed */
{
    int i, pos;
    Command *cmdPtr;
    Ensemble *ensData;
    cmdPtr = ensPart->cmdPtr;

    /*
     *  If this part has a delete proc, then call it to free
     *  up the client data.
     */
    if (cmdPtr->deleteData && cmdPtr->deleteProc) {
        (*cmdPtr->deleteProc)(cmdPtr->deleteData);
    }
    ckfree((char*)cmdPtr);

    /*
     *  Find this part within its ensemble, and remove it from
     *  the list of parts.
     */
    if (FindEnsemblePartIndex(ensPart->ensemble, ensPart->name, &pos)) {
        ensData = ensPart->ensemble;
        for (i=pos; i < ensData->numParts-1; i++) {
            ensData->parts[i] = ensData->parts[i+1];
        }
        ensData->numParts--;
    }

    /*
     *  Free the memory associated with the part.
     */
    if (ensPart->usage) {
        ckfree(ensPart->usage);
    }
    ckfree(ensPart->name);
    ckfree((char*)ensPart);
}


/*
 *----------------------------------------------------------------------
 *
 * FindEnsemblePart --
 *
 *      Searches for a part name within an ensemble.  Recognizes
 *      unique abbreviations for part names.
 *
 * Results:
 *      If the part name is not a unique abbreviation, this procedure
 *      returns TCL_ERROR.  Otherwise, it returns TCL_OK.  If the
 *      part can be found, "rensPart" returns a pointer to the part.
 *      Otherwise, it returns NULL.
 *
 * Side effects:
 *      If anything goes wrong, this procedure returns an error
 *      message as the result in the interpreter.
 *
 *----------------------------------------------------------------------
 */
static int
FindEnsemblePart(interp, ensData, partName, rensPart)
    Tcl_Interp *interp;       /* interpreter containing the ensemble */
    Ensemble *ensData;        /* ensemble being searched */
    CONST char* partName;     /* name of the desired part */
    EnsemblePart **rensPart;  /* returns:  pointer to the desired part */
{
    int pos = 0;
    int first, last, nlen;
    int i, cmp;

    *rensPart = NULL;

    /*
     *  Search for the desired part name.
     *  All parts are in lexicographical order, so use a
     *  binary search to find the part quickly.  Match only
     *  as many characters as are included in the specified
     *  part name.
     */
    first = 0;
    last  = ensData->numParts-1;
    nlen  = strlen(partName);

    while (last >= first) {
        pos = (first+last)/2;
        if (*partName == *ensData->parts[pos]->name) {
            cmp = strncmp(partName, ensData->parts[pos]->name, nlen);
            if (cmp == 0) {
                break;    /* found it! */
            }
        }
        else if (*partName < *ensData->parts[pos]->name) {
            cmp = -1;
        }
        else {
            cmp = 1;
        }

        if (cmp > 0) {
            first = pos+1;
        } else {
            last = pos-1;
        }
    }

    /*
     *  If a matching entry could not be found, then quit.
     */
    if (last < first) {
        return TCL_OK;
    }

    /*
     *  If a matching entry was found, there may be some ambiguity
     *  if the user did not specify enough characters.  Find the
     *  top-most match in the list, and see if the part name has
     *  enough characters.  If there are two parts like "foo"
     *  and "food", this allows us to match "foo" exactly.
     */
    if (nlen < ensData->parts[pos]->minChars) {
        while (pos > 0) {
            pos--;
            if (strncmp(partName, ensData->parts[pos]->name, nlen) != 0) {
                pos++;
                break;
            }
        }
    }
    if (nlen < ensData->parts[pos]->minChars) {
        Tcl_Obj *resultPtr = Tcl_NewStringObj((char*)NULL, 0);

        Tcl_AppendStringsToObj(resultPtr,
            "ambiguous option \"", partName, "\": should be one of...",
            (char*)NULL);

        for (i=pos; i < ensData->numParts; i++) {
            if (strncmp(partName, ensData->parts[i]->name, nlen) != 0) {
                break;
            }
            Tcl_AppendToObj(resultPtr, "\n  ", 3); 
            GetEnsemblePartUsage(ensData->parts[i], resultPtr);
        }
        Tcl_SetObjResult(interp, resultPtr);
        return TCL_ERROR;
    }

    /*
     *  Found a match.  Return the desired part.
     */
    *rensPart = ensData->parts[pos];
    return TCL_OK;
}


/*
 *----------------------------------------------------------------------
 *
 * FindEnsemblePartIndex --
 *
 *      Searches for a part name within an ensemble.  The part name
 *      must be an exact match for an existing part name in the
 *      ensemble.  This procedure is useful for managing (i.e.,
 *      creating and deleting) parts in an ensemble.
 *
 * Results:
 *      If an exact match is found, this procedure returns
 *      non-zero, along with the index of the part in posPtr.
 *      Otherwise, it returns zero, along with an index in posPtr
 *      indicating where the part should be.
 *
 * Side effects:
 *      None.
 *
 *----------------------------------------------------------------------
 */
static int
FindEnsemblePartIndex(ensData, partName, posPtr)
    Ensemble *ensData;        /* ensemble being searched */
    CONST char *partName;     /* name of desired part */
    int *posPtr;              /* returns: index for part */
{
    int pos = 0;
    int first, last;
    int cmp;

    /*
     *  Search for the desired part name.
     *  All parts are in lexicographical order, so use a
     *  binary search to find the part quickly.
     */
    first = 0;
    last  = ensData->numParts-1;

    while (last >= first) {
        pos = (first+last)/2;
        if (*partName == *ensData->parts[pos]->name) {
            cmp = strcmp(partName, ensData->parts[pos]->name);
            if (cmp == 0) {
                break;    /* found it! */
            }
        }
        else if (*partName < *ensData->parts[pos]->name) {
            cmp = -1;
        }
        else {
            cmp = 1;
        }

        if (cmp > 0) {
            first = pos+1;
        } else {
            last = pos-1;
        }
    }

    if (last >= first) {
        *posPtr = pos;
        return 1;
    }
    *posPtr = first;
    return 0;
}


/*
 *----------------------------------------------------------------------
 *
 * ComputeMinChars --
 *
 *      Compares part names on an ensemble's part list and
 *      determines the minimum number of characters needed for a
 *      unique abbreviation.  The parts on either side of a
 *      particular part index are compared.  As long as there is
 *      a part on one side or the other, this procedure updates
 *      the parts to have the proper minimum abbreviations.
 *
 * Results:
 *      None.
 *
 * Side effects:
 *      Updates three parts within the ensemble to remember
 *      the minimum abbreviations.
 *
 *----------------------------------------------------------------------
 */
static void
ComputeMinChars(ensData, pos)
    Ensemble *ensData;        /* ensemble being modified */
    int pos;                  /* index of part being updated */
{
    int min, max;
    char *p, *q;

    /*
     *  If the position is invalid, do nothing.
     */
    if (pos < 0 || pos >= ensData->numParts) {
        return;
    }

    /*
     *  Start by assuming that only the first letter is required
     *  to uniquely identify this part.  Then compare the name
     *  against each neighboring part to determine the real minimum.
     */
    ensData->parts[pos]->minChars = 1;

    if (pos-1 >= 0) {
        p = ensData->parts[pos]->name;
        q = ensData->parts[pos-1]->name;
        for (min=1; *p == *q && *p != '\0' && *q != '\0'; min++) {
            p++;
            q++;
        }
        if (min > ensData->parts[pos]->minChars) {
            ensData->parts[pos]->minChars = min;
        }
    }

    if (pos+1 < ensData->numParts) {
        p = ensData->parts[pos]->name;
        q = ensData->parts[pos+1]->name;
        for (min=1; *p == *q && *p != '\0' && *q != '\0'; min++) {
            p++;
            q++;
        }
        if (min > ensData->parts[pos]->minChars) {
            ensData->parts[pos]->minChars = min;
        }
    }

    max = strlen(ensData->parts[pos]->name);
    if (ensData->parts[pos]->minChars > max) {
        ensData->parts[pos]->minChars = max;
    }
}


/*
 *----------------------------------------------------------------------
 *
 * HandleEnsemble --
 *
 *      Invoked by Tcl whenever the user issues an ensemble-style
 *      command.  Handles commands of the form:
 *
 *        <ensembleName> <partName> ?<arg> <arg>...?
 *
 *      Looks for the <partName> within the ensemble, and if it
 *      exists, the procedure transfers control to it.
 *
 * Results:
 *      Returns TCL_OK if successful, and TCL_ERROR if anything
 *      goes wrong.
 *
 * Side effects:
 *      If anything goes wrong, this procedure returns an error
 *      message as the result in the interpreter.
 *
 *----------------------------------------------------------------------
 */
static int
HandleEnsemble(clientData, interp, objc, objv)
    ClientData clientData;   /* ensemble data */
    Tcl_Interp *interp;      /* current interpreter */
    int objc;                /* number of arguments */
    Tcl_Obj *CONST objv[];   /* argument objects */
{
    Ensemble *ensData = (Ensemble*)clientData;

    int i, result;
    Command *cmdPtr;
    EnsemblePart *ensPart;
    char *partName;
    int partNameLen;
    Tcl_Obj *cmdlinePtr, *chainObj;
    int cmdlinec;
    Tcl_Obj **cmdlinev;

    /*
     *  If a part name is not specified, return an error that
     *  summarizes the usage for this ensemble.
     */
    if (objc < 2) {
        Tcl_Obj *resultPtr = Tcl_NewStringObj(
            "wrong # args: should be one of...\n", -1);

        GetEnsembleUsage(ensData, resultPtr);
        Tcl_SetObjResult(interp, resultPtr);
        return TCL_ERROR;
    }

    /*
     *  Lookup the desired part.  If an ambiguous abbrevition is
     *  found, return an error immediately.
     */
    partName = Tcl_GetStringFromObj(objv[1], &partNameLen);
    if (FindEnsemblePart(interp, ensData, partName, &ensPart) != TCL_OK) {
        return TCL_ERROR;
    }

    /*
     *  If the part was not found, then look for an "@error" part
     *  to handle the error.
     */
    if (ensPart == NULL) {
        if (FindEnsemblePart(interp, ensData, "@error", &ensPart) != TCL_OK) {
            return TCL_ERROR;
        }
        if (ensPart != NULL) {
            cmdPtr = (Command*)ensPart->cmdPtr;
            result = (*cmdPtr->objProc)(cmdPtr->objClientData,
                interp, objc, objv);
            return result;
        }
    }
    if (ensPart == NULL) {
        return Itcl_EnsembleErrorCmd((ClientData)ensData,
            interp, objc-1, objv+1);
    }

    /*
     *  Pass control to the part, and return the result.
     */
    chainObj = Tcl_NewObj();
    chainObj->bytes = NULL;
    chainObj->typePtr = &itclEnsInvocType;
    chainObj->internalRep.twoPtrValue.ptr1 = (VOID *) ensPart;
    Tcl_IncrRefCount(objv[1]);
    chainObj->internalRep.twoPtrValue.ptr2 = (VOID *) objv[0];
    Tcl_IncrRefCount(objv[0]);

    cmdlinePtr = Tcl_NewListObj(0, (Tcl_Obj**)NULL);
    Tcl_ListObjAppendElement((Tcl_Interp*)NULL, cmdlinePtr, chainObj);
    for (i=2; i < objc; i++) {
        Tcl_ListObjAppendElement((Tcl_Interp*)NULL, cmdlinePtr, objv[i]);
    }
    Tcl_IncrRefCount(cmdlinePtr);

    result = Tcl_ListObjGetElements((Tcl_Interp*)NULL, cmdlinePtr,
        &cmdlinec, &cmdlinev);

    if (result == TCL_OK) {
        cmdPtr = (Command*)ensPart->cmdPtr;
        result = (*cmdPtr->objProc)(cmdPtr->objClientData, interp,
            cmdlinec, cmdlinev);
    }
    Tcl_DecrRefCount(cmdlinePtr);

    return result;
}


/*
 *----------------------------------------------------------------------
 *
 * Itcl_EnsembleCmd --
 *
 *      Invoked by Tcl whenever the user issues the "ensemble"
 *      command to manipulate an ensemble.  Handles the following
 *      syntax:
 *
 *        ensemble <ensName> ?<command> <arg> <arg>...?
 *        ensemble <ensName> {
 *            part <partName> <args> <body>
 *            ensemble <ensName> {
 *                ...
 *            }
 *        }
 *
 *      Finds or creates the ensemble <ensName>, and then executes
 *      the commands to add parts.
 *
 * Results:
 *      Returns TCL_OK if successful, and TCL_ERROR if anything
 *      goes wrong.
 *
 * Side effects:
 *      If anything goes wrong, this procedure returns an error
 *      message as the result in the interpreter.
 *
 *----------------------------------------------------------------------
 */
int
Itcl_EnsembleCmd(clientData, interp, objc, objv)
    ClientData clientData;   /* ensemble data */
    Tcl_Interp *interp;      /* current interpreter */
    int objc;                /* number of arguments */
    Tcl_Obj *CONST objv[];   /* argument objects */
{
    int status;
    char *ensName;
    EnsembleParser *ensInfo;
    Ensemble *ensData, *savedEnsData;
    EnsemblePart *ensPart;
    Tcl_Command cmd;
    Command *cmdPtr;
    Tcl_Obj *objPtr;

    /*
     *  Make sure that an ensemble name was specified.
     */
    if (objc < 2) {
        Tcl_AppendResult(interp,
            "wrong # args: should be \"",
            Tcl_GetStringFromObj(objv[0], (int*)NULL),
            " name ?command arg arg...?\"",
            (char*)NULL);
        return TCL_ERROR;
    }

    /*
     *  If this is the "ensemble" command in the main interpreter,
     *  then the client data will be null.  Otherwise, it is
     *  the "ensemble" command in the ensemble body parser, and
     *  the client data indicates which ensemble we are modifying.
     */
    if (clientData) {
        ensInfo = (EnsembleParser*)clientData;
    } else {
        ensInfo = GetEnsembleParser(interp);
    }
    ensData = ensInfo->ensData;

    /*
     *  Find or create the desired ensemble.  If an ensemble is
     *  being built, then this "ensemble" command is enclosed in
     *  another "ensemble" command.  Use the current ensemble as
     *  the parent, and find or create an ensemble part within it.
     */
    ensName = Tcl_GetStringFromObj(objv[1], (int*)NULL);

    if (ensData) {
        if (FindEnsemblePart(interp, ensData, ensName, &ensPart) != TCL_OK) {
            ensPart = NULL;
        }
        if (ensPart == NULL) {
            if (CreateEnsemble(interp, ensData, ensName) != TCL_OK) {
                return TCL_ERROR;
            }
            if (FindEnsemblePart(interp, ensData, ensName, &ensPart)
                != TCL_OK) {
                Tcl_Panic("Itcl_EnsembleCmd: can't create ensemble");
            }
        }

        cmdPtr = (Command*)ensPart->cmdPtr;
        if (cmdPtr->deleteProc != DeleteEnsemble) {
            Tcl_AppendResult(interp,
                "part \"", Tcl_GetStringFromObj(objv[1], (int*)NULL),
                "\" is not an ensemble",
                (char*)NULL);
            return TCL_ERROR;
        }
        ensData = (Ensemble*)cmdPtr->objClientData;
    }

    /*
     *  Otherwise, the desired ensemble is a top-level ensemble.
     *  Find or create the access command for the ensemble, and
     *  then get its data.
     */
    else {
        cmd = Tcl_FindCommand(interp, ensName, (Tcl_Namespace*)NULL, 0);
        if (cmd == NULL) {
            if (CreateEnsemble(interp, (Ensemble*)NULL, ensName)
                != TCL_OK) {
                return TCL_ERROR;
            }
            cmd = Tcl_FindCommand(interp, ensName, (Tcl_Namespace*)NULL, 0);
        }
        cmdPtr = (Command*)cmd;

        if (cmdPtr == NULL || cmdPtr->deleteProc != DeleteEnsemble) {
            Tcl_AppendResult(interp,
                "command \"", Tcl_GetStringFromObj(objv[1], (int*)NULL),
                "\" is not an ensemble",
                (char*)NULL);
            return TCL_ERROR;
        }
        ensData = (Ensemble*)cmdPtr->objClientData;
    }

    /*
     *  At this point, we have the data for the ensemble that is
     *  being manipulated.  Plug this into the parser, and then
     *  interpret the rest of the arguments in the ensemble parser. 
     */
    status = TCL_OK;
    savedEnsData = ensInfo->ensData;
    ensInfo->ensData = ensData;

    if (objc == 3) {
        status = Tcl_EvalObj(ensInfo->parser, objv[2]);
    }
    else if (objc > 3) {
        objPtr = Tcl_NewListObj(objc-2, objv+2);
        Tcl_IncrRefCount(objPtr);  /* stop Eval trashing it */
        status = Tcl_EvalObj(ensInfo->parser, objPtr);
        Tcl_DecrRefCount(objPtr);  /* we're done with the object */
    }

    /*
     *  Copy the result from the parser interpreter to the
     *  master interpreter.  If an error was encountered,
     *  copy the error info first, and then set the result.
     *  Otherwise, the offending command is reported twice.
     */
    if (status == TCL_ERROR) {
        CONST char *errInfo = Tcl_GetVar2(ensInfo->parser, "::errorInfo",
            (char*)NULL, TCL_GLOBAL_ONLY);

        if (errInfo) {
            Tcl_AddObjErrorInfo(interp, (CONST84 char *)errInfo, -1);
        }

        if (objc == 3) {
            char msg[128];
            sprintf(msg, "\n    (\"ensemble\" body line %d)",
                ensInfo->parser->errorLine);
            Tcl_AddObjErrorInfo(interp, msg, -1);
        }
    }
    Tcl_SetObjResult(interp, Tcl_GetObjResult(ensInfo->parser));

    ensInfo->ensData = savedEnsData;
    return status;
}


/*
 *----------------------------------------------------------------------
 *
 * GetEnsembleParser --
 *
 *      Returns the slave interpreter that acts as a parser for
 *      the body of an "ensemble" definition.  The first time that
 *      this is called for an interpreter, the parser is created
 *      and registered as associated data.  After that, it is
 *      simply returned.
 *
 * Results:
 *      Returns a pointer to the ensemble parser data structure.
 *
 * Side effects:
 *      On the first call, the ensemble parser is created and
 *      registered as "itcl_ensembleParser" with the interpreter.
 *
 *----------------------------------------------------------------------
 */
static EnsembleParser*
GetEnsembleParser(interp)
    Tcl_Interp *interp;     /* interpreter handling the ensemble */
{
    Namespace *nsPtr;
    Tcl_Namespace *childNs;
    EnsembleParser *ensInfo;
    Tcl_HashEntry *hPtr;
    Tcl_HashSearch search;
    Tcl_Command cmd;

    /*
     *  Look for an existing ensemble parser.  If it is found,
     *  return it immediately.
     */
    ensInfo = (EnsembleParser*) Tcl_GetAssocData(interp,
        "itcl_ensembleParser", NULL);

    if (ensInfo) {
        return ensInfo;
    }

    /*
     *  Create a slave interpreter that can be used to parse
     *  the body of an ensemble definition.
     */
    ensInfo = (EnsembleParser*)ckalloc(sizeof(EnsembleParser));
    ensInfo->master = interp;
    ensInfo->parser = Tcl_CreateInterp();
    ensInfo->ensData = NULL;

    /*
     *  Remove all namespaces and all normal commands from the
     *  parser interpreter.
     */
    nsPtr = (Namespace*)Tcl_GetGlobalNamespace(ensInfo->parser);

    for (hPtr = Tcl_FirstHashEntry(&nsPtr->childTable, &search);
         hPtr != NULL;
         hPtr = Tcl_FirstHashEntry(&nsPtr->childTable, &search)) {

        childNs = (Tcl_Namespace*)Tcl_GetHashValue(hPtr);
        Tcl_DeleteNamespace(childNs);
    }

    for (hPtr = Tcl_FirstHashEntry(&nsPtr->cmdTable, &search);
         hPtr != NULL;
         hPtr = Tcl_FirstHashEntry(&nsPtr->cmdTable, &search)) {

        cmd = (Tcl_Command)Tcl_GetHashValue(hPtr);
        Tcl_DeleteCommandFromToken(ensInfo->parser, cmd);
    }

    /*
     *  Add the allowed commands to the parser interpreter:
     *  part, delete, ensemble
     */
    Tcl_CreateObjCommand(ensInfo->parser, "part", Itcl_EnsPartCmd,
        (ClientData)ensInfo, (Tcl_CmdDeleteProc*)NULL);

    Tcl_CreateObjCommand(ensInfo->parser, "option", Itcl_EnsPartCmd,
        (ClientData)ensInfo, (Tcl_CmdDeleteProc*)NULL);

    Tcl_CreateObjCommand(ensInfo->parser, "ensemble", Itcl_EnsembleCmd,
        (ClientData)ensInfo, (Tcl_CmdDeleteProc*)NULL);

    /*
     *  Install the parser data, so we'll have it the next time
     *  we call this procedure.
     */
    (void) Tcl_SetAssocData(interp, "itcl_ensembleParser",
            DeleteEnsParser, (ClientData)ensInfo);

    return ensInfo;
}


/*
 *----------------------------------------------------------------------
 *
 * DeleteEnsParser --
 *
 *      Called when an interpreter is destroyed to clean up the
 *      ensemble parser within it.  Destroys the slave interpreter
 *      and frees up the data associated with it.
 *
 * Results:
 *      None.
 *
 * Side effects:
 *      None.
 *
 *----------------------------------------------------------------------
 */
	/* ARGSUSED */
static void
DeleteEnsParser(clientData, interp)
    ClientData clientData;    /* client data for ensemble-related commands */
    Tcl_Interp *interp;       /* interpreter containing the data */
{
    EnsembleParser* ensInfo = (EnsembleParser*)clientData;
    Tcl_DeleteInterp(ensInfo->parser);
    ckfree((char*)ensInfo);
}


/*
 *----------------------------------------------------------------------
 *
 * Itcl_EnsPartCmd --
 *
 *      Invoked by Tcl whenever the user issues the "part" command
 *      to manipulate an ensemble.  This command can only be used
 *      inside the "ensemble" command, which handles ensembles.
 *      Handles the following syntax:
 *
 *        ensemble <ensName> {
 *            part <partName> <args> <body>
 *        }
 *
 *      Adds a new part called <partName> to the ensemble.  If a
 *      part already exists with that name, it is an error.  The
 *      new part is handled just like an ordinary Tcl proc, with
 *      a list of <args> and a <body> of code to execute.
 *
 * Results:
 *      Returns TCL_OK if successful, and TCL_ERROR if anything
 *      goes wrong.
 *
 * Side effects:
 *      If anything goes wrong, this procedure returns an error
 *      message as the result in the interpreter.
 *
 *----------------------------------------------------------------------
 */
int
Itcl_EnsPartCmd(clientData, interp, objc, objv)
    ClientData clientData;   /* ensemble data */
    Tcl_Interp *interp;      /* current interpreter */
    int objc;                /* number of arguments */
    Tcl_Obj *CONST objv[];   /* argument objects */
{
    EnsembleParser *ensInfo = (EnsembleParser*)clientData;
    Ensemble *ensData = (Ensemble*)ensInfo->ensData;

    int status, varArgs, space;
    char *partName, *usage;
    Proc *procPtr;
    Command *cmdPtr;
    CompiledLocal *localPtr;
    EnsemblePart *ensPart;
    Tcl_DString buffer;

    if (objc != 4) {
        Tcl_AppendResult(interp,
            "wrong # args: should be \"",
            Tcl_GetStringFromObj(objv[0], (int*)NULL),
            " name args body\"",
            (char*)NULL);
        return TCL_ERROR;
    }

    /*
     *  Create a Tcl-style proc definition using the specified args
     *  and body.  This is not a proc in the usual sense.  It belongs
     *  to the namespace that contains the ensemble, but it is
     *  accessed through the ensemble, not through a Tcl command.
     */
    partName = Tcl_GetStringFromObj(objv[1], (int*)NULL);
    cmdPtr = (Command*)ensData->cmd;

    if (TclCreateProc(interp, cmdPtr->nsPtr, partName, objv[2], objv[3],
        &procPtr) != TCL_OK) {
        return TCL_ERROR;
    }

    /*
     *  Deduce the usage information from the argument list.
     *  We'll register this when we create the part, in a moment.
     */
    Tcl_DStringInit(&buffer);
    varArgs = 0;
    space = 0;

    for (localPtr=procPtr->firstLocalPtr;
         localPtr != NULL;
         localPtr=localPtr->nextPtr) {

        if (TclIsVarArgument(localPtr)) {
            varArgs = 0;
            if (strcmp(localPtr->name, "args") == 0) {
                varArgs = 1;
            }
            else if (localPtr->defValuePtr) {
                if (space) {
                    Tcl_DStringAppend(&buffer, " ", 1);
                }
                Tcl_DStringAppend(&buffer, "?", 1);
                Tcl_DStringAppend(&buffer, localPtr->name, -1);
                Tcl_DStringAppend(&buffer, "?", 1);
                space = 1;
            }
            else {
                if (space) {
                    Tcl_DStringAppend(&buffer, " ", 1);
                }
                Tcl_DStringAppend(&buffer, localPtr->name, -1);
                space = 1;
            }
        }
    }
    if (varArgs) {
        if (space) {
            Tcl_DStringAppend(&buffer, " ", 1);
        }
        Tcl_DStringAppend(&buffer, "?arg arg ...?", 13);
    }

    usage = Tcl_DStringValue(&buffer);

    /*
     *  Create a new part within the ensemble.  If successful,
     *  plug the command token into the proc; we'll need it later
     *  if we try to compile the Tcl code for the part.  If
     *  anything goes wrong, clean up before bailing out.
     */
    status = AddEnsemblePart(interp, ensData, partName, usage,
        TclObjInterpProc, (ClientData)procPtr, TclProcDeleteProc,
        &ensPart);

    if (status == TCL_OK) {
        procPtr->cmdPtr = ensPart->cmdPtr;
    } else {
        TclProcDeleteProc((ClientData)procPtr);
    }
    Tcl_DStringFree(&buffer);

    return status;
}


/*
 *----------------------------------------------------------------------
 *
 * Itcl_EnsembleErrorCmd --
 *
 *      Invoked when the user tries to access an unknown part for
 *      an ensemble.  Acts as the default handler for the "@error"
 *      part.  Generates an error message like:
 *
 *          bad option "foo": should be one of...
 *            info args procname
 *            info body procname
 *            info cmdcount
 *            ...
 *
 * Results:
 *      Always returns TCL_OK.
 *
 * Side effects:
 *      Returns the error message as the result in the interpreter.
 *
 *----------------------------------------------------------------------
 */
	/* ARGSUSED */
int
Itcl_EnsembleErrorCmd(clientData, interp, objc, objv)
    ClientData clientData;   /* ensemble info */
    Tcl_Interp *interp;      /* current interpreter */
    int objc;                /* number of arguments */
    Tcl_Obj *CONST objv[];   /* argument objects */
{
    Ensemble *ensData = (Ensemble*)clientData;

    char *cmdName;
    Tcl_Obj *objPtr;

    cmdName = Tcl_GetStringFromObj(objv[0], (int*)NULL);

    objPtr = Tcl_NewStringObj((char*)NULL, 0);
    Tcl_AppendStringsToObj(objPtr,
        "bad option \"", cmdName, "\": should be one of...\n",
        (char*)NULL);
    GetEnsembleUsage(ensData, objPtr);

    Tcl_SetObjResult(interp, objPtr);
    return TCL_ERROR;
}


/*
 *----------------------------------------------------------------------
 *
 * FreeEnsInvocInternalRep --
 *
 *      Frees the resources associated with an ensembleInvoc object's
 *      internal representation.
 *
 * Results:
 *      None.
 *
 * Side effects:
 *      Decrements the ref count of the two objects referenced by
 *      this object.  If there are no more uses, this will free
 *      the other objects.
 *
 *----------------------------------------------------------------------
 */
static void
FreeEnsInvocInternalRep(objPtr)
    register Tcl_Obj *objPtr;   /* namespName object with internal
                                 * representation to free */
{
    Tcl_Obj *prevArgObj = (Tcl_Obj*)objPtr->internalRep.twoPtrValue.ptr2;

    if (prevArgObj) {
        Tcl_DecrRefCount(prevArgObj);
    }
}


/*
 *----------------------------------------------------------------------
 *
 * DupEnsInvocInternalRep --
 *
 *      Initializes the internal representation of an ensembleInvoc
 *      object to a copy of the internal representation of
 *      another ensembleInvoc object.
 *
 *      This shouldn't be called.  Normally, a temporary ensembleInvoc
 *      object is created while an ensemble call is in progress.
 *      This object may be converted to string form if an error occurs.
 *      It does not stay around long, and there is no reason for it
 *      to be duplicated.
 *
 * Results:
 *      None.
 *
 * Side effects:
 *      copyPtr's internal rep is set to duplicates of the objects
 *      pointed to by srcPtr's internal rep.
 *
 *----------------------------------------------------------------------
 */
static void
DupEnsInvocInternalRep(srcPtr, copyPtr)
    Tcl_Obj *srcPtr;                /* Object with internal rep to copy. */
    register Tcl_Obj *copyPtr;      /* Object with internal rep to set. */
{
    EnsemblePart *ensPart = (EnsemblePart*)srcPtr->internalRep.twoPtrValue.ptr1;
    Tcl_Obj *prevArgObj = (Tcl_Obj*)srcPtr->internalRep.twoPtrValue.ptr2;
    Tcl_Obj *objPtr;

    copyPtr->internalRep.twoPtrValue.ptr1 = (VOID *) ensPart;

    if (prevArgObj) {
        objPtr = Tcl_DuplicateObj(prevArgObj);
        Tcl_IncrRefCount(objPtr);
        copyPtr->internalRep.twoPtrValue.ptr2 = (VOID *) objPtr;
    }
}


/*
 *----------------------------------------------------------------------
 *
 * SetEnsInvocFromAny --
 *
 *      Generates the internal representation for an ensembleInvoc
 *      object.  This conversion really shouldn't take place.
 *      Normally, a temporary ensembleInvoc object is created while
 *      an ensemble call is in progress.  This object may be converted
 *      to string form if an error occurs.  But there is no reason
 *      for any other object to be converted to ensembleInvoc form.
 *
 * Results:
 *      Always returns TCL_OK.
 *
 * Side effects:
 *      The string representation is saved as if it were the
 *      command line argument for the ensemble invocation.  The
 *      reference to the ensemble part is set to NULL.
 *
 *----------------------------------------------------------------------
 */
static int
SetEnsInvocFromAny(interp, objPtr)
    Tcl_Interp *interp;              /* Determines the context for
                                        name resolution */
    register Tcl_Obj *objPtr;        /* The object to convert */
{
    int length;
    char *name;
    Tcl_Obj *argObj;

    /*
     *  Get objPtr's string representation.
     *  Make it up-to-date if necessary.
     *  THIS FAILS IF THE OBJECT'S STRING REP CONTAINS NULLS.
     */
    name = Tcl_GetStringFromObj(objPtr, &length);

    /*
     *  Make an argument object to contain the string, and
     *  set the ensemble part definition to NULL.  At this point,
     *  we don't know anything about an ensemble, so we'll just
     *  keep the string around as if it were the command line
     *  invocation.
     */
    argObj = Tcl_NewStringObj(name, length);

    /*
     *  Free the old representation and install a new one.
     */
    if (objPtr->typePtr && objPtr->typePtr->freeIntRepProc != NULL) {
        (*objPtr->typePtr->freeIntRepProc)(objPtr);
    }
    objPtr->internalRep.twoPtrValue.ptr1 = (VOID *) NULL;
    objPtr->internalRep.twoPtrValue.ptr2 = (VOID *) argObj;
    objPtr->typePtr = &itclEnsInvocType;

    return TCL_OK;
}


/*
 *----------------------------------------------------------------------
 *
 * UpdateStringOfEnsInvoc --
 *
 *      Updates the string representation for an ensembleInvoc object.
 *      This is called when an error occurs in an ensemble part, when
 *      the code tries to print objv[0] as the command name.  This
 *      code automatically chains together all of the names leading
 *      to the ensemble part, so the error message references the
 *      entire command, not just the part name.
 *
 *      Note: This procedure does not free an existing old string rep
 *      so storage will be lost if this has not already been done.
 *
 * Results:
 *      None.
 *
 * Side effects:
 *      The object's string is set to the full command name for
 *      the ensemble part.
 *
 *----------------------------------------------------------------------
 */
static void
UpdateStringOfEnsInvoc(objPtr)
    register Tcl_Obj *objPtr;      /* NamespName obj to update string rep. */
{
    EnsemblePart *ensPart = (EnsemblePart*)objPtr->internalRep.twoPtrValue.ptr1;
    Tcl_Obj *prevArgObj = (Tcl_Obj*)objPtr->internalRep.twoPtrValue.ptr2;

    Tcl_DString buffer;
    int length;
    char *name;

    Tcl_DStringInit(&buffer);

    /*
     *  Get the string representation for the previous argument.
     *  This will force each ensembleInvoc argument up the line
     *  to get its string representation.  So we will get the
     *  original command name, followed by the sub-ensemble, and
     *  the next sub-ensemble, and so on.  Then add the part
     *  name from the ensPart argument.
     */
    if (prevArgObj) {
        name = Tcl_GetStringFromObj(prevArgObj, &length);
        Tcl_DStringAppend(&buffer, name, length);
    }

    if (ensPart) {
        Tcl_DStringAppendElement(&buffer, ensPart->name);
    }

    /*
     *  The following allocates an empty string on the heap if name is ""
     *  (e.g., if the internal rep is NULL).
     */
    name = Tcl_DStringValue(&buffer);
    length = strlen(name);
    objPtr->bytes = (char *) ckalloc((unsigned) (length + 1));
    memcpy((VOID *) objPtr->bytes, (VOID *) name, (unsigned) length);
    objPtr->bytes[length] = '\0';
    objPtr->length = length;
}
