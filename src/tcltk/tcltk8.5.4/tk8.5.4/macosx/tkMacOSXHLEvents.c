/*
 * tkMacOSXHLEvents.c --
 *
 *	Implements high level event support for the Macintosh. Currently, the
 *	only event that really does anything is the Quit event.
 *
 * Copyright (c) 1995-1997 Sun Microsystems, Inc.
 * Copyright 2001, Apple Computer, Inc.
 * Copyright (c) 2006 Daniel A. Steffen <das@users.sourceforge.net>
 *
 * See the file "license.terms" for information on usage and redistribution of
 * this file, and for a DISCLAIMER OF ALL WARRANTIES.
 *
 * RCS: @(#) $Id: tkMacOSXHLEvents.c,v 1.15.2.1 2008/07/22 17:00:49 das Exp $
 */

#include "tkMacOSXPrivate.h"

/*
 * This is a Tcl_Event structure that the Quit AppleEvent handler uses to
 * schedule the ReallyKillMe function.
 */

typedef struct KillEvent {
    Tcl_Event header;		/* Information that is standard for all
				 * events. */
    Tcl_Interp *interp;		/* Interp that was passed to the Quit
				 * AppleEvent */
} KillEvent;

/*
 * Static functions used only in this file.
 */

static OSErr		QuitHandler(const AppleEvent *event,
			    AppleEvent *reply, long handlerRefcon);
static OSErr		OappHandler(const AppleEvent *event,
			    AppleEvent *reply, long handlerRefcon);
static OSErr		RappHandler(const AppleEvent *event,
			    AppleEvent *reply, long handlerRefcon);
static OSErr		OdocHandler(const AppleEvent *event,
			    AppleEvent *reply, long handlerRefcon);
static OSErr		PrintHandler(const AppleEvent *event,
			    AppleEvent *reply, long handlerRefcon);
static OSErr		ScriptHandler(const AppleEvent *event,
			    AppleEvent *reply, long handlerRefcon);
static OSErr		PrefsHandler(const AppleEvent *event,
			    AppleEvent *reply, long handlerRefcon);
static int		MissedAnyParameters(const AppleEvent *theEvent);
static int		ReallyKillMe(Tcl_Event *eventPtr, int flags);
static OSStatus		FSRefToDString(const FSRef *fsref, Tcl_DString *ds);

/*
 *----------------------------------------------------------------------
 *
 * TkMacOSXInitAppleEvents --
 *
 *	Initilize the Apple Events on the Macintosh. This registers the core
 *	event handlers.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */

void
TkMacOSXInitAppleEvents(
    Tcl_Interp *interp)		/* Interp to handle basic events. */
{
    AEEventHandlerUPP OappHandlerUPP, RappHandlerUPP, OdocHandlerUPP;
    AEEventHandlerUPP PrintHandlerUPP, QuitHandlerUPP, ScriptHandlerUPP;
    AEEventHandlerUPP PrefsHandlerUPP;
    static Boolean initialized = FALSE;

    if (!initialized) {
	initialized = TRUE;

	/*
	 * Install event handlers for the core apple events.
	 */

	QuitHandlerUPP = NewAEEventHandlerUPP(QuitHandler);
	ChkErr(AEInstallEventHandler, kCoreEventClass, kAEQuitApplication,
		QuitHandlerUPP, (long) interp, false);

	OappHandlerUPP = NewAEEventHandlerUPP(OappHandler);
	ChkErr(AEInstallEventHandler, kCoreEventClass, kAEOpenApplication,
		OappHandlerUPP, (long) interp, false);

	RappHandlerUPP = NewAEEventHandlerUPP(RappHandler);
	ChkErr(AEInstallEventHandler, kCoreEventClass, kAEReopenApplication,
		RappHandlerUPP, (long) interp, false);

	OdocHandlerUPP = NewAEEventHandlerUPP(OdocHandler);
	ChkErr(AEInstallEventHandler, kCoreEventClass, kAEOpenDocuments,
		OdocHandlerUPP, (long) interp, false);

	PrintHandlerUPP = NewAEEventHandlerUPP(PrintHandler);
	ChkErr(AEInstallEventHandler, kCoreEventClass, kAEPrintDocuments,
		PrintHandlerUPP, (long) interp, false);

	PrefsHandlerUPP = NewAEEventHandlerUPP(PrefsHandler);
	ChkErr(AEInstallEventHandler, kCoreEventClass, kAEShowPreferences,
		PrefsHandlerUPP, (long) interp, false);

	if (interp) {
	    ScriptHandlerUPP = NewAEEventHandlerUPP(ScriptHandler);
	    ChkErr(AEInstallEventHandler, kAEMiscStandards, kAEDoScript,
		    ScriptHandlerUPP, (long) interp, false);
	}
    }
}

/*
 *----------------------------------------------------------------------
 *
 * TkMacOSXDoHLEvent --
 *
 *	Dispatch incomming highlevel events.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	Depends on the incoming event.
 *
 *----------------------------------------------------------------------
 */

int
TkMacOSXDoHLEvent(
    EventRecord *theEvent)
{
    return AEProcessAppleEvent(theEvent);
}

/*
 *----------------------------------------------------------------------
 *
 * QuitHandler --
 *
 *	This is the 'quit' core Apple event handler.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */

static OSErr
QuitHandler(
    const AppleEvent *event,
    AppleEvent *reply,
    long handlerRefcon)
{
    Tcl_Interp *interp = (Tcl_Interp *) handlerRefcon;
    KillEvent *eventPtr;

    if (interp) {
	/*
	 * Call the exit command from the event loop, since you are not
	 * supposed to call ExitToShell in an Apple Event Handler. We put this
	 * at the head of Tcl's event queue because this message usually comes
	 * when the Mac is shutting down, and we want to kill the shell as
	 * quickly as possible.
	 */

	eventPtr = (KillEvent *) ckalloc(sizeof(KillEvent));
	eventPtr->header.proc = ReallyKillMe;
	eventPtr->interp = interp;

	Tcl_QueueEvent((Tcl_Event *) eventPtr, TCL_QUEUE_HEAD);
    }
    return noErr;
}

/*
 *----------------------------------------------------------------------
 *
 * OappHandler --
 *
 *	This is the 'oapp' core Apple event handler.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */

static OSErr
OappHandler(
    const AppleEvent *event,
    AppleEvent *reply,
    long handlerRefcon)
{
    Tcl_CmdInfo dummy;
    Tcl_Interp *interp = (Tcl_Interp *) handlerRefcon;

    if (interp &&
	    Tcl_GetCommandInfo(interp, "::tk::mac::OpenApplication", &dummy)){
	if (Tcl_GlobalEval(interp, "::tk::mac::OpenApplication") != TCL_OK) {
	    Tcl_BackgroundError(interp);
	}
    }
    return noErr;
}

/*
 *----------------------------------------------------------------------
 *
 * RappHandler --
 *
 *	This is the 'rapp' core Apple event handler.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */

static OSErr
RappHandler(
    const AppleEvent *event,
    AppleEvent *reply,
    long handlerRefcon)
{
    Tcl_CmdInfo dummy;
    Tcl_Interp *interp = (Tcl_Interp *) handlerRefcon;
    ProcessSerialNumber thePSN = {0, kCurrentProcess};
    OSStatus err = ChkErr(SetFrontProcess, &thePSN);

    if (interp && Tcl_GetCommandInfo(interp,
	    "::tk::mac::ReopenApplication", &dummy)) {
	if (Tcl_GlobalEval(interp, "::tk::mac::ReopenApplication") != TCL_OK){
	    Tcl_BackgroundError(interp);
	}
    }
    return err;
}

/*
 *----------------------------------------------------------------------
 *
 * PrefsHandler --
 *
 *	This is the 'pref' core Apple event handler. Called when the user
 *	selects 'Preferences...' in MacOS X
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */

static OSErr
PrefsHandler(
    const AppleEvent *event,
    AppleEvent *reply,
    long handlerRefcon)
{
    Tcl_CmdInfo dummy;
    Tcl_Interp *interp = (Tcl_Interp *) handlerRefcon;

    if (interp &&
	    Tcl_GetCommandInfo(interp, "::tk::mac::ShowPreferences", &dummy)){
	if (Tcl_GlobalEval(interp, "::tk::mac::ShowPreferences") != TCL_OK) {
	    Tcl_BackgroundError(interp);
	}
    }
    return noErr;
}

/*
 *----------------------------------------------------------------------
 *
 * OdocHandler --
 *
 *	This is the 'odoc' core Apple event handler.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */

static OSErr
OdocHandler(
    const AppleEvent *event,
    AppleEvent *reply,
    long handlerRefcon)
{
    Tcl_Interp *interp = (Tcl_Interp *) handlerRefcon;
    AEDescList fileSpecList;
    FSRef file;
    DescType type;
    Size actual;
    long count, index;
    AEKeyword keyword;
    Tcl_DString command, pathName;
    Tcl_CmdInfo dummy;

    /*
     * Don't bother if we don't have an interp or the open document procedure
     * doesn't exist.
     */

    if (!interp ||
	    !Tcl_GetCommandInfo(interp, "::tk::mac::OpenDocument", &dummy)) {
	return noErr;
    }

    /*
     * If we get any errors wil retrieving our parameters we just return with
     * no error.
     */

    if (ChkErr(AEGetParamDesc, event, keyDirectObject, typeAEList,
	    &fileSpecList) != noErr) {
	return noErr;
    }
    if (MissedAnyParameters(event) != noErr) {
	return noErr;
    }
    if (ChkErr(AECountItems, &fileSpecList, &count) != noErr) {
	return noErr;
    }

    /*
     * Convert our parameters into a script to evaluate, skipping things that
     * we can't handle right.
     */

    Tcl_DStringInit(&command);
    Tcl_DStringAppend(&command, "::tk::mac::OpenDocument", -1);
    for (index = 1; index <= count; index++) {
	if (ChkErr(AEGetNthPtr, &fileSpecList, index, typeFSRef, &keyword,
		&type, (Ptr) &file, sizeof(FSRef), &actual) != noErr) {
	    continue;
	}

	if (ChkErr(FSRefToDString, &file, &pathName) == noErr) {
	    Tcl_DStringAppendElement(&command, Tcl_DStringValue(&pathName));
	    Tcl_DStringFree(&pathName);
	}
    }

    /*
     * Now handle the event by evaluating a script.
     */

    if (Tcl_EvalEx(interp, Tcl_DStringValue(&command),
	    Tcl_DStringLength(&command), TCL_EVAL_GLOBAL) != TCL_OK) {
	Tcl_BackgroundError(interp);
    }
    Tcl_DStringFree(&command);
    return noErr;
}

/*
 *----------------------------------------------------------------------
 *
 * PrintHandler --
 *
 *	This is the 'pdoc' core Apple event handler.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */

static OSErr
PrintHandler(
    const AppleEvent * event,
    AppleEvent * reply,
    long handlerRefcon)
{
    Tcl_Interp *interp = (Tcl_Interp *) handlerRefcon;
    AEDescList fileSpecList;
    FSRef file;
    DescType type;
    Size actual;
    long count, index;
    AEKeyword keyword;
    Tcl_DString command, pathName;
    Tcl_CmdInfo dummy;

    /*
     * Don't bother if we don't have an interp or the print document procedure
     * doesn't exist.
     */

    if (!interp ||
	    !Tcl_GetCommandInfo(interp, "::tk::mac::PrintDocument", &dummy)) {
	return noErr;
    }

    /*
     * If we get any errors wil retrieving our parameters we just return with
     * no error.
     */

    if (ChkErr(AEGetParamDesc, event, keyDirectObject, typeAEList,
	    &fileSpecList) != noErr) {
	return noErr;
    }
    if (ChkErr(MissedAnyParameters, event) != noErr) {
	return noErr;
    }
    if (ChkErr(AECountItems, &fileSpecList, &count) != noErr) {
	return noErr;
    }

    Tcl_DStringInit(&command);
    Tcl_DStringAppend(&command, "::tk::mac::PrintDocument", -1);
    for (index = 1; index <= count; index++) {
	if (ChkErr(AEGetNthPtr, &fileSpecList, index, typeFSRef, &keyword,
		&type, (Ptr) &file, sizeof(FSRef), &actual) != noErr) {
	    continue;
	}

	if (ChkErr(FSRefToDString, &file, &pathName) == noErr) {
	    Tcl_DStringAppendElement(&command, Tcl_DStringValue(&pathName));
	    Tcl_DStringFree(&pathName);
	}
    }

    if (Tcl_EvalEx(interp, Tcl_DStringValue(&command),
	    Tcl_DStringLength(&command), TCL_EVAL_GLOBAL) != TCL_OK) {
	Tcl_BackgroundError(interp);
    }
    Tcl_DStringFree(&command);
    return noErr;
}

/*
 *----------------------------------------------------------------------
 *
 * ScriptHandler --
 *
 *	This handler process the script event.
 *
 * Results:
 *	Schedules the given event to be processed.
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */

static OSErr
ScriptHandler(
    const AppleEvent *event,
    AppleEvent *reply,
    long handlerRefcon)
{
    OSStatus theErr;
    AEDescList theDesc;
    int tclErr = -1;
    Tcl_Interp *interp = (Tcl_Interp *) handlerRefcon;
    char errString[128];

    /*
     * The do script event receives one parameter that should be data or a
     * file.
     */

    theErr = AEGetParamDesc(event, keyDirectObject, typeWildCard,
	    &theDesc);
    if (theErr != noErr) {
	sprintf(errString, "AEDoScriptHandler: GetParamDesc error %ld",
		theErr);
	theErr = AEPutParamPtr(reply, keyErrorString, typeChar, errString,
		strlen(errString));
    } else if (MissedAnyParameters(event)) {
	/*
	 * Return error if parameter is missing.
	 */

	sprintf(errString, "AEDoScriptHandler: extra parameters");
	AEPutParamPtr(reply, keyErrorString, typeChar, errString,
		strlen(errString));
	theErr = -1771;
    } else if (theDesc.descriptorType == (DescType) typeChar) {
	/*
	 * We've had some data sent to us. Evaluate it.
	 */

	Tcl_DString encodedText;
	short i;
	Size size = AEGetDescDataSize(&theDesc);
	char *data = ckalloc(size + 1);

	AEGetDescData(&theDesc, data, size);
	data[size] = 0;
	for (i = 0; i < size; i++) {
	    if (data[i] == '\r') {
		data[i] = '\n';
	    }
	}
	AEReplaceDescData(theDesc.descriptorType, data, size + 1, &theDesc);
	Tcl_ExternalToUtfDString(NULL, data, size, &encodedText);
	tclErr = Tcl_EvalEx(interp, Tcl_DStringValue(&encodedText),
		Tcl_DStringLength(&encodedText), TCL_EVAL_GLOBAL);
	Tcl_DStringFree(&encodedText);
    } else if (theDesc.descriptorType == (DescType) typeAlias) {
	/*
	 * We've had a file sent to us. Source it.
	 */

	Boolean dummy;
	FSRef file;
	Size theSize = AEGetDescDataSize(&theDesc);
	AliasPtr alias = (AliasPtr) ckalloc(theSize);

	if (alias) {
	    AEGetDescData(&theDesc, alias, theSize);

	    theErr = FSResolveAlias(NULL, &alias, &file, &dummy);
	    ckfree((char*)alias);
	} else {
	    theErr = memFullErr;
	}
	if (theErr == noErr) {
	    Tcl_DString scriptName;

	    theErr = FSRefToDString(&file, &scriptName);
	    if (theErr == noErr) {
		Tcl_EvalFile(interp, Tcl_DStringValue(&scriptName));
		Tcl_DStringFree(&scriptName);
	    }
	} else {
	    sprintf(errString, "AEDoScriptHandler: file not found");
	    AEPutParamPtr(reply, keyErrorString, typeChar, errString,
		    strlen(errString));
	}
    } else {
	/*
	 * Umm, don't recognize what we've got...
	 */

	sprintf(errString, "AEDoScriptHandler: invalid script type '%-4.4s',"
		" must be 'alis' or 'TEXT'", (char*) &theDesc.descriptorType);
	AEPutParamPtr(reply, keyErrorString, typeChar, errString,
		strlen(errString));
	theErr = -1770;
    }

    /*
     * If we actually go to run Tcl code - put the result in the reply.
     */

    if (tclErr >= 0) {
	int reslen;
	const char *result =
		Tcl_GetStringFromObj(Tcl_GetObjResult(interp), &reslen);

	if (tclErr == TCL_OK) {
	    AEPutParamPtr(reply, keyDirectObject, typeChar, result, reslen);
	} else {
	    AEPutParamPtr(reply, keyErrorString, typeChar, result, reslen);
	    AEPutParamPtr(reply, keyErrorNumber, typeInteger, (Ptr) &tclErr,
		    sizeof(int));
	}
    }

    AEDisposeDesc(&theDesc);
    return theErr;
}

/*
 *----------------------------------------------------------------------
 *
 * ReallyKillMe --
 *
 *	This proc tries to kill the shell by running exit, called from an
 *	event scheduled by the "Quit" AppleEvent handler.
 *
 * Results:
 *	Runs the "exit" command which might kill the shell.
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */

static int
ReallyKillMe(
    Tcl_Event *eventPtr,
    int flags)
{
    Tcl_Interp *interp = ((KillEvent *) eventPtr)->interp;
    Tcl_CmdInfo dummy;
    int quit = Tcl_GetCommandInfo(interp, "::tk::mac::Quit", &dummy);

    if (Tcl_GlobalEval(interp, quit ? "::tk::mac::Quit" : "exit") != TCL_OK) {
	/*
	 * Should be never reached...
	 */

	Tcl_BackgroundError(interp);
    }
    return 1;
}

/*
 *----------------------------------------------------------------------
 *
 * MissedAnyParameters --
 *
 *	Checks to see if parameters are still left in the event.
 *
 * Results:
 *	True or false.
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */

static int
MissedAnyParameters(
    const AppleEvent *theEvent)
{
   DescType returnedType;
   Size actualSize;
   OSStatus err;

   err = ChkErr(AEGetAttributePtr, theEvent, keyMissedKeywordAttr,
	    typeWildCard, &returnedType, NULL, 0, &actualSize);

   return (err != errAEDescNotFound);
}

/*
 *----------------------------------------------------------------------
 *
 * FSRefToDString --
 *
 *	Get a POSIX path from an FSRef.
 *
 * Results:
 *	In the parameter ds.
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */

static OSStatus
FSRefToDString(
    const FSRef *fsref,
    Tcl_DString *ds)
{
    UInt8 fileName[PATH_MAX+1];
    OSStatus err;

    err = ChkErr(FSRefMakePath, fsref, fileName, sizeof(fileName));
    if (err == noErr) {
	Tcl_ExternalToUtfDString(NULL, (char*) fileName, -1, ds);
    }
    return err;
}

/*
 * Local Variables:
 * mode: c
 * c-basic-offset: 4
 * fill-column: 78
 * End:
 */
