/*
 * tkMacOSXDialog.c --
 *
 *	Contains the Mac implementation of the common dialog boxes.
 *
 * Copyright (c) 1996-1997 Sun Microsystems, Inc.
 * Copyright 2001, Apple Computer, Inc.
 * Copyright (c) 2006-2007 Daniel A. Steffen <das@users.sourceforge.net>
 *
 * See the file "license.terms" for information on usage and redistribution
 * of this file, and for a DISCLAIMER OF ALL WARRANTIES.
 *
 * RCS: @(#) $Id: tkMacOSXDialog.c,v 1.36.2.2 2008/05/03 21:33:00 das Exp $
 */

#include "tkMacOSXPrivate.h"
#include "tkFileFilter.h"

#ifndef StrLength
#define StrLength(s)	(*((unsigned char *) (s)))
#endif
#ifndef StrBody
#define StrBody(s)	((char *) (s) + 1)
#endif

#define OPEN_POPUP_ITEM 10

#define SAVE_FILE	0
#define OPEN_FILE	1
#define CHOOSE_FOLDER	2

#define MATCHED		0
#define UNMATCHED	1

#define TK_DEFAULT_ABOUT 128

/*
 * The following structures are used in the GetFileName() function. They store
 * information about the file dialog and the file filters.
 */
typedef struct _OpenFileData {
    FileFilterList fl;          /* List of file filters.                   */
    SInt16 curType;             /* The filetype currently being listed.    */
    short initialType;          /* Type to use initially                   */
    short popupItem;            /* Item number of the popup in the dialog. */
    short usePopup;             /* True if we show the popup menu (this    */
                                /* is an open operation and the            */
                                /* -filetypes option is set).              */
} OpenFileData;

typedef struct NavHandlerUserData {
    OpenFileData *ofdPtr;
    NavReplyRecord reply;
    OSStatus err;
    CFStringRef saveNameRef;
    int sheet;
    WindowRef dialogWindow, origUnavailWindow;
    WindowModality origModality;
} NavHandlerUserData;

/*
 * The following structure is used in the tk_messageBox implementation.
 */

typedef struct {
    int buttonIndex;
    WindowRef dialogWindow, origUnavailWindow;
    WindowModality origModality;
    EventHandlerRef handlerRef;
} AlertHandlerUserData;


static OSStatus		AlertHandler(EventHandlerCallRef callRef,
			    EventRef eventRef, void *userData);
static Boolean		MatchOneType(StringPtr fileNamePtr, OSType fileType,
			    OpenFileData *myofdPtr, FileFilter *filterPtr);
static pascal Boolean	OpenFileFilterProc(AEDesc* theItem, void* info,
			    NavCallBackUserData callBackUD,
			    NavFilterModes filterMode);
static pascal void	OpenEventProc(NavEventCallbackMessage callBackSelector,
			    NavCBRecPtr callBackParms,
			    NavCallBackUserData callBackUD);
static void		InitFileDialogs(void);
static int		NavServicesGetFile(Tcl_Interp *interp,
			    OpenFileData *ofd, AEDesc *initialDescPtr,
			    char *initialFile, AEDescList *selectDescPtr,
			    CFStringRef title, CFStringRef message,
			    const char *initialType, int multiple, int isOpen,
			    Tk_Window parent);
static int		HandleInitialDirectory(Tcl_Interp *interp,
			    char *initialFile, char *initialDir, FSRef *dirRef,
			    AEDescList *selectDescPtr, AEDesc *dirDescPtr);

/*
 * Have we initialized the file dialog subsystem
 */

static int fileDlgInited = 0;

/*
 * Filter and hook functions used by the tk_getOpenFile and tk_getSaveFile
 * commands.
 */

static NavObjectFilterUPP openFileFilterUPP;
static NavEventUPP openFileEventUPP;

/*
 *----------------------------------------------------------------------
 *
 * Tk_ChooseColorObjCmd --
 *
 *	This procedure implements the color dialog box for the Mac platform.
 *	See the user documentation for details on what it does.
 *
 * Results:
 *	A standard Tcl result.
 *
 * Side effects:
 *	See the user documentation.
 *
 *----------------------------------------------------------------------
 */

int
Tk_ChooseColorObjCmd(
    ClientData clientData,	/* Main window associated with interpreter. */
    Tcl_Interp *interp,		/* Current interpreter. */
    int objc,			/* Number of arguments. */
    Tcl_Obj *CONST objv[])	/* Argument objects. */
{
    OSStatus err;
    int result = TCL_ERROR;
    Tk_Window parent, tkwin = clientData;
    const char *title;
    int i, srcRead, dstWrote;
    CMError cmerr;
    CMProfileRef prof;
    NColorPickerInfo cpinfo;
    static RGBColor color = {0xffff, 0xffff, 0xffff};
    static const char *optionStrings[] = {
	"-initialcolor", "-parent", "-title", NULL
    };
    enum options {
	COLOR_INITIAL, COLOR_PARENT, COLOR_TITLE
    };

    title = "Choose a color:";
    bzero(&cpinfo, sizeof(cpinfo));
    cpinfo.theColor.color.rgb.red   = color.red;
    cpinfo.theColor.color.rgb.green = color.green;
    cpinfo.theColor.color.rgb.blue  = color.blue;

    for (i = 1; i < objc; i += 2) {
	int index;
	const char *option, *value;

	if (Tcl_GetIndexFromObj(interp, objv[i], optionStrings, "option",
		TCL_EXACT, &index) != TCL_OK) {
	    goto end;
	}
	if (i + 1 == objc) {
	    option = Tcl_GetString(objv[i]);
	    Tcl_AppendResult(interp, "value for \"", option, "\" missing",
		    NULL);
	    goto end;
	}
	value = Tcl_GetString(objv[i + 1]);

	switch ((enum options) index) {
	    case COLOR_INITIAL: {
		XColor *colorPtr;

		colorPtr = Tk_GetColor(interp, tkwin, value);
		if (colorPtr == NULL) {
		    goto end;
		}
		cpinfo.theColor.color.rgb.red   = colorPtr->red;
		cpinfo.theColor.color.rgb.green = colorPtr->green;
		cpinfo.theColor.color.rgb.blue  = colorPtr->blue;
		Tk_FreeColor(colorPtr);
		break;
	    }
	    case COLOR_PARENT: {
		parent = Tk_NameToWindow(interp, value, tkwin);
		if (parent == NULL) {
		    goto end;
		}
		break;
	    }
	    case COLOR_TITLE: {
		title = value;
		break;
	    }
	}
    }

    cmerr = CMGetDefaultProfileBySpace(cmRGBData, &prof);
    cpinfo.theColor.profile = prof;
    cpinfo.dstProfile = prof;
    cpinfo.flags = kColorPickerDialogIsMoveable | kColorPickerDialogIsModal;
    cpinfo.placeWhere = kCenterOnMainScreen;
    /* Currently, this does not actually change the colorpicker title */
    Tcl_UtfToExternal(NULL, TkMacOSXCarbonEncoding, title, -1, 0, NULL,
	    StrBody(cpinfo.prompt), 255, &srcRead, &dstWrote, NULL);
    StrLength(cpinfo.prompt) = (unsigned char) dstWrote;

    TkMacOSXTrackingLoop(1);
    err = ChkErr(NPickColor, &cpinfo);
    TkMacOSXTrackingLoop(0);
    cmerr = CMCloseProfile(prof);
    if ((err == noErr) && (cpinfo.newColorChosen != 0)) {
	char colorstr[8];

	color.red   = cpinfo.theColor.color.rgb.red;
	color.green = cpinfo.theColor.color.rgb.green;
	color.blue  = cpinfo.theColor.color.rgb.blue;
	snprintf(colorstr, 8, "#%02x%02x%02x", color.red >> 8,
		color.green >> 8, color.blue >> 8);
	Tcl_SetObjResult(interp, Tcl_NewStringObj(colorstr, 7));
    } else {
	Tcl_ResetResult(interp);
    }
    result = TCL_OK;

  end:
    return result;
}

/*
 *----------------------------------------------------------------------
 *
 * Tk_GetOpenFileObjCmd --
 *
 *	This procedure implements the "open file" dialog box for the Mac
 *	platform. See the user documentation for details on what it does.
 *
 * Results:
 *	A standard Tcl result.
 *
 * Side effects:
 *	See user documentation.
 *----------------------------------------------------------------------
 */

int
Tk_GetOpenFileObjCmd(
    ClientData clientData,	/* Main window associated with interpreter. */
    Tcl_Interp *interp,		/* Current interpreter. */
    int objc,			/* Number of arguments. */
    Tcl_Obj *CONST objv[])	/* Argument objects. */
{
    int i, result = TCL_ERROR, multiple = 0;
    OpenFileData ofd;
    Tk_Window parent = NULL;
    CFStringRef message = NULL, title = NULL;
    AEDesc initialDesc = {typeNull, NULL};
    FSRef dirRef;
    AEDesc *initialPtr = NULL;
    AEDescList selectDesc = {typeNull, NULL};
    char *initialFile = NULL, *initialDir = NULL;
    Tcl_Obj *typeVariablePtr = NULL;
    const char *initialtype = NULL;
    static const char *openOptionStrings[] = {
	"-defaultextension", "-filetypes", "-initialdir", "-initialfile",
	"-message", "-multiple", "-parent", "-title", "-typevariable", NULL
    };
    enum openOptions {
	OPEN_DEFAULT, OPEN_FILETYPES, OPEN_INITDIR, OPEN_INITFILE,
	OPEN_MESSAGE, OPEN_MULTIPLE, OPEN_PARENT, OPEN_TITLE,
	OPEN_TYPEVARIABLE,
    };

    if (!fileDlgInited) {
	InitFileDialogs();
    }
    TkInitFileFilters(&ofd.fl);
    ofd.curType = 0;
    ofd.initialType = -1;
    ofd.popupItem = OPEN_POPUP_ITEM;
    ofd.usePopup = 1;

    for (i = 1; i < objc; i += 2) {
	char *choice;
	int index, choiceLen;
	char *string;
	Tcl_Obj *types;

	if (Tcl_GetIndexFromObj(interp, objv[i], openOptionStrings, "option",
		TCL_EXACT, &index) != TCL_OK) {
	    goto end;
	}
	if (i + 1 == objc) {
	    string = Tcl_GetString(objv[i]);
	    Tcl_AppendResult(interp, "value for \"", string, "\" missing",
		    NULL);
	    goto end;
	}

	switch (index) {
	case OPEN_DEFAULT:
	    break;
	case OPEN_FILETYPES:
	    types = objv[i + 1];
	    if (TkGetFileFilters(interp, &ofd.fl, types, 0) != TCL_OK) {
		goto end;
	    }
	    break;
	case OPEN_INITDIR:
	    initialDir = Tcl_GetStringFromObj(objv[i + 1], &choiceLen);
	    /* empty strings should be like no selection given */
	    if (choiceLen == 0) {
		initialDir = NULL;
	    }
	    break;
	case OPEN_INITFILE:
	    initialFile = Tcl_GetString(objv[i + 1]);
	    /* empty strings should be like no selection given */
	    if (choiceLen == 0) {
		initialFile = NULL;
	    }
	    break;
	case OPEN_MESSAGE:
	    choice = Tcl_GetStringFromObj(objv[i + 1], &choiceLen);
	    message = CFStringCreateWithBytes(NULL, (unsigned char *) choice,
		    choiceLen, kCFStringEncodingUTF8, false);
	    break;
	case OPEN_MULTIPLE:
	    if (Tcl_GetBooleanFromObj(interp, objv[i + 1],
		    &multiple) != TCL_OK) {
		goto end;
	    }
	    break;
	case OPEN_PARENT:
	    choice = Tcl_GetStringFromObj(objv[i + 1], &choiceLen);
	    parent = Tk_NameToWindow(interp, choice, clientData);
	    if (parent == NULL) {
		goto end;
	    }
	    break;
	case OPEN_TITLE:
	    choice = Tcl_GetStringFromObj(objv[i + 1], &choiceLen);
	    title = CFStringCreateWithBytes(NULL, (unsigned char *) choice,
		    choiceLen, kCFStringEncodingUTF8, false);
	    break;
	case OPEN_TYPEVARIABLE:
	    typeVariablePtr = objv[i + 1];
	    break;
	}
    }

    if (HandleInitialDirectory(interp, initialFile, initialDir, &dirRef,
	    &selectDesc, &initialDesc) != TCL_OK) {
	goto end;
    }
    if (initialDesc.descriptorType == typeFSRef) {
	initialPtr = &initialDesc;
    }
    if (typeVariablePtr) {
	initialtype = Tcl_GetVar(interp, Tcl_GetString(typeVariablePtr), 0);
    }
    result = NavServicesGetFile(interp, &ofd, initialPtr, NULL, &selectDesc,
	    title, message, initialtype, multiple, OPEN_FILE, parent);

    if (typeVariablePtr) {
	FileFilter *filterPtr = ofd.fl.filters;
	int i = ofd.curType;

	while (filterPtr && i-- > 0) {
	    filterPtr = filterPtr->next;
	}
	Tcl_SetVar(interp, Tcl_GetString(typeVariablePtr), filterPtr->name, 0);
    }

  end:
    TkFreeFileFilters(&ofd.fl);
    if (initialDesc.dataHandle) {
	ChkErr(AEDisposeDesc, &initialDesc);
    }
    if (selectDesc.dataHandle) {
	ChkErr(AEDisposeDesc, &selectDesc);
    }
    if (title) {
	CFRelease(title);
    }
    if (message) {
	CFRelease(message);
    }
    return result;
}

/*
 *----------------------------------------------------------------------
 *
 * Tk_GetSaveFileObjCmd --
 *
 *	Same as Tk_GetOpenFileCmd but opens a "save file" dialog box instead.
 *
 * Results:
 *	A standard Tcl result.
 *
 * Side effects:
 *	See user documentation.
 *----------------------------------------------------------------------
 */

int
Tk_GetSaveFileObjCmd(
    ClientData clientData,	/* Main window associated with interpreter. */
    Tcl_Interp *interp,		/* Current interpreter. */
    int objc,			/* Number of arguments. */
    Tcl_Obj *CONST objv[])	/* Argument objects. */
{
    int i, result = TCL_ERROR;
    char *initialFile = NULL;
    Tk_Window parent = NULL;
    AEDesc initialDesc = {typeNull, NULL};
    AEDesc *initialPtr = NULL;
    FSRef dirRef;
    CFStringRef title = NULL, message = NULL;
    OpenFileData ofd;
    static const char *saveOptionStrings[] = {
	"-defaultextension", "-filetypes", "-initialdir", "-initialfile",
	"-message", "-parent", "-title", "-typevariable", NULL
    };
    enum saveOptions {
	SAVE_DEFAULT, SAVE_FILETYPES, SAVE_INITDIR, SAVE_INITFILE,
	SAVE_MESSAGE, SAVE_PARENT, SAVE_TITLE, SAVE_TYPEVARIABLE,
    };

    if (!fileDlgInited) {
	InitFileDialogs();
    }

    TkInitFileFilters(&ofd.fl);
    ofd.curType = 0;
    ofd.usePopup = 0;

    for (i = 1; i < objc; i += 2) {
	char *choice, *string;
	int index, choiceLen;
	Tcl_Obj *types;

	if (Tcl_GetIndexFromObj(interp, objv[i], saveOptionStrings, "option",
		TCL_EXACT, &index) != TCL_OK) {
	    goto end;
	}
	if (i + 1 == objc) {
	    string = Tcl_GetString(objv[i]);
	    Tcl_AppendResult(interp, "value for \"", string, "\" missing",
		    NULL);
	    goto end;
	}
	switch (index) {
	case SAVE_DEFAULT:
	    break;
	case SAVE_FILETYPES:
	    types = objv[i + 1];
	    if (TkGetFileFilters(interp, &ofd.fl, types, 0) != TCL_OK) {
		goto end;
	    }
	    break;
	case SAVE_INITDIR:
	    choice = Tcl_GetStringFromObj(objv[i + 1], &choiceLen);
	    /* empty strings should be like no selection given */
	    if (choiceLen && HandleInitialDirectory(interp, NULL, choice,
		    &dirRef, NULL, &initialDesc) != TCL_OK) {
		goto end;
	    }
	    break;
	case SAVE_INITFILE:
	    initialFile = Tcl_GetStringFromObj(objv[i + 1], &choiceLen);
	    /* empty strings should be like no selection given */
	    if (choiceLen == 0) {
		initialFile = NULL;
	    }
	    break;
	case SAVE_MESSAGE:
	    choice = Tcl_GetStringFromObj(objv[i + 1], &choiceLen);
	    message = CFStringCreateWithBytes(NULL, (unsigned char *) choice,
		    choiceLen, kCFStringEncodingUTF8, false);
	    break;
	case SAVE_PARENT:
	    choice = Tcl_GetStringFromObj(objv[i + 1], &choiceLen);
	    parent = Tk_NameToWindow(interp, choice, (Tk_Window) clientData);
	    if (parent == NULL) {
		goto end;
	    }
	    break;
	case SAVE_TITLE:
	    choice = Tcl_GetStringFromObj(objv[i + 1], &choiceLen);
	    title = CFStringCreateWithBytes(NULL, (unsigned char *) choice,
		    choiceLen, kCFStringEncodingUTF8, false);
	    break;
	}
    }

    if (initialDesc.descriptorType == typeFSRef) {
	initialPtr = &initialDesc;
    }
    result = NavServicesGetFile(interp, &ofd, initialPtr, initialFile, NULL,
	    title, message, NULL, false, SAVE_FILE, parent);
    TkFreeFileFilters(&ofd.fl);
  end:
    if (initialDesc.dataHandle) {
	ChkErr(AEDisposeDesc, &initialDesc);
    }
    if (title) {
	CFRelease(title);
    }
    if (message) {
	CFRelease(message);
    }
    return result;
}

/*
 *----------------------------------------------------------------------
 *
 * Tk_ChooseDirectoryObjCmd --
 *
 *	This procedure implements the "tk_chooseDirectory" dialog box for the
 *	MacOS X platform. See the user documentation for details on what it
 *	does.
 *
 * Results:
 *	See user documentation.
 *
 * Side effects:
 *	A modal dialog window is created.
 *
 *----------------------------------------------------------------------
 */

int
Tk_ChooseDirectoryObjCmd(
    ClientData clientData,	/* Main window associated with interpreter. */
    Tcl_Interp *interp,		/* Current interpreter. */
    int objc,			/* Number of arguments. */
    Tcl_Obj *CONST objv[])	/* Argument objects. */
{
    int i, result = TCL_ERROR;
    Tk_Window parent = NULL;
    AEDesc initialDesc = {typeNull, NULL}, *initialPtr = NULL;
    FSRef dirRef;
    CFStringRef message = NULL, title = NULL;
    OpenFileData ofd;
    static const char *chooseOptionStrings[] = {
	"-initialdir", "-message", "-mustexist", "-parent", "-title", NULL
    };
    enum chooseOptions {
	CHOOSE_INITDIR, CHOOSE_MESSAGE, CHOOSE_MUSTEXIST, CHOOSE_PARENT,
	CHOOSE_TITLE
    };

    if (!fileDlgInited) {
	InitFileDialogs();
    }

    for (i = 1; i < objc; i += 2) {
	char *string, *choice;
	int index, choiceLen;

	if (Tcl_GetIndexFromObj(interp, objv[i], chooseOptionStrings, "option",
		TCL_EXACT, &index) != TCL_OK) {
	    goto end;
	}
	if (i + 1 == objc) {
	    string = Tcl_GetString(objv[i]);
	    Tcl_AppendResult(interp, "value for \"", string, "\" missing",
		    NULL);
	    goto end;
	}
	switch (index) {
	case CHOOSE_INITDIR:
	    choice = Tcl_GetStringFromObj(objv[i + 1], &choiceLen);
	    if (choiceLen && HandleInitialDirectory(interp, NULL, choice,
		    &dirRef, NULL, &initialDesc) != TCL_OK) {
		goto end;
	    }
	    break;
	case CHOOSE_MESSAGE:
	    choice = Tcl_GetStringFromObj(objv[i + 1], &choiceLen);
	    message = CFStringCreateWithBytes(NULL, (unsigned char *) choice,
		    choiceLen, kCFStringEncodingUTF8, false);
	    break;
	case CHOOSE_PARENT:
	    choice = Tcl_GetStringFromObj(objv[i + 1], &choiceLen);
	    parent = Tk_NameToWindow(interp, choice, clientData);
	    if (parent == NULL) {
		goto end;
	    }
	    break;
	case CHOOSE_TITLE:
	    choice = Tcl_GetStringFromObj(objv[i + 1], &choiceLen);
	    title = CFStringCreateWithBytes(NULL, (unsigned char *) choice,
		    choiceLen, kCFStringEncodingUTF8, false);
	    break;
	}
    }

    TkInitFileFilters(&ofd.fl);
    ofd.usePopup = 0;
    if (initialDesc.descriptorType == typeFSRef) {
	initialPtr = &initialDesc;
    }
    result = NavServicesGetFile(interp, &ofd, initialPtr, NULL, NULL, title,
	    message, NULL, false, CHOOSE_FOLDER, parent);
    TkFreeFileFilters(&ofd.fl);
  end:
    if (initialDesc.dataHandle) {
	ChkErr(AEDisposeDesc, &initialDesc);
    }
    if (title) {
	CFRelease(title);
    }
    if (message) {
	CFRelease(message);
    }
    return result;
}

/*
 *----------------------------------------------------------------------
 *
 * HandleInitialDirectory --
 *
 *	Helper for -initialdir setup.
 *
 * Results:
 *	Tcl result.
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */

int
HandleInitialDirectory(
    Tcl_Interp *interp,
    char *initialFile,
    char *initialDir,
    FSRef *dirRef,
    AEDescList *selectDescPtr,
    AEDesc *dirDescPtr)
{
    Tcl_DString ds;
    OSStatus err;
    Boolean isDirectory;
    char *dirName = NULL;
    int result = TCL_ERROR;

    if (initialDir) {
	dirName = Tcl_TranslateFileName(interp, initialDir, &ds);
	if (dirName == NULL) {
	    goto end;
	}
	err = ChkErr(FSPathMakeRef, (unsigned char *) dirName, dirRef,
		&isDirectory);
	if (err != noErr) {
	    Tcl_AppendResult(interp, "bad directory \"", initialDir, "\"",
		    NULL);
	    goto end;
	}
	if (!isDirectory) {
	    Tcl_AppendResult(interp, "-intialdir \"", initialDir, "\""
		    " is a file, not a directory.", NULL);
	    goto end;
	}
	ChkErr(AECreateDesc, typeFSRef, dirRef, sizeof(*dirRef), dirDescPtr);
    }

    if (initialFile && selectDescPtr) {
	FSRef fileRef;
	AEDesc fileDesc;
	char *namePtr;

	if (initialDir) {
	    Tcl_DStringAppend(&ds, "/", 1);
	    Tcl_DStringAppend(&ds, initialFile, -1);
	    namePtr = Tcl_DStringValue(&ds);
	} else {
	    namePtr = initialFile;
	}

	ChkErr(AECreateList, NULL, 0, false, selectDescPtr);

	err = ChkErr(FSPathMakeRef, (unsigned char *) namePtr, &fileRef,
		&isDirectory);
	if (err != noErr) {
	    Tcl_AppendResult(interp, "bad initialfile \"", initialFile,
		    "\" file does not exist.", NULL);
	    goto end;
	}
	ChkErr(AECreateDesc, typeFSRef, &fileRef, sizeof(fileRef), &fileDesc);
	ChkErr(AEPutDesc, selectDescPtr, 1, &fileDesc);
	ChkErr(AEDisposeDesc, &fileDesc);
    }
    result = TCL_OK;
  end:
    if (dirName) {
	Tcl_DStringFree(&ds);
    }
    return result;
}

/*
 *----------------------------------------------------------------------
 *
 * InitFileDialogs --
 *
 *	Initialize file dialog subsystem.
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
InitFileDialogs(void)
{
    fileDlgInited = 1;
    openFileFilterUPP = NewNavObjectFilterUPP(OpenFileFilterProc);
    openFileEventUPP = NewNavEventUPP(OpenEventProc);
}

/*
 *----------------------------------------------------------------------
 *
 * NavServicesGetFile --
 *
 *	Common wrapper for NavServices API.
 *
 * Results:
 *	Tcl result.
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */

int
NavServicesGetFile(
    Tcl_Interp *interp,
    OpenFileData *ofdPtr,
    AEDesc *initialDescPtr,
    char *initialFile,
    AEDescList *selectDescPtr,
    CFStringRef title,
    CFStringRef message,
    const char *initialtype,
    int multiple,
    int isOpen,
    Tk_Window parent)
{
    NavHandlerUserData data;
    NavDialogCreationOptions options;
    NavDialogRef dialogRef = NULL;
    CFStringRef *menuItemNames = NULL;
    OSStatus err;
    Tcl_Obj *theResult = NULL;
    int result = TCL_ERROR;

    bzero(&data, sizeof(data));
    err = NavGetDefaultDialogCreationOptions(&options);
    if (err != noErr) {
	return result;
    }
    options.optionFlags = kNavDontAutoTranslate | kNavDontAddTranslateItems
	    | kNavSupportPackages | kNavAllFilesInPopup;
    if (multiple) {
	options.optionFlags |= kNavAllowMultipleFiles;
    }
    options.modality = kWindowModalityAppModal;
    if (parent && ((TkWindow *) parent)->window != None &&
	    TkMacOSXHostToplevelExists(parent)) {
	options.parentWindow = TkMacOSXDrawableWindow(Tk_WindowId(parent));
	TK_IF_HI_TOOLBOX (5,
	    /*
	     * Impossible to modify dialog modality with the Cocoa-based
	     * NavServices implementation.
	     */
	) TK_ELSE_HI_TOOLBOX (5,
	    if (options.parentWindow) {
		options.modality = kWindowModalityWindowModal;
		data.sheet = 1;
	    }
	) TK_ENDIF
    }

    /*
     * Now process the selection list. We have to use the popupExtension
     * to fill the menu.
     */

    if (ofdPtr && ofdPtr->usePopup) {
	FileFilter *filterPtr = ofdPtr->fl.filters;

	if (filterPtr == NULL) {
	    ofdPtr->usePopup = 0;
	}
    }
    if (ofdPtr && ofdPtr->usePopup) {
	FileFilter *filterPtr;
	int index = 0;
	ofdPtr->curType = 0;

	menuItemNames = (CFStringRef *)
		ckalloc(ofdPtr->fl.numFilters * sizeof(CFStringRef));

	for (filterPtr = ofdPtr->fl.filters; filterPtr != NULL;
		filterPtr = filterPtr->next, index++) {
	    menuItemNames[index] = CFStringCreateWithCString(NULL,
		    filterPtr->name, kCFStringEncodingUTF8);
	    if (initialtype && strcmp(filterPtr->name, initialtype) == 0) {
		ofdPtr->initialType = index;
	    }
	}
	options.popupExtension = CFArrayCreate(NULL,
		(const void **) menuItemNames, ofdPtr->fl.numFilters, NULL);
    } else {
	options.optionFlags |= kNavNoTypePopup;
	options.popupExtension = NULL;
    }
    options.clientName = CFSTR("Wish");
    options.message = message;
    options.windowTitle = title;
    if (initialFile) {
	options.saveFileName = CFStringCreateWithCString(NULL, initialFile,
		kCFStringEncodingUTF8);
    } else {
	options.saveFileName = NULL;
    }
    if (isOpen == OPEN_FILE) {
	data.ofdPtr = ofdPtr;
	err = ChkErr(NavCreateGetFileDialog, &options, NULL,
		openFileEventUPP, NULL, openFileFilterUPP, &data, &dialogRef);
    } else if (isOpen == SAVE_FILE) {
	err = ChkErr(NavCreatePutFileDialog, &options, 'TEXT', 'WIsH',
		openFileEventUPP, &data, &dialogRef);
    } else if (isOpen == CHOOSE_FOLDER) {
	err = ChkErr(NavCreateChooseFolderDialog, &options,
		openFileEventUPP, openFileFilterUPP, &data, &dialogRef);
    }
    if (err == noErr && dialogRef) {
	if (initialDescPtr) {
	    ChkErr(NavCustomControl, dialogRef, kNavCtlSetLocation,
		initialDescPtr);
	}
	if (selectDescPtr && selectDescPtr->descriptorType != typeNull) {
	    ChkErr(NavCustomControl, dialogRef, kNavCtlSetSelection,
		    selectDescPtr);
	}
	TkMacOSXTrackingLoop(1);
	err = ChkErr(NavDialogRun, dialogRef);
	if (err == noErr) {
	    if (data.sheet) {
		data.dialogWindow = NavDialogGetWindow(dialogRef);
		ChkErr(GetWindowModality, data.dialogWindow,
			&data.origModality, &data.origUnavailWindow);
		ChkErr(SetWindowModality, data.dialogWindow,
			kWindowModalityAppModal, NULL);
		ChkErr(RunAppModalLoopForWindow, data.dialogWindow);
	    }
	    err = data.err;
	}
	TkMacOSXTrackingLoop(0);
    }

    /*
     * Most commands assume that the file dialogs return a single item, not a
     * list. So only build a list if multiple is true...
     */

    if (err == noErr) {
	if (multiple) {
	    theResult = Tcl_NewListObj(0, NULL);
	} else {
	    theResult = Tcl_NewObj();
	}
	if (!theResult) {
	    err = memFullErr;
	}
    }
    if (err == noErr && data.reply.validRecord) {
	AEDesc resultDesc;
	long count, i;
	FSRef fsRef;
	char pathPtr[PATH_MAX + 1];
	char saveName[PATH_MAX + 1];

	err = ChkErr(AECountItems, &data.reply.selection, &count);
	if (err != noErr) {
	    /*
	     * There was an error when counting the items? Treat as if no
	     * items were chosen.
	     */

	    goto installResult;
	}

	/*
	 * Process the chosen files. This will be one unless -multiple was
	 * specified.
	 */

	for (i = 1; i <= count; i++) {
	    /*
	     * Get the name of the selected file.
	     */

	    err = ChkErr(AEGetNthDesc, &data.reply.selection, i,
		    typeFSRef, NULL, &resultDesc);
	    if (err != noErr) {
		continue;
	    }
	    err = ChkErr(AEGetDescData, &resultDesc, &fsRef, sizeof(fsRef));
	    if (err != noErr) {
		goto nextFilename;
	    }
	    err = ChkErr(FSRefMakePath, &fsRef, (unsigned char *) pathPtr,
		    PATH_MAX + 1);
	    if (err != noErr) {
		goto nextFilename;
	    }

	    /*
	     * If we're saving the file, we're creating a new filename and
	     * must therefore check whether it is a legal filename (not
	     * exceeding path length limits, etc.)
	     */

	    if (isOpen == SAVE_FILE) {
		if (!data.saveNameRef) {
		    TkMacOSXDbgMsg("NavDialogGetSaveFileName failed");
		    goto nextFilename;
		}

		if (!CFStringGetCString(data.saveNameRef, saveName,
			PATH_MAX + 1, kCFStringEncodingUTF8)) {
		    TkMacOSXDbgMsg("CFStringGetCString failed");
		    goto nextFilename;
		}

		if (strlen(pathPtr) + strlen(saveName) >= PATH_MAX) {
		    TkMacOSXDbgMsg("Path name too long");
		    goto nextFilename;
		}

		strcat(pathPtr, "/");
		strcat(pathPtr, saveName);
	    }

	    /*
	     * Got a valid file name; put it in the result object.
	     */

	    if (multiple) {
		Tcl_ListObjAppendElement(interp, theResult,
			Tcl_NewStringObj(pathPtr, -1));
	    } else {
		Tcl_SetStringObj(theResult, pathPtr, -1);
	    }

	nextFilename:
	    ChkErr(AEDisposeDesc, &resultDesc);
	}

    installResult:
	Tcl_SetObjResult(interp, theResult);
	result = TCL_OK;
    } else if (err == userCanceledErr) {
	Tcl_ResetResult(interp);
	result = TCL_OK;
    }

    /*
     * Clean up any allocated memory.
     */

    if (data.reply.validRecord) {
	ChkErr(NavDisposeReply, &data.reply);
    }
    if (data.saveNameRef) {
	CFRelease(data.saveNameRef);
    }
    if (options.saveFileName) {
	CFRelease(options.saveFileName);
    }
    if (options.clientName) {
	CFRelease(options.clientName);
    }
    if (menuItemNames) {
	int i;

	for (i = 0; i < ofdPtr->fl.numFilters; i++) {
	    CFRelease(menuItemNames[i]);
	}
	ckfree((void *) menuItemNames);
    }
    if (options.popupExtension) {
	CFRelease(options.popupExtension);
    }
    return result;
}

/*
 *----------------------------------------------------------------------
 *
 * OpenEventProc --
 *
 *	NavServices event handling callback.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */

pascal void
OpenEventProc(
    NavEventCallbackMessage callBackSelector,
    NavCBRecPtr callBackParams,
    NavCallBackUserData callBackUD)
{
    NavHandlerUserData *data = (NavHandlerUserData*) callBackUD;
    OpenFileData *ofd = data->ofdPtr;

    switch (callBackSelector) {
	case kNavCBStart:
	    if (ofd && ofd->initialType >= 0) {
		/* Select initial filter */
		FileFilter *filterPtr = ofd->fl.filters;
		int i = ofd->initialType;

		while (filterPtr && i-- > 0) {
		    filterPtr = filterPtr->next;
		}
		if (filterPtr) {
		    NavMenuItemSpec selectItem;

		    selectItem.version = kNavMenuItemSpecVersion;
		    selectItem.menuCreator = 0;
		    selectItem.menuType = ofd->initialType;
		    selectItem.menuItemName[0] = strlen(filterPtr->name);
		    strncpy((char *) &selectItem.menuItemName[1],
			    filterPtr->name, 255);
		    ChkErr(NavCustomControl, callBackParams->context,
			    kNavCtlSelectCustomType, &selectItem);
		}
	    }
	    break;
	case kNavCBPopupMenuSelect:
	    ofd->curType = ((NavMenuItemSpec *)
		    callBackParams->eventData.eventDataParms.param)->menuType;
	    break;
	case kNavCBAccept:
	case kNavCBCancel:
	    if (data->sheet) {
		ChkErr(QuitAppModalLoopForWindow, data->dialogWindow);
		ChkErr(SetWindowModality, data->dialogWindow,
			data->origModality, data->origUnavailWindow);
	    }
	    break;
	case kNavCBUserAction:
	    if (data->reply.validRecord) {
		ChkErr(NavDisposeReply, &data->reply);
		data->reply.validRecord = 0;
	    }
	    data->err = NavDialogGetReply(callBackParams->context,
		    &data->reply);
	    if (callBackParams->userAction == kNavUserActionSaveAs) {
		data->saveNameRef = NavDialogGetSaveFileName(
			callBackParams->context);
		if (data->saveNameRef) {
		    CFRetain(data->saveNameRef);
		}
	    }
	    break;
	case kNavCBTerminate:
	    NavDialogDispose(callBackParams->context);
	    break;
	case kNavCBEvent:
	    TkMacOSXRunTclEventLoop();
	    break;
    }
}

/*
 *----------------------------------------------------------------------
 *
 * OpenFileFilterProc --
 *
 *	NavServices file filter callback.
 *
 * Results:
 *	Whether to use the file in question.
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */

pascal Boolean
OpenFileFilterProc(
    AEDesc *theItem,
    void *info,
    NavCallBackUserData callBackUD,
    NavFilterModes filterMode)
{
    OpenFileData *ofdPtr = ((NavHandlerUserData *) callBackUD)->ofdPtr;
    int result = MATCHED;

    if (ofdPtr && ofdPtr->usePopup && ofdPtr->fl.numFilters > 0 &&
	    ((theItem->descriptorType == typeFSS)
	    || (theItem->descriptorType == typeFSRef))) {
	NavFileOrFolderInfo *theInfo = info;
	char fileName[256];
	OSType fileType;
	StringPtr fileNamePtr = NULL;
	Tcl_DString fileNameDString;
	int i;
	FileFilter *filterPtr;

	if (!theInfo->isFolder) {
	    fileType = theInfo->fileAndFolder.fileInfo.finderInfo.fdType;
	    Tcl_DStringInit(&fileNameDString);

	    if (theItem->descriptorType == typeFSS) {
		int len;

		fileNamePtr = ((FSSpec *) *theItem->dataHandle)->name;
		len = fileNamePtr[0];
		strncpy(fileName, (char *) fileNamePtr + 1, len);
		fileName[len] = '\0';
		fileNamePtr = (unsigned char *) fileName;
	    } else if ((theItem->descriptorType == typeFSRef)) {
		OSStatus err;
		FSRef *theRef = (FSRef *) *theItem->dataHandle;
		HFSUniStr255 uniFileName;

		err = ChkErr(FSGetCatalogInfo, theRef, kFSCatInfoNone,
			NULL, &uniFileName, NULL, NULL);

		if (err == noErr) {
		    Tcl_UniCharToUtfDString((Tcl_UniChar *)uniFileName.unicode,
			    uniFileName.length, &fileNameDString);
		    fileNamePtr = (unsigned char *)
			    Tcl_DStringValue(&fileNameDString);
		}
	    }
	    if (ofdPtr->usePopup) {
		i = ofdPtr->curType;
		for (filterPtr = ofdPtr->fl.filters; filterPtr && i>0; i--) {
		    filterPtr = filterPtr->next;
		}
		if (filterPtr) {
		    result = MatchOneType(fileNamePtr, fileType, ofdPtr,
			    filterPtr);
		} else {
		    result = UNMATCHED;
		}
	    } else {
		/*
		 * We are not using the popup menu. In this case, the file is
		 * considered matched if it matches any of the file filters.
		 */

		result = UNMATCHED;
		for (filterPtr = ofdPtr->fl.filters; filterPtr;
			filterPtr = filterPtr->next) {
		    if (MatchOneType(fileNamePtr, fileType, ofdPtr,
			    filterPtr) == MATCHED) {
			result = MATCHED;
			break;
		    }
		}
	    }
	    Tcl_DStringFree(&fileNameDString);
	}
    }
    return (result == MATCHED);
}

/*
 *----------------------------------------------------------------------
 *
 * MatchOneType --
 *
 *	Match a file with one file type in the list of file types.
 *
 * Results:
 *	Returns MATCHED if the file matches with the file type; returns
 *	UNMATCHED otherwise.
 *
 * Side effects:
 *	None
 *
 *----------------------------------------------------------------------
 */

Boolean
MatchOneType(
    StringPtr fileNamePtr,	/* Name of the file */
    OSType fileType,		/* Type of the file, 0 means there was no
				 * specified type. */
    OpenFileData *ofdPtr,	/* Information about this file dialog */
    FileFilter *filterPtr)	/* Match the file described by pb against this
				 * filter */
{
    FileFilterClause *clausePtr;

    /*
     * A file matches with a file type if it matches with at least one clause
     * of the type.
     *
     * If the clause has both glob patterns and ostypes, the file must match
     * with at least one pattern AND at least one ostype.
     *
     * If the clause has glob patterns only, the file must match with at least
     * one pattern.
     *
     * If the clause has mac types only, the file must match with at least one
     * mac type.
     *
     * If the clause has neither glob patterns nor mac types, it's considered
     * an error.
     */

    for (clausePtr = filterPtr->clauses; clausePtr;
	    clausePtr = clausePtr->next) {
	int macMatched = 0;
	int globMatched = 0;
	GlobPattern *globPtr;
	MacFileType *mfPtr;

	if (clausePtr->patterns == NULL) {
	    globMatched = 1;
	}
	if (clausePtr->macTypes == NULL) {
	    macMatched = 1;
	}

	for (globPtr = clausePtr->patterns; globPtr;
		globPtr = globPtr->next) {
	    char *q, *ext;

	    if (fileNamePtr == NULL) {
		continue;
	    }
	    ext = globPtr->pattern;

	    if (ext[0] == '\0') {
		/*
		 * We don't want any extensions: OK if the filename doesn't
		 * have "." in it
		 */

		for (q = (char*) fileNamePtr; *q; q++) {
		    if (*q == '.') {
			goto glob_unmatched;
		    }
		}
		goto glob_matched;
	    }

	    if (Tcl_StringMatch((char*) fileNamePtr, ext)) {
		goto glob_matched;
	    }
	glob_unmatched:
	    continue;

	glob_matched:
	    globMatched = 1;
	    break;
	}

	for (mfPtr = clausePtr->macTypes; mfPtr; mfPtr = mfPtr->next) {
	    if (fileType == mfPtr->type) {
		macMatched = 1;
		break;
	    }
	}

	/*
	 * On Mac OS X, it is not uncommon for files to have NO file type. But
	 * folks with Tcl code on Classic MacOS pretty much assume that a
	 * generic file will have type TEXT. So if we were strict about
	 * matching types when the source file had NO type set, they would
	 * have to add another rule always with no fileType. To avoid that, we
	 * pass the macMatch side of the test if no fileType is set.
	 */

	if (globMatched && (macMatched || (fileType == 0))) {
	    return MATCHED;
	}
    }

    return UNMATCHED;
}

/*
 *----------------------------------------------------------------------
 *
 * TkAboutDlg --
 *
 *	Displays the default Tk About box. This code uses Macintosh resources
 *	to define the content of the About Box.
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
TkAboutDlg(void)
{
    DialogPtr aboutDlog;
    WindowRef windowRef;
    short itemHit = -9;

    aboutDlog = GetNewDialog(TK_DEFAULT_ABOUT, NULL, (void *) (-1));
    if (!aboutDlog) {
	return;
    }
    windowRef = GetDialogWindow(aboutDlog);
    SelectWindow(windowRef);
    TkMacOSXTrackingLoop(1);
    while (itemHit != 1) {
	ModalDialog(NULL, &itemHit);
    }
    TkMacOSXTrackingLoop(0);
    DisposeDialog(aboutDlog);
    SelectWindow(ActiveNonFloatingWindow());
}

/*
 *----------------------------------------------------------------------
 *
 * Tk_MessageBoxObjCmd --
 *
 *	Implements the tk_messageBox in native Mac OS X style.
 *
 * Results:
 *	A standard Tcl result.
 *
 * Side effects:
 *	none
 *
 *----------------------------------------------------------------------
 */

int
Tk_MessageBoxObjCmd(
    ClientData clientData,	/* Main window associated with interpreter. */
    Tcl_Interp *interp,		/* Current interpreter. */
    int objc,			/* Number of arguments. */
    Tcl_Obj *CONST objv[])	/* Argument objects. */
{
    Tk_Window tkwin = clientData;
    AlertStdCFStringAlertParamRec paramCFStringRec;
    AlertType alertType;
    DialogRef dialogRef;
    CFStringRef messageTextCF = NULL, finemessageTextCF = NULL;
    OSStatus err;
    SInt16 itemHit;
    Boolean haveDefaultOption = false, haveParentOption = false;
    char *str;
    int index, defaultButtonIndex;
    int defaultNativeButtonIndex; /* 1, 2, 3: right to left */
    int typeIndex, i, indexDefaultOption = 0, result = TCL_ERROR;

    static const char *movableAlertStrings[] = {
	"-default", "-detail", "-icon", "-message", "-parent", "-title",
	"-type", NULL
    };
    static const char *movableTypeStrings[] = {
	"abortretryignore", "ok", "okcancel", "retrycancel", "yesno",
	"yesnocancel", NULL
    };
    static const char *movableButtonStrings[] = {
	"abort", "retry", "ignore", "ok", "cancel", "yes", "no", NULL
    };
    static const char *movableIconStrings[] = {
	"error", "info", "question", "warning", NULL
    };
    enum movableAlertOptions {
	ALERT_DEFAULT, ALERT_DETAIL, ALERT_ICON, ALERT_MESSAGE, ALERT_PARENT,
	ALERT_TITLE, ALERT_TYPE
    };
    enum movableTypeOptions {
	TYPE_ABORTRETRYIGNORE, TYPE_OK, TYPE_OKCANCEL, TYPE_RETRYCANCEL,
	TYPE_YESNO, TYPE_YESNOCANCEL
    };
    enum movableButtonOptions {
	TEXT_ABORT, TEXT_RETRY, TEXT_IGNORE, TEXT_OK, TEXT_CANCEL, TEXT_YES,
	TEXT_NO
    };
    enum movableIconOptions {
	ICON_ERROR, ICON_INFO, ICON_QUESTION, ICON_WARNING
    };

    /*
     * Need to map from 'movableButtonStrings' and its corresponding integer,
     * index to the native button index, which is 1, 2, 3, from right to left.
     * This is necessary to do for each separate '-type' of button sets.
     */

    short buttonIndexAndTypeToNativeButtonIndex[][7] = {
    /*	abort retry ignore ok	cancel yes   no */
	{1,    2,    3,	   0,	 0,    0,    0},	/* abortretryignore */
	{0,    0,    0,	   1,	 0,    0,    0},	/* ok */
	{0,    0,    0,	   1,	 2,    0,    0},	/* okcancel */
	{0,    1,    0,	   0,	 2,    0,    0},	/* retrycancel */
	{0,    0,    0,	   0,	 0,    1,    2},	/* yesno */
	{0,    0,    0,	   0,	 3,    1,    2},	/* yesnocancel */
    };

    /*
     * Need also the inverse mapping, from native button (1, 2, 3) to the
     * descriptive button text string index.
     */

    short nativeButtonIndexAndTypeToButtonIndex[][4] = {
	{-1, 0, 1, 2},	/* abortretryignore */
	{-1, 3, 0, 0},	/* ok */
	{-1, 3, 4, 0},	/* okcancel */
	{-1, 1, 4, 0},	/* retrycancel */
	{-1, 5, 6, 0},	/* yesno */
	{-1, 5, 6, 4},	/* yesnocancel */
    };

    alertType = kAlertPlainAlert;
    typeIndex = TYPE_OK;

    ChkErr(GetStandardAlertDefaultParams, &paramCFStringRec,
	    kStdCFStringAlertVersionOne);
    paramCFStringRec.movable = true;
    paramCFStringRec.helpButton = false;
    paramCFStringRec.defaultButton = kAlertStdAlertOKButton;
    paramCFStringRec.cancelButton = kAlertStdAlertCancelButton;

    for (i = 1; i < objc; i += 2) {
	int iconIndex;
	char *string;

	if (Tcl_GetIndexFromObj(interp, objv[i], movableAlertStrings, "option",
		TCL_EXACT, &index) != TCL_OK) {
	    goto end;
	}
	if (i + 1 == objc) {
	    string = Tcl_GetString(objv[i]);
	    Tcl_AppendResult(interp, "value for \"", string, "\" missing",
		    NULL);
	    goto end;
	}

	switch (index) {
	case ALERT_DEFAULT:
	    /*
	     * Need to postpone processing of this option until we are sure to
	     * know the '-type' as well.
	     */

	    haveDefaultOption = true;
	    indexDefaultOption = i;
	    break;

	case ALERT_DETAIL:
	    str = Tcl_GetString(objv[i + 1]);
	    finemessageTextCF = CFStringCreateWithCString(NULL, str,
		    kCFStringEncodingUTF8);
	    break;

	case ALERT_ICON:
	    if (Tcl_GetIndexFromObj(interp, objv[i + 1], movableIconStrings,
		    "value", TCL_EXACT, &iconIndex) != TCL_OK) {
		goto end;
	    }
	    switch (iconIndex) {
	    case ICON_ERROR:
		alertType = kAlertStopAlert;
		break;
	    case ICON_INFO:
		alertType = kAlertNoteAlert;
		break;
	    case ICON_QUESTION:
		alertType = kAlertCautionAlert;
		break;
	    case ICON_WARNING:
		alertType = kAlertCautionAlert;
		break;
	    }
	    break;

	case ALERT_MESSAGE:
	    str = Tcl_GetString(objv[i + 1]);
	    messageTextCF = CFStringCreateWithCString(NULL, str,
		    kCFStringEncodingUTF8);
	    break;

	case ALERT_PARENT:
	    str = Tcl_GetString(objv[i + 1]);
	    tkwin = Tk_NameToWindow(interp, str, tkwin);
	    if (tkwin == NULL) {
		goto end;
	    }
	    if (((TkWindow *) tkwin)->window != None &&
		    TkMacOSXHostToplevelExists(tkwin)) {
		haveParentOption = true;
	    }
	    break;

	case ALERT_TITLE:
	    break;

	case ALERT_TYPE:
	    if (Tcl_GetIndexFromObj(interp, objv[i + 1], movableTypeStrings,
		    "value", TCL_EXACT, &typeIndex) != TCL_OK) {
		goto end;
	    }
	    switch (typeIndex) {
	    case TYPE_ABORTRETRYIGNORE:
		paramCFStringRec.defaultText = CFSTR("Abort");
		paramCFStringRec.cancelText = CFSTR("Retry");
		paramCFStringRec.otherText = CFSTR("Ignore");
		paramCFStringRec.cancelButton = kAlertStdAlertOtherButton;
		break;
	    case TYPE_OK:
		paramCFStringRec.defaultText = CFSTR("OK");
		break;
	    case TYPE_OKCANCEL:
		paramCFStringRec.defaultText = CFSTR("OK");
		paramCFStringRec.cancelText = CFSTR("Cancel");
		break;
	    case TYPE_RETRYCANCEL:
		paramCFStringRec.defaultText = CFSTR("Retry");
		paramCFStringRec.cancelText = CFSTR("Cancel");
		break;
	    case TYPE_YESNO:
		paramCFStringRec.defaultText = CFSTR("Yes");
		paramCFStringRec.cancelText = CFSTR("No");
		break;
	    case TYPE_YESNOCANCEL:
		paramCFStringRec.defaultText = CFSTR("Yes");
		paramCFStringRec.cancelText = CFSTR("No");
		paramCFStringRec.otherText = CFSTR("Cancel");
		paramCFStringRec.cancelButton = kAlertStdAlertOtherButton;
		break;
	    }
	    break;
	}
    }

    if (haveDefaultOption) {
	/*
	 * Any '-default' option needs to know the '-type' option, which is why
	 * we do this here.
	 */

	str = Tcl_GetString(objv[indexDefaultOption + 1]);
	if (Tcl_GetIndexFromObj(interp, objv[indexDefaultOption + 1],
		movableButtonStrings, "value", TCL_EXACT, &defaultButtonIndex)
		!= TCL_OK) {
	    goto end;
	}

	/*
	 * Need to map from "ok" etc. to 1, 2, 3, right to left.
	 */

	defaultNativeButtonIndex =
	buttonIndexAndTypeToNativeButtonIndex[typeIndex][defaultButtonIndex];
	if (defaultNativeButtonIndex == 0) {
	    Tcl_SetObjResult(interp,
		    Tcl_NewStringObj("Illegal default option", -1));
	    goto end;
	}
	paramCFStringRec.defaultButton = defaultNativeButtonIndex;
	if (paramCFStringRec.cancelButton == defaultNativeButtonIndex) {
	    paramCFStringRec.cancelButton = 0;
	}
    }
    ChkErr(SetThemeCursor, kThemeArrowCursor);

    if (haveParentOption) {
	AlertHandlerUserData data;
	static EventHandlerUPP handler = NULL;
	WindowRef windowRef;
	const EventTypeSpec kEvents[] = {
	    {kEventClassCommand, kEventProcessCommand}
	};

	bzero(&data, sizeof(data));
	if (!handler) {
	    handler = NewEventHandlerUPP(AlertHandler);
	}
	windowRef = TkMacOSXDrawableWindow(Tk_WindowId(tkwin));
	if (!windowRef) {
	    goto end;
	}
	err = ChkErr(CreateStandardSheet, alertType, messageTextCF,
		finemessageTextCF, &paramCFStringRec, NULL, &dialogRef);
	if(err != noErr) {
	    goto end;
	}
	data.dialogWindow = GetDialogWindow(dialogRef);
	err = ChkErr(ShowSheetWindow, data.dialogWindow, windowRef);
	if(err != noErr) {
	    DisposeDialog(dialogRef);
	    goto end;
	}
	ChkErr(GetWindowModality, data.dialogWindow, &data.origModality,
		&data.origUnavailWindow);
	ChkErr(SetWindowModality, data.dialogWindow, kWindowModalityAppModal,
		NULL);
	ChkErr(InstallEventHandler, GetWindowEventTarget(data.dialogWindow),
		handler, GetEventTypeCount(kEvents), kEvents, &data,
		&data.handlerRef);
	TkMacOSXTrackingLoop(1);
	ChkErr(RunAppModalLoopForWindow, data.dialogWindow);
	TkMacOSXTrackingLoop(0);
	itemHit = data.buttonIndex;
    } else {
	err = ChkErr(CreateStandardAlert, alertType, messageTextCF,
		finemessageTextCF, &paramCFStringRec, &dialogRef);
	if(err != noErr) {
	    goto end;
	}
	TkMacOSXTrackingLoop(1);
	err = ChkErr(RunStandardAlert, dialogRef, NULL, &itemHit);
	TkMacOSXTrackingLoop(0);
	if (err != noErr) {
	    goto end;
	}
    }
    if (err == noErr) {
	/*
	 * Map 'itemHit' (1, 2, 3) to descriptive text string.
	 */

	int ind = nativeButtonIndexAndTypeToButtonIndex[typeIndex][itemHit];

	Tcl_SetObjResult(interp, Tcl_NewStringObj(movableButtonStrings[ind],
		-1));
	result = TCL_OK;
    }

  end:
    if (finemessageTextCF) {
	CFRelease(finemessageTextCF);
    }
    if (messageTextCF) {
	CFRelease(messageTextCF);
    }
    return result;
}

/*
 *----------------------------------------------------------------------
 *
 * AlertHandler --
 *
 *	Carbon event handler for the Standard Sheet dialog.
 *
 * Results:
 *	OSStatus if event handled or not.
 *
 * Side effects:
 *	May set userData.
 *
 *----------------------------------------------------------------------
 */

OSStatus
AlertHandler(
    EventHandlerCallRef callRef,
    EventRef eventRef,
    void *userData)
{
    AlertHandlerUserData *data = userData;
    HICommand cmd;

    ChkErr(GetEventParameter,eventRef, kEventParamDirectObject, typeHICommand,
	    NULL, sizeof(cmd), NULL, &cmd);
    switch (cmd.commandID) {
    case kHICommandOK:
	data->buttonIndex = 1;
	break;
    case kHICommandCancel:
	data->buttonIndex = 2;
	break;
    case kHICommandOther:
	data->buttonIndex = 3;
	break;
    }
    if (data->buttonIndex) {
	ChkErr(QuitAppModalLoopForWindow, data->dialogWindow);
	ChkErr(RemoveEventHandler, data->handlerRef);
	ChkErr(SetWindowModality, data->dialogWindow,
		data->origModality, data->origUnavailWindow);
    }
    return eventNotHandledErr;
}
