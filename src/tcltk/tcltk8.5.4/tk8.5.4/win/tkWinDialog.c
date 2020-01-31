/*
 * tkWinDialog.c --
 *
 *	Contains the Windows implementation of the common dialog boxes.
 *
 * Copyright (c) 1996-1997 Sun Microsystems, Inc.
 *
 * See the file "license.terms" for information on usage and redistribution of
 * this file, and for a DISCLAIMER OF ALL WARRANTIES.
 *
 * RCS: @(#) $Id: tkWinDialog.c,v 1.50.2.1 2008/04/14 20:59:51 patthoyts Exp $
 *
 */

#include "tkWinInt.h"
#include "tkFileFilter.h"

#include <commdlg.h>		/* includes common dialog functionality */
#ifdef _MSC_VER
#   pragma comment (lib, "comdlg32.lib")
#endif
#include <dlgs.h>		/* includes common dialog template defines */
#include <cderr.h>		/* includes the common dialog error codes */

#include <shlobj.h>		/* includes SHBrowseForFolder */
#ifdef _MSC_VER
#   pragma comment (lib, "shell32.lib")
#endif

/* These needed for compilation with VC++ 5.2 */
#ifndef BIF_EDITBOX
#define BIF_EDITBOX 0x10
#endif

#ifndef BIF_VALIDATE
#define BIF_VALIDATE 0x0020
#endif

#ifndef BFFM_VALIDATEFAILED
#ifdef UNICODE
#define BFFM_VALIDATEFAILED 4
#else
#define BFFM_VALIDATEFAILED 3
#endif
#endif /* BFFM_VALIDATEFAILED */

/*
 * The following structure is used by the new Tk_ChooseDirectoryObjCmd to pass
 * data between it and its callback. Unqiue to Winodws platform.
 */

typedef struct ChooseDirData {
   TCHAR utfInitDir[MAX_PATH];	/* Initial folder to use */
   TCHAR utfRetDir[MAX_PATH];	/* Returned folder to use */
   Tcl_Interp *interp;
   int mustExist;		/* True if file must exist to return from
				 * callback */
} CHOOSEDIRDATA;

typedef struct ThreadSpecificData {
    int debugFlag;		/* Flags whether we should output debugging
				 * information while displaying a builtin
				 * dialog. */
    Tcl_Interp *debugInterp;	/* Interpreter to used for debugging. */
    UINT WM_LBSELCHANGED;	/* Holds a registered windows event used for
				 * communicating between the Directory Chooser
				 * dialog and its hook proc. */
    HHOOK hMsgBoxHook;		/* Hook proc for tk_messageBox and the */
    HICON hSmallIcon;		/* icons used by a parent to be used in */
    HICON hBigIcon;		/* the message box */
} ThreadSpecificData;
static Tcl_ThreadDataKey dataKey;

/*
 * The following structures are used by Tk_MessageBoxCmd() to parse arguments
 * and return results.
 */

static const TkStateMap iconMap[] = {
    {MB_ICONERROR,		"error"},
    {MB_ICONINFORMATION,	"info"},
    {MB_ICONQUESTION,		"question"},
    {MB_ICONWARNING,		"warning"},
    {-1,			NULL}
};

static const TkStateMap typeMap[] = {
    {MB_ABORTRETRYIGNORE,	"abortretryignore"},
    {MB_OK,			"ok"},
    {MB_OKCANCEL,		"okcancel"},
    {MB_RETRYCANCEL,		"retrycancel"},
    {MB_YESNO,			"yesno"},
    {MB_YESNOCANCEL,		"yesnocancel"},
    {-1,			NULL}
};

static const TkStateMap buttonMap[] = {
    {IDABORT,			"abort"},
    {IDRETRY,			"retry"},
    {IDIGNORE,			"ignore"},
    {IDOK,			"ok"},
    {IDCANCEL,			"cancel"},
    {IDNO,			"no"},
    {IDYES,			"yes"},
    {-1,			NULL}
};

static const int buttonFlagMap[] = {
    MB_DEFBUTTON1, MB_DEFBUTTON2, MB_DEFBUTTON3, MB_DEFBUTTON4
};

static const struct {int type; int btnIds[3];} allowedTypes[] = {
    {MB_ABORTRETRYIGNORE,	{IDABORT, IDRETRY,  IDIGNORE}},
    {MB_OK,			{IDOK,	  -1,	    -1	    }},
    {MB_OKCANCEL,		{IDOK,	  IDCANCEL, -1	    }},
    {MB_RETRYCANCEL,		{IDRETRY, IDCANCEL, -1	    }},
    {MB_YESNO,			{IDYES,	  IDNO,	    -1	    }},
    {MB_YESNOCANCEL,		{IDYES,	  IDNO,	    IDCANCEL}}
};

#define NUM_TYPES (sizeof(allowedTypes) / sizeof(allowedTypes[0]))

/*
 * Abstract trivial differences between Win32 and Win64.
 */

#define TkWinGetHInstance(from) \
	((HINSTANCE) GetWindowLongPtr((from), GWLP_HINSTANCE))
#define TkWinGetUserData(from) \
	GetWindowLongPtr((from), GWLP_USERDATA)
#define TkWinSetUserData(to,what) \
	SetWindowLongPtr((to), GWLP_USERDATA, (LPARAM)(what))

/*
 * The value of TK_MULTI_MAX_PATH dictactes how many files can be retrieved
 * with tk_get*File -multiple 1. It must be allocated on the stack, so make it
 * large enough but not too large. - hobbs
 *
 * The data is stored as <dir>\0<file1>\0<file2>\0...<fileN>\0\0. Since
 * MAX_PATH == 260 on Win2K/NT, *40 is ~10Kbytes.
 */

#define TK_MULTI_MAX_PATH	(MAX_PATH*40)

/*
 * The following structure is used to pass information between the directory
 * chooser function, Tk_ChooseDirectoryObjCmd(), and its dialog hook proc.
 */

typedef struct ChooseDir {
    Tcl_Interp *interp;		/* Interp, used only if debug is turned on,
				 * for setting the "tk_dialog" variable. */
    int lastCtrl;		/* Used by hook proc to keep track of last
				 * control that had input focus, so when OK is
				 * pressed we know whether to browse a new
				 * directory or return. */
    int lastIdx;		/* Last item that was selected in directory
				 * browser listbox. */
    TCHAR path[MAX_PATH];	/* On return from choose directory dialog,
				 * holds the selected path. Cannot return
				 * selected path in ofnPtr->lpstrFile because
				 * the default dialog proc stores a '\0' in
				 * it, since, of course, no _file_ was
				 * selected. */
    OPENFILENAME *ofnPtr;	/* pointer to the OFN structure */
} ChooseDir;

/*
 * Definitions of functions used only in this file.
 */

static UINT APIENTRY	ChooseDirectoryValidateProc(HWND hdlg, UINT uMsg,
			    LPARAM wParam, LPARAM lParam);
static UINT CALLBACK	ColorDlgHookProc(HWND hDlg, UINT uMsg, WPARAM wParam,
			    LPARAM lParam);
static int 		GetFileNameA(ClientData clientData,
			    Tcl_Interp *interp, int objc,
			    Tcl_Obj *CONST objv[], int isOpen);
static int 		GetFileNameW(ClientData clientData,
			    Tcl_Interp *interp, int objc,
			    Tcl_Obj *CONST objv[], int isOpen);
static int 		MakeFilter(Tcl_Interp *interp, Tcl_Obj *valuePtr,
			    Tcl_DString *dsPtr, Tcl_Obj *initialPtr,
			    int *index);
static UINT APIENTRY	OFNHookProc(HWND hdlg, UINT uMsg, WPARAM wParam,
			    LPARAM lParam);
static UINT APIENTRY	OFNHookProcW(HWND hdlg, UINT uMsg, WPARAM wParam,
			    LPARAM lParam);
static LRESULT CALLBACK MsgBoxCBTProc(int nCode, WPARAM wParam, LPARAM lParam);
static void		SetTkDialog(ClientData clientData);
static char *		ConvertExternalFilename(Tcl_Encoding encoding,
			    char *filename, Tcl_DString *dsPtr);

/*
 *-------------------------------------------------------------------------
 *
 * EatSpuriousMessageBugFix --
 *
 *	In the file open/save dialog, double clicking on a list item causes
 *	the dialog box to close, but an unwanted WM_LBUTTONUP message is sent
 *	to the window underneath. If the window underneath happens to be a
 *	windows control (eg a button) then it will be activated by accident.
 *
 * 	This problem does not occur in dialog boxes, because windows must do
 * 	some special processing to solve the problem. (separate message
 * 	processing functions are used to cope with keyboard navigation of
 * 	controls.)
 *
 * 	Here is one solution. After returning, we poll the message queue for
 * 	1/4s looking for WM_LBUTTON up messages. If we see one it's consumed.
 * 	If we get a WM_LBUTTONDOWN message, then we exit early, since the user
 * 	must be doing something new. This fix only works for the current
 * 	application, so the problem will still occur if the open dialog
 * 	happens to be over another applications button. However this is a
 * 	fairly rare occurrance.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	Consumes an unwanted BUTTON messages.
 *
 *-------------------------------------------------------------------------
 */

static void
EatSpuriousMessageBugFix(void)
{
    MSG msg;
    DWORD nTime = GetTickCount() + 250;

    while (GetTickCount() < nTime) {
	if (PeekMessage(&msg, 0, WM_LBUTTONDOWN, WM_LBUTTONDOWN, PM_NOREMOVE)){
	    break;
	}
	PeekMessage(&msg, 0, WM_LBUTTONUP, WM_LBUTTONUP, PM_REMOVE);
    }
}

/*
 *-------------------------------------------------------------------------
 *
 * TkWinDialogDebug --
 *
 *	Function to turn on/off debugging support for common dialogs under
 *	windows. The variable "tk_debug" is set to the identifier of the
 *	dialog window when the modal dialog window pops up and it is safe to
 *	send messages to the dialog.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	This variable only makes sense if just one dialog is up at a time.
 *
 *-------------------------------------------------------------------------
 */

void
TkWinDialogDebug(
    int debug)
{
    ThreadSpecificData *tsdPtr = (ThreadSpecificData *)
	    Tcl_GetThreadData(&dataKey, sizeof(ThreadSpecificData));

    tsdPtr->debugFlag = debug;
}

/*
 *-------------------------------------------------------------------------
 *
 * Tk_ChooseColorObjCmd --
 *
 *	This function implements the color dialog box for the Windows
 *	platform. See the user documentation for details on what it does.
 *
 * Results:
 *	See user documentation.
 *
 * Side effects:
 *	A dialog window is created the first time this function is called.
 *	This window is not destroyed and will be reused the next time the
 *	application invokes the "tk_chooseColor" command.
 *
 *-------------------------------------------------------------------------
 */

int
Tk_ChooseColorObjCmd(
    ClientData clientData,	/* Main window associated with interpreter. */
    Tcl_Interp *interp,		/* Current interpreter. */
    int objc,			/* Number of arguments. */
    Tcl_Obj *CONST objv[])	/* Argument objects. */
{
    Tk_Window tkwin, parent;
    HWND hWnd;
    int i, oldMode, winCode, result;
    CHOOSECOLOR chooseColor;
    static int inited = 0;
    static COLORREF dwCustColors[16];
    static long oldColor;		/* the color selected last time */
    static CONST char *optionStrings[] = {
	"-initialcolor", "-parent", "-title", NULL
    };
    enum options {
	COLOR_INITIAL, COLOR_PARENT, COLOR_TITLE
    };

    result = TCL_OK;
    if (inited == 0) {
	/*
	 * dwCustColors stores the custom color which the user can modify. We
	 * store these colors in a static array so that the next time the
	 * color dialog pops up, the same set of custom colors remain in the
	 * dialog.
	 */

	for (i = 0; i < 16; i++) {
	    dwCustColors[i] = RGB(255-i * 10, i, i * 10);
	}
	oldColor = RGB(0xa0, 0xa0, 0xa0);
	inited = 1;
    }

    tkwin = (Tk_Window) clientData;

    parent			= tkwin;
    chooseColor.lStructSize	= sizeof(CHOOSECOLOR);
    chooseColor.hwndOwner	= NULL;
    chooseColor.hInstance	= NULL;
    chooseColor.rgbResult	= oldColor;
    chooseColor.lpCustColors	= dwCustColors;
    chooseColor.Flags		= CC_RGBINIT | CC_FULLOPEN | CC_ENABLEHOOK;
    chooseColor.lCustData	= (LPARAM) NULL;
    chooseColor.lpfnHook	= (LPOFNHOOKPROC) ColorDlgHookProc;
    chooseColor.lpTemplateName	= (LPTSTR) interp;

    for (i = 1; i < objc; i += 2) {
	int index;
	char *string;
	Tcl_Obj *optionPtr, *valuePtr;

	optionPtr = objv[i];
	valuePtr = objv[i + 1];

	if (Tcl_GetIndexFromObj(interp, optionPtr, optionStrings, "option",
		TCL_EXACT, &index) != TCL_OK) {
	    return TCL_ERROR;
	}
	if (i + 1 == objc) {
	    string = Tcl_GetString(optionPtr);
	    Tcl_AppendResult(interp, "value for \"", string, "\" missing",
		    NULL);
	    return TCL_ERROR;
	}

	string = Tcl_GetString(valuePtr);
	switch ((enum options) index) {
	case COLOR_INITIAL: {
	    XColor *colorPtr;

	    colorPtr = Tk_GetColor(interp, tkwin, string);
	    if (colorPtr == NULL) {
		return TCL_ERROR;
	    }
	    chooseColor.rgbResult = RGB(colorPtr->red / 0x100,
		    colorPtr->green / 0x100, colorPtr->blue / 0x100);
	    break;
	}
	case COLOR_PARENT:
	    parent = Tk_NameToWindow(interp, string, tkwin);
	    if (parent == NULL) {
		return TCL_ERROR;
	    }
	    break;
	case COLOR_TITLE:
	    chooseColor.lCustData = (LPARAM) string;
	    break;
	}
    }

    Tk_MakeWindowExist(parent);
    chooseColor.hwndOwner = NULL;
    hWnd = Tk_GetHWND(Tk_WindowId(parent));
    chooseColor.hwndOwner = hWnd;

    oldMode = Tcl_SetServiceMode(TCL_SERVICE_ALL);
    winCode = ChooseColor(&chooseColor);
    (void) Tcl_SetServiceMode(oldMode);

    /*
     * Ensure that hWnd is enabled, because it can happen that we have updated
     * the wrapper of the parent, which causes us to leave this child disabled
     * (Windows loses sync).
     */

    EnableWindow(hWnd, 1);

    /*
     * Clear the interp result since anything may have happened during the
     * modal loop.
     */

    Tcl_ResetResult(interp);

    /*
     * 3. Process the result of the dialog
     */

    if (winCode) {
	/*
	 * User has selected a color
	 */
	char color[100];

	sprintf(color, "#%02x%02x%02x",
		GetRValue(chooseColor.rgbResult),
		GetGValue(chooseColor.rgbResult),
		GetBValue(chooseColor.rgbResult));
	Tcl_AppendResult(interp, color, NULL);
	oldColor = chooseColor.rgbResult;
	result = TCL_OK;
    }

    return result;
}

/*
 *-------------------------------------------------------------------------
 *
 * ColorDlgHookProc --
 *
 *	Provides special handling of messages for the Color common dialog box.
 *	Used to set the title when the dialog first appears.
 *
 * Results:
 *	The return value is 0 if the default dialog box function should handle
 *	the message, non-zero otherwise.
 *
 * Side effects:
 *	Changes the title of the dialog window.
 *
 *----------------------------------------------------------------------
 */

static UINT CALLBACK
ColorDlgHookProc(
    HWND hDlg,			/* Handle to the color dialog. */
    UINT uMsg,			/* Type of message. */
    WPARAM wParam,		/* First message parameter. */
    LPARAM lParam)		/* Second message parameter. */
{
    ThreadSpecificData *tsdPtr = (ThreadSpecificData *)
	    Tcl_GetThreadData(&dataKey, sizeof(ThreadSpecificData));
    const char *title;
    CHOOSECOLOR *ccPtr;

    if (WM_INITDIALOG == uMsg) {

	/*
	 * Set the title string of the dialog.
	 */

	ccPtr = (CHOOSECOLOR *) lParam;
	title = (const char *) ccPtr->lCustData;

	if ((title != NULL) && (title[0] != '\0')) {
	    Tcl_DString ds;

	    (*tkWinProcs->setWindowText)(hDlg,
		    Tcl_WinUtfToTChar(title, -1, &ds));
	    Tcl_DStringFree(&ds);
	}
	if (tsdPtr->debugFlag) {
	    tsdPtr->debugInterp = (Tcl_Interp *) ccPtr->lpTemplateName;
	    Tcl_DoWhenIdle(SetTkDialog, (ClientData) hDlg);
	}
	return TRUE;
    }
    return FALSE;
}

/*
 *----------------------------------------------------------------------
 *
 * Tk_GetOpenFileCmd --
 *
 *	This function implements the "open file" dialog box for the Windows
 *	platform. See the user documentation for details on what it does.
 *
 * Results:
 *	See user documentation.
 *
 * Side effects:
 *	A dialog window is created the first this function is called.
 *
 *----------------------------------------------------------------------
 */

int
Tk_GetOpenFileObjCmd(
    ClientData clientData,	/* Main window associated with interpreter. */
    Tcl_Interp *interp,		/* Current interpreter. */
    int objc,			/* Number of arguments. */
    Tcl_Obj *CONST objv[])	/* Argument objects. */
{
    if (TkWinGetPlatformId() == VER_PLATFORM_WIN32_NT) {
	return GetFileNameW(clientData, interp, objc, objv, 1);
    } else {
	return GetFileNameA(clientData, interp, objc, objv, 1);
    }
}

/*
 *----------------------------------------------------------------------
 *
 * Tk_GetSaveFileCmd --
 *
 *	Same as Tk_GetOpenFileCmd but opens a "save file" dialog box
 *	instead
 *
 * Results:
 *	Same as Tk_GetOpenFileCmd.
 *
 * Side effects:
 *	Same as Tk_GetOpenFileCmd.
 *
 *----------------------------------------------------------------------
 */

int
Tk_GetSaveFileObjCmd(
    ClientData clientData,	/* Main window associated with interpreter. */
    Tcl_Interp *interp,		/* Current interpreter. */
    int objc,			/* Number of arguments. */
    Tcl_Obj *CONST objv[])	/* Argument objects. */
{
    if (TkWinGetPlatformId() == VER_PLATFORM_WIN32_NT) {
	return GetFileNameW(clientData, interp, objc, objv, 0);
    } else {
	return GetFileNameA(clientData, interp, objc, objv, 0);
    }
}

/*
 *----------------------------------------------------------------------
 *
 * GetFileNameW --
 *
 *	Calls GetOpenFileName() or GetSaveFileName().
 *
 * Results:
 *	See user documentation.
 *
 * Side effects:
 *	See user documentation.
 *
 *----------------------------------------------------------------------
 */

static int
GetFileNameW(
    ClientData clientData,	/* Main window associated with interpreter. */
    Tcl_Interp *interp,		/* Current interpreter. */
    int objc,			/* Number of arguments. */
    Tcl_Obj *CONST objv[],	/* Argument objects. */
    int open)			/* 1 to call GetOpenFileName(), 0 to call
				 * GetSaveFileName(). */
{
    OPENFILENAMEW ofn;
    WCHAR file[TK_MULTI_MAX_PATH];
    int filterIndex, result, winCode, oldMode, i, multi = 0;
    char *extension, *filter, *title;
    Tk_Window tkwin;
    HWND hWnd;
    Tcl_Obj *filterObj, *initialTypeObj, *typeVariableObj;
    Tcl_DString utfFilterString, utfDirString;
    Tcl_DString extString, filterString, dirString, titleString;
    Tcl_Encoding unicodeEncoding = TkWinGetUnicodeEncoding();
    ThreadSpecificData *tsdPtr = (ThreadSpecificData *)
	    Tcl_GetThreadData(&dataKey, sizeof(ThreadSpecificData));
    static CONST char *saveOptionStrings[] = {
	"-defaultextension", "-filetypes", "-initialdir", "-initialfile",
	"-parent", "-title", "-typevariable", NULL
    };
    static CONST char *openOptionStrings[] = {
	"-defaultextension", "-filetypes", "-initialdir", "-initialfile",
	"-multiple", "-parent", "-title", "-typevariable", NULL
    };
    CONST char **optionStrings;

    enum options {
	FILE_DEFAULT,	FILE_TYPES,	FILE_INITDIR,	FILE_INITFILE,
	FILE_MULTIPLE,	FILE_PARENT,	FILE_TITLE,     FILE_TYPEVARIABLE
    };

    result = TCL_ERROR;
    file[0] = '\0';

    /*
     * Parse the arguments.
     */

    extension = NULL;
    filter = NULL;
    Tcl_DStringInit(&utfFilterString);
    Tcl_DStringInit(&utfDirString);
    tkwin = (Tk_Window) clientData;
    title = NULL;
    filterObj = NULL;
    typeVariableObj = NULL;
    initialTypeObj = NULL;

    if (open) {
	optionStrings = openOptionStrings;
    } else {
	optionStrings = saveOptionStrings;
    }

    for (i = 1; i < objc; i += 2) {
	int index;
	char *string;
	Tcl_Obj *optionPtr, *valuePtr;

	optionPtr = objv[i];
	valuePtr = objv[i + 1];

	if (Tcl_GetIndexFromObj(interp, optionPtr, optionStrings,
		"option", 0, &index) != TCL_OK) {
	    goto end;
	}

	/*
	 * We want to maximize code sharing between the open and save file
	 * dialog implementations; in particular, the switch statement below.
	 * We use different sets of option strings from the GetIndexFromObj
	 * call above, but a single enumeration for both. The save file dialog
	 * doesn't support -multiple, but it falls in the middle of the
	 * enumeration. Ultimately, this means that when the index found by
	 * GetIndexFromObj is >= FILE_MULTIPLE, when doing a save file dialog,
	 * we have to increment the index, so that it matches the open file
	 * dialog enumeration.
	 */

	if (!open && index >= FILE_MULTIPLE) {
	    index++;
	}
	if (i + 1 == objc) {
	    string = Tcl_GetString(optionPtr);
	    Tcl_AppendResult(interp, "value for \"", string, "\" missing",
		    NULL);
	    goto end;
	}

	string = Tcl_GetString(valuePtr);
	switch ((enum options) index) {
	case FILE_DEFAULT:
	    if (string[0] == '.') {
		string++;
	    }
	    extension = string;
	    break;
	case FILE_TYPES:
	    filterObj = valuePtr;
	    break;
	case FILE_INITDIR:
	    Tcl_DStringFree(&utfDirString);
	    if (Tcl_TranslateFileName(interp, string,
		    &utfDirString) == NULL) {
		goto end;
	    }
	    break;
	case FILE_INITFILE: {
	    Tcl_DString ds;

	    if (Tcl_TranslateFileName(interp, string, &ds) == NULL) {
		goto end;
	    }
	    Tcl_UtfToExternal(NULL, unicodeEncoding, Tcl_DStringValue(&ds),
		    Tcl_DStringLength(&ds), 0, NULL, (char *) file,
		    sizeof(file), NULL, NULL, NULL);
	    Tcl_DStringFree(&ds);
	    break;
	}
	case FILE_MULTIPLE:
	    if (Tcl_GetBooleanFromObj(interp, valuePtr, &multi) != TCL_OK) {
		return TCL_ERROR;
	    }
	    break;
	case FILE_PARENT:
	    tkwin = Tk_NameToWindow(interp, string, tkwin);
	    if (tkwin == NULL) {
		goto end;
	    }
	    break;
	case FILE_TITLE:
	    title = string;
	    break;
	case FILE_TYPEVARIABLE:
	    typeVariableObj = valuePtr;
	    initialTypeObj = Tcl_ObjGetVar2(interp, typeVariableObj, NULL, 0);
	    break;
	}
    }

    if (MakeFilter(interp, filterObj, &utfFilterString, initialTypeObj,
		    &filterIndex) != TCL_OK) {
	goto end;
    }
    filter = Tcl_DStringValue(&utfFilterString);

    Tk_MakeWindowExist(tkwin);
    hWnd = Tk_GetHWND(Tk_WindowId(tkwin));

    ZeroMemory(&ofn, sizeof(OPENFILENAMEW));
    ofn.lStructSize = sizeof(OPENFILENAMEW);
    ofn.hwndOwner = hWnd;
    ofn.hInstance = TkWinGetHInstance(ofn.hwndOwner);
    ofn.lpstrFile = (WCHAR *) file;
    ofn.nMaxFile = TK_MULTI_MAX_PATH;
    ofn.Flags = OFN_HIDEREADONLY | OFN_PATHMUSTEXIST | OFN_NOCHANGEDIR
	    | OFN_EXPLORER;
    ofn.lpfnHook = (LPOFNHOOKPROC) OFNHookProcW;
    ofn.lCustData = (LPARAM) interp;

    if (open != 0) {
	ofn.Flags |= OFN_FILEMUSTEXIST;
    } else {
	ofn.Flags |= OFN_OVERWRITEPROMPT;
    }

    if (tsdPtr->debugFlag != 0) {
	ofn.Flags |= OFN_ENABLEHOOK;
    }

    if (multi != 0) {
	ofn.Flags |= OFN_ALLOWMULTISELECT;
    }

    if (extension != NULL) {
	Tcl_UtfToExternalDString(unicodeEncoding, extension, -1, &extString);
	ofn.lpstrDefExt = (WCHAR *) Tcl_DStringValue(&extString);
    }

    Tcl_UtfToExternalDString(unicodeEncoding,
	    Tcl_DStringValue(&utfFilterString),
	    Tcl_DStringLength(&utfFilterString), &filterString);
    ofn.lpstrFilter = (WCHAR *) Tcl_DStringValue(&filterString);
    ofn.nFilterIndex = filterIndex;

    if (Tcl_DStringValue(&utfDirString)[0] != '\0') {
	Tcl_UtfToExternalDString(unicodeEncoding,
		Tcl_DStringValue(&utfDirString),
		Tcl_DStringLength(&utfDirString), &dirString);
    } else {
	/*
	 * NT 5.0 changed the meaning of lpstrInitialDir, so we have to ensure
	 * that we set the [pwd] if the user didn't specify anything else.
	 */

	Tcl_DString cwd;

	Tcl_DStringFree(&utfDirString);
	if ((Tcl_GetCwd(interp, &utfDirString) == NULL) ||
		(Tcl_TranslateFileName(interp,
			Tcl_DStringValue(&utfDirString), &cwd) == NULL)) {
	    Tcl_ResetResult(interp);
	} else {
	    Tcl_UtfToExternalDString(unicodeEncoding, Tcl_DStringValue(&cwd),
		    Tcl_DStringLength(&cwd), &dirString);
	}
	Tcl_DStringFree(&cwd);
    }
    ofn.lpstrInitialDir = (WCHAR *) Tcl_DStringValue(&dirString);

    if (title != NULL) {
	Tcl_UtfToExternalDString(unicodeEncoding, title, -1, &titleString);
	ofn.lpstrTitle = (WCHAR *) Tcl_DStringValue(&titleString);
    }

    /*
     * Popup the dialog.
     */

    oldMode = Tcl_SetServiceMode(TCL_SERVICE_ALL);
    if (open != 0) {
	winCode = GetOpenFileNameW(&ofn);
    } else {
	winCode = GetSaveFileNameW(&ofn);
    }
    Tcl_SetServiceMode(oldMode);
    EatSpuriousMessageBugFix();

    /*
     * Ensure that hWnd is enabled, because it can happen that we have updated
     * the wrapper of the parent, which causes us to leave this child disabled
     * (Windows loses sync).
     */

    EnableWindow(hWnd, 1);

    /*
     * Clear the interp result since anything may have happened during the
     * modal loop.
     */

    Tcl_ResetResult(interp);

    /*
     * Process the results.
     */

    if (winCode != 0) {
	if (ofn.Flags & OFN_ALLOWMULTISELECT) {
	    /*
	     * The result in custData->szFile contains many items, separated
	     * with null characters. It is terminated with two nulls in a row.
	     * The first element is the directory path.
	     */

	    WCHAR *files;
	    Tcl_DString dirBuf;
	    Tcl_Obj *returnList;
	    int count = 0;

	    returnList = Tcl_NewObj();
	    Tcl_IncrRefCount(returnList);

	    files = ofn.lpstrFile;

	    /*
	     * Get directory.
	     */

	    (void) ConvertExternalFilename(unicodeEncoding, (char *) files,
		    &dirBuf);

	    while (*files != '\0') {
		while (*files != '\0') {
		    files++;
		}
		files++;
		if (*files != '\0') {
		    Tcl_Obj *fullnameObj;
		    Tcl_DString filenameBuf;

		    count++;
		    (void) ConvertExternalFilename(unicodeEncoding,
			    (char *) files, &filenameBuf);

		    fullnameObj = Tcl_NewStringObj(Tcl_DStringValue(&dirBuf),
			    Tcl_DStringLength(&dirBuf));
		    Tcl_AppendToObj(fullnameObj, "/", -1);
		    Tcl_AppendToObj(fullnameObj, Tcl_DStringValue(&filenameBuf),
			    Tcl_DStringLength(&filenameBuf));
		    Tcl_DStringFree(&filenameBuf);
		    Tcl_ListObjAppendElement(NULL, returnList, fullnameObj);
		}
	    }

	    if (count == 0) {
		/*
		 * Only one file was returned.
		 */

		Tcl_ListObjAppendElement(NULL, returnList,
			Tcl_NewStringObj(Tcl_DStringValue(&dirBuf),
				Tcl_DStringLength(&dirBuf)));
	    }
	    Tcl_SetObjResult(interp, returnList);
	    Tcl_DecrRefCount(returnList);
	    Tcl_DStringFree(&dirBuf);
	} else {
	    Tcl_DString ds;

	    Tcl_AppendResult(interp, ConvertExternalFilename(unicodeEncoding,
		    (char *) ofn.lpstrFile, &ds), NULL);
	    Tcl_DStringFree(&ds);
	}
	if ((ofn.nFilterIndex > 0) &&
		Tcl_GetCharLength(Tcl_GetObjResult(interp)) > 0 &&
		typeVariableObj && filterObj) {
	    int listObjc, count;
	    Tcl_Obj **listObjv = NULL;
	    Tcl_Obj **typeInfo = NULL;
	    if (Tcl_ListObjGetElements(interp, filterObj,
			    &listObjc, &listObjv) != TCL_OK) {
		result = TCL_ERROR;
	    } else if (Tcl_ListObjGetElements(interp,
			    listObjv[ofn.nFilterIndex - 1],
			    &count, &typeInfo) != TCL_OK) {
		result = TCL_ERROR;
	    } else {
		Tcl_ObjSetVar2(interp, typeVariableObj, NULL, typeInfo[0], 0);
	    }
	}
	result = TCL_OK;
    } else {
	/*
	 * Use the CommDlgExtendedError() function to retrieve the error code.
	 * This function can return one of about two dozen codes; most of
	 * these indicate some sort of gross system failure (insufficient
	 * memory, bad window handles, etc.). Most of the error codes will be
	 * ignored; as we find we want more specific error messages for
	 * particular errors, we can extend the code as needed.
	 *
	 * We could also check for FNERR_BUFFERTOOSMALL, but we can't really
	 * do anything about it when it happens.
	 */

	if (CommDlgExtendedError() == FNERR_INVALIDFILENAME) {
	    Tcl_DString ds;

	    Tcl_SetResult(interp, "invalid filename \"", TCL_STATIC);
	    Tcl_AppendResult(interp, ConvertExternalFilename(unicodeEncoding,
		    (char *) ofn.lpstrFile, &ds), "\"", NULL);
	    Tcl_DStringFree(&ds);
	} else {
	    result = TCL_OK;
	}
    }

    if (ofn.lpstrTitle != NULL) {
	Tcl_DStringFree(&titleString);
    }
    if (ofn.lpstrInitialDir != NULL) {
	Tcl_DStringFree(&dirString);
    }
    Tcl_DStringFree(&filterString);
    if (ofn.lpstrDefExt != NULL) {
	Tcl_DStringFree(&extString);
    }

  end:
    Tcl_DStringFree(&utfDirString);
    Tcl_DStringFree(&utfFilterString);

    return result;
}

/*
 *-------------------------------------------------------------------------
 *
 * OFNHookProcW --
 *
 *	Hook function called only if debugging is turned on. Sets the
 *	"tk_dialog" variable when the dialog is ready to receive messages.
 *
 * Results:
 *	Returns 0 to allow default processing of messages to occur.
 *
 * Side effects:
 *	None.
 *
 *-------------------------------------------------------------------------
 */

static UINT APIENTRY
OFNHookProcW(
    HWND hdlg,			/* Handle to child dialog window. */
    UINT uMsg,			/* Message identifier */
    WPARAM wParam,		/* Message parameter */
    LPARAM lParam)		/* Message parameter */
{
    ThreadSpecificData *tsdPtr = (ThreadSpecificData *)
	    Tcl_GetThreadData(&dataKey, sizeof(ThreadSpecificData));
    OPENFILENAMEW *ofnPtr;

    if (uMsg == WM_INITDIALOG) {
	TkWinSetUserData(hdlg, lParam);
    } else if (uMsg == WM_WINDOWPOSCHANGED) {
	/*
	 * This message is delivered at the right time to enable Tk to set the
	 * debug information. Unhooks itself so it won't set the debug
	 * information every time it gets a WM_WINDOWPOSCHANGED message.
	 */

	ofnPtr = (OPENFILENAMEW *) TkWinGetUserData(hdlg);
	if (ofnPtr != NULL) {
	    hdlg = GetParent(hdlg);
	    tsdPtr->debugInterp = (Tcl_Interp *) ofnPtr->lCustData;
	    Tcl_DoWhenIdle(SetTkDialog, (ClientData) hdlg);
	    TkWinSetUserData(hdlg, NULL);
	}
    }
    return 0;
}

/*
 *----------------------------------------------------------------------
 *
 * GetFileNameA --
 *
 *	Calls GetOpenFileName() or GetSaveFileName().
 *
 * Results:
 *	See user documentation.
 *
 * Side effects:
 *	See user documentation.
 *
 *----------------------------------------------------------------------
 */

static int
GetFileNameA(
    ClientData clientData,	/* Main window associated with interpreter. */
    Tcl_Interp *interp,		/* Current interpreter. */
    int objc,			/* Number of arguments. */
    Tcl_Obj *CONST objv[],	/* Argument objects. */
    int open)			/* 1 to call GetOpenFileName(), 0 to call
				 * GetSaveFileName(). */
{
    OPENFILENAME ofn;
    TCHAR file[TK_MULTI_MAX_PATH], savePath[MAX_PATH];
    int filterIndex, result, winCode, oldMode, i, multi = 0;
    char *extension, *filter, *title;
    Tk_Window tkwin;
    HWND hWnd;
    Tcl_Obj *filterObj, *initialTypeObj, *typeVariableObj;
    Tcl_DString utfFilterString, utfDirString;
    Tcl_DString extString, filterString, dirString, titleString;
    ThreadSpecificData *tsdPtr = (ThreadSpecificData *)
	    Tcl_GetThreadData(&dataKey, sizeof(ThreadSpecificData));
    static CONST char *saveOptionStrings[] = {
	"-defaultextension", "-filetypes", "-initialdir", "-initialfile",
	"-parent", "-title", "-typevariable", NULL
    };
    static CONST char *openOptionStrings[] = {
	"-defaultextension", "-filetypes", "-initialdir", "-initialfile",
	"-multiple", "-parent", "-title", "-typevariable", NULL
    };
    CONST char **optionStrings;

    enum options {
	FILE_DEFAULT,	FILE_TYPES,	FILE_INITDIR,	FILE_INITFILE,
	FILE_MULTIPLE,	FILE_PARENT,	FILE_TITLE, FILE_TYPEVARIABLE
    };

    result = TCL_ERROR;
    file[0] = '\0';

    /*
     * Parse the arguments.
     */

    extension = NULL;
    filter = NULL;
    Tcl_DStringInit(&utfFilterString);
    Tcl_DStringInit(&utfDirString);
    tkwin = (Tk_Window) clientData;
    title = NULL;
    filterObj = NULL;
    typeVariableObj = NULL;
    initialTypeObj = NULL;

    if (open) {
	optionStrings = openOptionStrings;
    } else {
	optionStrings = saveOptionStrings;
    }

    for (i = 1; i < objc; i += 2) {
	int index;
	char *string;
	Tcl_Obj *optionPtr, *valuePtr;

	optionPtr = objv[i];
	valuePtr = objv[i + 1];

	if (Tcl_GetIndexFromObj(interp, optionPtr, optionStrings,
		"option", 0, &index) != TCL_OK) {
	    goto end;
	}

	/*
	 * We want to maximize code sharing between the open and save file
	 * dialog implementations; in particular, the switch statement below.
	 * We use different sets of option strings from the GetIndexFromObj
	 * call above, but a single enumeration for both. The save file dialog
	 * doesn't support -multiple, but it falls in the middle of the
	 * enumeration. Ultimately, this means that when the index found by
	 * GetIndexFromObj is >= FILE_MULTIPLE, when doing a save file dialog,
	 * we have to increment the index, so that it matches the open file
	 * dialog enumeration.
	 */

	if (!open && index >= FILE_MULTIPLE) {
	    index++;
	}
	if (i + 1 == objc) {
	    string = Tcl_GetString(optionPtr);
	    Tcl_AppendResult(interp, "value for \"", string, "\" missing",
		    NULL);
	    goto end;
	}

	string = Tcl_GetString(valuePtr);
	switch ((enum options) index) {
	case FILE_DEFAULT:
	    if (string[0] == '.') {
		string++;
	    }
	    extension = string;
	    break;
	case FILE_TYPES:
	    filterObj = valuePtr;
	    break;
	case FILE_INITDIR:
	    Tcl_DStringFree(&utfDirString);
	    if (Tcl_TranslateFileName(interp, string, &utfDirString) == NULL) {
		goto end;
	    }
	    break;
	case FILE_INITFILE: {
	    Tcl_DString ds;

	    if (Tcl_TranslateFileName(interp, string, &ds) == NULL) {
		goto end;
	    }
	    Tcl_UtfToExternal(NULL, NULL, Tcl_DStringValue(&ds),
		    Tcl_DStringLength(&ds), 0, NULL, (char *) file,
		    sizeof(file), NULL, NULL, NULL);
	    Tcl_DStringFree(&ds);
	    break;
	}
	case FILE_MULTIPLE:
	    if (Tcl_GetBooleanFromObj(interp, valuePtr, &multi) != TCL_OK) {
		return TCL_ERROR;
	    }
	    break;
	case FILE_PARENT:
	    tkwin = Tk_NameToWindow(interp, string, tkwin);
	    if (tkwin == NULL) {
		goto end;
	    }
	    break;
	case FILE_TITLE:
	    title = string;
	    break;
	case FILE_TYPEVARIABLE:
	    typeVariableObj = valuePtr;
	    initialTypeObj = Tcl_ObjGetVar2(interp, typeVariableObj, NULL, 0);
	    break;
	}
    }

    if (MakeFilter(interp, filterObj, &utfFilterString, initialTypeObj,
		    &filterIndex) != TCL_OK) {
	goto end;
    }
    filter = Tcl_DStringValue(&utfFilterString);

    Tk_MakeWindowExist(tkwin);
    hWnd = Tk_GetHWND(Tk_WindowId(tkwin));

    ofn.lStructSize = sizeof(ofn);
    ofn.hwndOwner = hWnd;
    ofn.hInstance = TkWinGetHInstance(ofn.hwndOwner);
    ofn.lpstrFilter = NULL;
    ofn.lpstrCustomFilter = NULL;
    ofn.nMaxCustFilter = 0;
    ofn.nFilterIndex = 0;
    ofn.lpstrFile = (LPTSTR) file;
    ofn.nMaxFile = TK_MULTI_MAX_PATH;
    ofn.lpstrFileTitle = NULL;
    ofn.nMaxFileTitle = 0;
    ofn.lpstrInitialDir = NULL;
    ofn.lpstrTitle = NULL;
    ofn.Flags = OFN_HIDEREADONLY | OFN_PATHMUSTEXIST | OFN_NOCHANGEDIR
	    | OFN_EXPLORER;
    ofn.nFileOffset = 0;
    ofn.nFileExtension = 0;
    ofn.lpstrDefExt = NULL;
    ofn.lpfnHook = (LPOFNHOOKPROC) OFNHookProc;
    ofn.lCustData = (LPARAM) interp;
    ofn.lpTemplateName = NULL;

    if (open != 0) {
	ofn.Flags |= OFN_FILEMUSTEXIST;
    } else {
	ofn.Flags |= OFN_OVERWRITEPROMPT;
    }

    if (tsdPtr->debugFlag != 0) {
	ofn.Flags |= OFN_ENABLEHOOK;
    }

    if (multi != 0) {
	ofn.Flags |= OFN_ALLOWMULTISELECT;
    }

    if (extension != NULL) {
	Tcl_UtfToExternalDString(NULL, extension, -1, &extString);
	ofn.lpstrDefExt = (LPTSTR) Tcl_DStringValue(&extString);
    }
    Tcl_UtfToExternalDString(NULL, Tcl_DStringValue(&utfFilterString),
	    Tcl_DStringLength(&utfFilterString), &filterString);
    ofn.lpstrFilter = (LPTSTR) Tcl_DStringValue(&filterString);

    if (Tcl_DStringValue(&utfDirString)[0] != '\0') {
	Tcl_UtfToExternalDString(NULL, Tcl_DStringValue(&utfDirString),
		Tcl_DStringLength(&utfDirString), &dirString);
    } else {
	/*
	 * NT 5.0 changed the meaning of lpstrInitialDir, so we have to ensure
	 * that we set the [pwd] if the user didn't specify anything else.
	 */

	Tcl_DString cwd;

	Tcl_DStringFree(&utfDirString);
	if ((Tcl_GetCwd(interp, &utfDirString) == NULL) ||
		(Tcl_TranslateFileName(interp,
			Tcl_DStringValue(&utfDirString), &cwd) == NULL)) {
	    Tcl_ResetResult(interp);
	} else {
	    Tcl_UtfToExternalDString(NULL, Tcl_DStringValue(&cwd),
		    Tcl_DStringLength(&cwd), &dirString);
	}
	Tcl_DStringFree(&cwd);
    }
    ofn.lpstrInitialDir = (LPTSTR) Tcl_DStringValue(&dirString);

    if (title != NULL) {
	Tcl_UtfToExternalDString(NULL, title, -1, &titleString);
	ofn.lpstrTitle = (LPTSTR) Tcl_DStringValue(&titleString);
    }

    /*
     * Popup the dialog.
     */

    GetCurrentDirectory(MAX_PATH, savePath);
    oldMode = Tcl_SetServiceMode(TCL_SERVICE_ALL);
    if (open != 0) {
	winCode = GetOpenFileName(&ofn);
    } else {
	winCode = GetSaveFileName(&ofn);
    }
    Tcl_SetServiceMode(oldMode);
    EatSpuriousMessageBugFix();
    SetCurrentDirectory(savePath);

    /*
     * Ensure that hWnd is enabled, because it can happen that we have updated
     * the wrapper of the parent, which causes us to leave this child disabled
     * (Windows loses sync).
     */

    EnableWindow(hWnd, 1);

    /*
     * Clear the interp result since anything may have happened during the
     * modal loop.
     */

    Tcl_ResetResult(interp);

    /*
     * Process the results.
     */

    if (winCode != 0) {
	if (ofn.Flags & OFN_ALLOWMULTISELECT) {
	    /*
	     * The result in custData->szFile contains many items, separated
	     * with null characters. It is terminated with two nulls in a row.
	     * The first element is the directory path (if multiple files are
	     * selected) or the only returned file (if only a single file has
	     * been chosen).
	     */

	    char *files;
	    Tcl_DString ds;
	    Tcl_Obj *returnList;
	    int count = 0;

	    returnList = Tcl_NewObj();
	    Tcl_IncrRefCount(returnList);

	    files = ofn.lpstrFile;

	    /*
	     * Get directory.
	     */

	    (void) ConvertExternalFilename(NULL, (char *) files, &ds);

	    while (*files != '\0') {
		while (*files != '\0') {
		    files++;
		}
		files++;
		if (*files != '\0') {
		    Tcl_Obj *fullnameObj;
		    Tcl_DString filename;

		    count++;
		    (void) ConvertExternalFilename(NULL, (char *) files,
			    &filename);
		    fullnameObj = Tcl_NewStringObj(Tcl_DStringValue(&ds),
			    Tcl_DStringLength(&ds));
		    Tcl_AppendToObj(fullnameObj, "/", -1);
		    Tcl_AppendToObj(fullnameObj, Tcl_DStringValue(&filename),
			    Tcl_DStringLength(&filename));
		    Tcl_DStringFree(&filename);
		    Tcl_ListObjAppendElement(NULL, returnList, fullnameObj);
		}
	    }
	    if (count == 0) {
		/*
		 * Only one file was returned.
		 */

		Tcl_ListObjAppendElement(NULL, returnList, Tcl_NewStringObj(
			Tcl_DStringValue(&ds), Tcl_DStringLength(&ds)));
	    }
	    Tcl_SetObjResult(interp, returnList);
	    Tcl_DecrRefCount(returnList);
	    Tcl_DStringFree(&ds);
	} else {
	    Tcl_DString ds;

	    Tcl_AppendResult(interp, ConvertExternalFilename(NULL,
		    (char *) ofn.lpstrFile, &ds), NULL);
	    Tcl_DStringFree(&ds);
	}
	if ((ofn.nFilterIndex > 0) &&
		(Tcl_GetCharLength(Tcl_GetObjResult(interp)) > 0) &&
		typeVariableObj && filterObj) {
	    int listObjc, count;
	    Tcl_Obj **listObjv = NULL;
	    Tcl_Obj **typeInfo = NULL;
	    if (Tcl_ListObjGetElements(interp, filterObj,
			    &listObjc, &listObjv) != TCL_OK) {
		result = TCL_ERROR;
	    } else if (Tcl_ListObjGetElements(interp,
			    listObjv[ofn.nFilterIndex - 1],
			    &count, &typeInfo) != TCL_OK) {
		result = TCL_ERROR;
	    } else {
		Tcl_ObjSetVar2(interp, typeVariableObj, NULL, typeInfo[0], 0);
	    }
	}
	result = TCL_OK;
    } else {
	/*
	 * Use the CommDlgExtendedError() function to retrieve the error code.
	 * This function can return one of about two dozen codes; most of
	 * these indicate some sort of gross system failure (insufficient
	 * memory, bad window handles, etc.) Most of the error codes will be
	 * ignored; as we find we want specific error messages for particular
	 * errors, we can extend the code as needed.
	 *
	 * We could also check for FNERR_BUFFERTOOSMALL, but we can't really
	 * do anything about it when it happens.
	 */

	if (CommDlgExtendedError() == FNERR_INVALIDFILENAME) {
	    Tcl_DString ds;

	    Tcl_SetResult(interp, "invalid filename \"", TCL_STATIC);
	    Tcl_AppendResult(interp, ConvertExternalFilename(NULL,
		    (char *) ofn.lpstrFile, &ds), "\"", NULL);
	    Tcl_DStringFree(&ds);
	} else {
	    result = TCL_OK;
	}
    }

    if (ofn.lpstrTitle != NULL) {
	Tcl_DStringFree(&titleString);
    }
    if (ofn.lpstrInitialDir != NULL) {
	Tcl_DStringFree(&dirString);
    }
    Tcl_DStringFree(&filterString);
    if (ofn.lpstrDefExt != NULL) {
	Tcl_DStringFree(&extString);
    }

  end:
    Tcl_DStringFree(&utfDirString);
    Tcl_DStringFree(&utfFilterString);

    return result;
}

/*
 *-------------------------------------------------------------------------
 *
 * OFNHookProc --
 *
 *	Hook function called only if debugging is turned on. Sets the
 *	"tk_dialog" variable when the dialog is ready to receive messages.
 *
 * Results:
 *	Returns 0 to allow default processing of messages to occur.
 *
 * Side effects:
 *	None.
 *
 *-------------------------------------------------------------------------
 */

static UINT APIENTRY
OFNHookProc(
    HWND hdlg,			/* handle to child dialog window */
    UINT uMsg,			/* message identifier */
    WPARAM wParam,		/* message parameter */
    LPARAM lParam)		/* message parameter */
{
    ThreadSpecificData *tsdPtr = (ThreadSpecificData *)
	    Tcl_GetThreadData(&dataKey, sizeof(ThreadSpecificData));
    OPENFILENAME *ofnPtr;

    if (uMsg == WM_INITDIALOG) {
	TkWinSetUserData(hdlg, lParam);
    } else if (uMsg == WM_WINDOWPOSCHANGED) {
	/*
	 * This message is delivered at the right time to both old-style and
	 * explorer-style hook procs to enable Tk to set the debug
	 * information. Unhooks itself so it won't set the debug information
	 * every time it gets a WM_WINDOWPOSCHANGED message.
	 */

	ofnPtr = (OPENFILENAME *) TkWinGetUserData(hdlg);
	if (ofnPtr != NULL) {
	    if (ofnPtr->Flags & OFN_EXPLORER) {
		hdlg = GetParent(hdlg);
	    }
	    tsdPtr->debugInterp = (Tcl_Interp *) ofnPtr->lCustData;
	    Tcl_DoWhenIdle(SetTkDialog, (ClientData) hdlg);
	    TkWinSetUserData(hdlg, NULL);
	}
    }
    return 0;
}

/*
 *----------------------------------------------------------------------
 *
 * MakeFilter --
 *
 *	Allocate a buffer to store the filters in a format understood by
 *	Windows.
 *
 * Results:
 *	A standard TCL return value.
 *
 * Side effects:
 *	ofnPtr->lpstrFilter is modified.
 *
 *----------------------------------------------------------------------
 */

static int
MakeFilter(
    Tcl_Interp *interp,		/* Current interpreter. */
    Tcl_Obj *valuePtr,		/* Value of the -filetypes option */
    Tcl_DString *dsPtr,		/* Filled with windows filter string. */
    Tcl_Obj *initialPtr,	/* Initial type name  */
    int *index)			/* Index of initial type in filter string */
{
    char *filterStr;
    char *p;
    char *initial = NULL;
    int pass;
    int ix = 0; /* index counter */
    FileFilterList flist;
    FileFilter *filterPtr;

    if (initialPtr) {
	initial = Tcl_GetStringFromObj(initialPtr, NULL);
    }
    TkInitFileFilters(&flist);
    if (TkGetFileFilters(interp, &flist, valuePtr, 1) != TCL_OK) {
	return TCL_ERROR;
    }

    if (flist.filters == NULL) {
	/*
	 * Use "All Files (*.*) as the default filter if none is specified
	 */
	char *defaultFilter = "All Files (*.*)";

	p = filterStr = (char*)ckalloc(30 * sizeof(char));

	strcpy(p, defaultFilter);
	p+= strlen(defaultFilter);

	*p++ = '\0';
	*p++ = '*';
	*p++ = '.';
	*p++ = '*';
	*p++ = '\0';
	*p++ = '\0';
	*p = '\0';

    } else {
	int len;

	if (valuePtr == NULL) {
	    len = 0;
	} else {
	    (void) Tcl_GetStringFromObj(valuePtr, &len);
	}

	/*
	 * We format the filetype into a string understood by Windows: {"Text
	 * Documents" {.doc .txt} {TEXT}} becomes "Text Documents
	 * (*.doc,*.txt)\0*.doc;*.txt\0"
	 *
	 * See the Windows OPENFILENAME manual page for details on the filter
	 * string format.
	 */

	/*
	 * Since we may only add asterisks (*) to the filter, we need at most
	 * twice the size of the string to format the filter
	 */

	filterStr = ckalloc((unsigned int) len * 3);

	for (filterPtr = flist.filters, p = filterStr; filterPtr;
		filterPtr = filterPtr->next) {
	    char *sep;
	    FileFilterClause *clausePtr;

	    /*
	     * Check initial index for match, set index.
	     * Filter index is 1 based so increment first
	     */
	    ix++;
	    if (index && initial && (strcmp(initial, filterPtr->name) == 0)) {
		*index = ix;
	    }

	    /*
	     * First, put in the name of the file type.
	     */

	    strcpy(p, filterPtr->name);
	    p+= strlen(filterPtr->name);
	    *p++ = ' ';
	    *p++ = '(';

	    for (pass = 1; pass <= 2; pass++) {
		/*
		 * In the first pass, we format the extensions in the name
		 * field. In the second pass, we format the extensions in the
		 * filter pattern field
		 */

		sep = "";
		for (clausePtr=filterPtr->clauses;clausePtr;
			clausePtr=clausePtr->next) {
		    GlobPattern *globPtr;

		    for (globPtr=clausePtr->patterns; globPtr;
			    globPtr=globPtr->next) {
			strcpy(p, sep);
			p += strlen(sep);
			strcpy(p, globPtr->pattern);
			p += strlen(globPtr->pattern);

			if (pass == 1) {
			    sep = ",";
			} else {
			    sep = ";";
			}
		    }
		}
		if (pass == 1) {
		    *p ++ = ')';
		}
		*p++ = '\0';
	    }
	}

	/*
	 * Windows requires the filter string to be ended by two NULL
	 * characters.
	 */

	*p++ = '\0';
	*p = '\0';
    }

    Tcl_DStringAppend(dsPtr, filterStr, (int) (p - filterStr));
    ckfree((char *) filterStr);

    TkFreeFileFilters(&flist);
    return TCL_OK;
}

/*
 *----------------------------------------------------------------------
 *
 * Tk_ChooseDirectoryObjCmd --
 *
 *	This function implements the "tk_chooseDirectory" dialog box for the
 *	Windows platform. See the user documentation for details on what it
 *	does. Uses the newer SHBrowseForFolder explorer type interface.
 *
 * Results:
 *	See user documentation.
 *
 * Side effects:
 *	A modal dialog window is created. Tcl_SetServiceMode() is called to
 *	allow background events to be processed
 *
 *----------------------------------------------------------------------
 *
 * The function tk_chooseDirectory pops up a dialog box for the user to select
 * a directory. The following option-value pairs are possible as command line
 * arguments:
 *
 * -initialdir dirname
 *
 * Specifies that the directories in directory should be displayed when the
 * dialog pops up. If this parameter is not specified, then the directories in
 * the current working directory are displayed. If the parameter specifies a
 * relative path, the return value will convert the relative path to an
 * absolute path. This option may not always work on the Macintosh. This is
 * not a bug. Rather, the General Controls control panel on the Mac allows the
 * end user to override the application default directory.
 *
 * -parent window
 *
 * Makes window the logical parent of the dialog. The dialog is displayed on
 * top of its parent window.
 *
 * -title titleString
 *
 * Specifies a string to display as the title of the dialog box. If this
 * option is not specified, then a default title will be displayed.
 *
 * -mustexist boolean
 *
 * Specifies whether the user may specify non-existant directories. If this
 * parameter is true, then the user may only select directories that already
 * exist. The default value is false.
 *
 * New Behaviour:
 *
 * - If mustexist = 0 and a user entered folder does not exist, a prompt will
 *   pop-up asking if the user wants another chance to change it. The old
 *   dialog just returned the bogus entry. On mustexist = 1, the entries MUST
 *   exist before exiting the box with OK.
 *
 *   Bugs:
 *
 * - If valid abs directory name is entered into the entry box and Enter
 *   pressed, the box will close returning the name. This is inconsistent when
 *   entering relative names or names with forward slashes, which are
 *   invalidated then corrected in the callback. After correction, the box is
 *   held open to allow further modification by the user.
 *
 * - Not sure how to implement localization of message prompts.
 *
 * - -title is really -message.
 * ToDo:
 * - Fix bugs.
 * - test to see what platforms this really works on. May require v4.71 of
 *   shell32.dll everywhere (what is standard?).
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
    char path[MAX_PATH];
    int oldMode, result, i;
    LPCITEMIDLIST pidl;		/* Returned by browser */
    BROWSEINFO bInfo;		/* Used by browser */
    CHOOSEDIRDATA cdCBData;	/* Structure to pass back and forth */
    LPMALLOC pMalloc;		/* Used by shell */

    Tk_Window tkwin;
    HWND hWnd;
    char *utfTitle;		/* Title for window */
    TCHAR saveDir[MAX_PATH];
    Tcl_DString titleString;	/* UTF Title */
    Tcl_DString initDirString;	/* Initial directory */
    static CONST char *optionStrings[] = {
	"-initialdir", "-mustexist",  "-parent",  "-title", NULL
    };
    enum options {
	DIR_INITIAL,   DIR_EXIST,  DIR_PARENT, FILE_TITLE
    };

    /*
     * Initialize
     */

    result = TCL_ERROR;
    path[0] = '\0';
    utfTitle = NULL;

    ZeroMemory(&cdCBData, sizeof(CHOOSEDIRDATA));
    cdCBData.interp = interp;

    tkwin = (Tk_Window) clientData;

    /*
     * Process the command line options
     */

    for (i = 1; i < objc; i += 2) {
	int index;
	char *string;
	Tcl_Obj *optionPtr, *valuePtr;

	optionPtr = objv[i];
	valuePtr = objv[i + 1];

	if (Tcl_GetIndexFromObj(interp, optionPtr, optionStrings, "option", 0,
		&index) != TCL_OK) {
	    goto cleanup;
	}
	if (i + 1 == objc) {
	    string = Tcl_GetString(optionPtr);
	    Tcl_AppendResult(interp, "value for \"", string, "\" missing",
		    NULL);
	    goto cleanup;
	}

	string = Tcl_GetString(valuePtr);
	switch ((enum options) index) {
	case DIR_INITIAL:
	    if (Tcl_TranslateFileName(interp,string,&initDirString) == NULL) {
		goto cleanup;
	    }
	    string = Tcl_DStringValue(&initDirString);

	    /*
	     * Convert possible relative path to full path to keep dialog
	     * happy.
	     */

	    GetFullPathName(string, MAX_PATH, saveDir, NULL);
	    lstrcpyn(cdCBData.utfInitDir, saveDir, MAX_PATH);
	    Tcl_DStringFree(&initDirString);
	    break;
	case DIR_EXIST:
	    if (Tcl_GetBooleanFromObj(interp, valuePtr,
		    &cdCBData.mustExist) != TCL_OK) {
		goto cleanup;
	    }
	    break;
	case DIR_PARENT:
	    tkwin = Tk_NameToWindow(interp, string, tkwin);
	    if (tkwin == NULL) {
		goto cleanup;
	    }
	    break;
	case FILE_TITLE:
	    utfTitle = string;
	    break;
	}
    }

    /*
     * Get ready to call the browser
     */

    Tk_MakeWindowExist(tkwin);
    hWnd = Tk_GetHWND(Tk_WindowId(tkwin));

    /*
     * Setup the parameters used by SHBrowseForFolder
     */

    bInfo.hwndOwner = hWnd;
    bInfo.pszDisplayName = path;
    bInfo.pidlRoot = NULL;
    if (lstrlen(cdCBData.utfInitDir) == 0) {
	GetCurrentDirectory(MAX_PATH, cdCBData.utfInitDir);
    }
    bInfo.lParam = (LPARAM) &cdCBData;

    if (utfTitle != NULL) {
	Tcl_UtfToExternalDString(NULL, utfTitle, -1, &titleString);
	bInfo.lpszTitle = (LPTSTR) Tcl_DStringValue(&titleString);
    } else {
	bInfo.lpszTitle = "Please choose a directory, then select OK.";
    }

    /*
     * Set flags to add edit box (needs 4.71 Shell DLLs), status text line,
     * validate edit box and
     */

    bInfo.ulFlags = BIF_EDITBOX | BIF_STATUSTEXT | BIF_RETURNFSANCESTORS
	    | BIF_VALIDATE;

    /*
     * Callback to handle events
     */

    bInfo.lpfn = (BFFCALLBACK) ChooseDirectoryValidateProc;

    /*
     * Display dialog in background and process result. We look to give the
     * user a chance to change their mind on an invalid folder if mustexist is
     * 0;
     */

    oldMode = Tcl_SetServiceMode(TCL_SERVICE_ALL);
    GetCurrentDirectory(MAX_PATH, saveDir);
    if (SHGetMalloc(&pMalloc) == NOERROR) {
	pidl = SHBrowseForFolder(&bInfo);

	/*
	 * Null for cancel button or invalid dir, otherwise valid.
	 */

	if (pidl != NULL) {
	    if (!SHGetPathFromIDList(pidl, path)) {
		Tcl_SetResult(interp, "Error: Not a file system folder\n",
			TCL_VOLATILE);
	    };
	    pMalloc->lpVtbl->Free(pMalloc, (void *) pidl);
	} else if (lstrlen(cdCBData.utfRetDir) > 0) {
	    lstrcpy(path, cdCBData.utfRetDir);
	}
	pMalloc->lpVtbl->Release(pMalloc);
    }
    SetCurrentDirectory(saveDir);
    Tcl_SetServiceMode(oldMode);

    /*
     * Ensure that hWnd is enabled, because it can happen that we have updated
     * the wrapper of the parent, which causes us to leave this child disabled
     * (Windows loses sync).
     */

    EnableWindow(hWnd, 1);

    /*
     * Change the pathname to the Tcl "normalized" pathname, where back
     * slashes are used instead of forward slashes
     */

    Tcl_ResetResult(interp);
    if (*path) {
	Tcl_DString ds;

	Tcl_AppendResult(interp, ConvertExternalFilename(NULL, (char *) path,
		&ds), NULL);
	Tcl_DStringFree(&ds);
    }

    result = TCL_OK;

    if (utfTitle != NULL) {
	Tcl_DStringFree(&titleString);
    }

  cleanup:
    return result;
}

/*
 *----------------------------------------------------------------------
 *
 * ChooseDirectoryValidateProc --
 *
 *	Hook function called by the explorer ChooseDirectory dialog when
 *	events occur. It is used to validate the text entry the user may have
 *	entered.
 *
 * Results:
 *	Returns 0 to allow default processing of message, or 1 to
 *	tell default dialog function not to close.
 *
 *----------------------------------------------------------------------
 */

static UINT APIENTRY
ChooseDirectoryValidateProc(
    HWND hwnd,
    UINT message,
    LPARAM lParam,
    LPARAM lpData)
{
    TCHAR selDir[MAX_PATH];
    CHOOSEDIRDATA *chooseDirSharedData;
    Tcl_DString initDirString;
    char string[MAX_PATH];
    ThreadSpecificData *tsdPtr = (ThreadSpecificData *)
	    Tcl_GetThreadData(&dataKey, sizeof(ThreadSpecificData));

    chooseDirSharedData = (CHOOSEDIRDATA *)lpData;

    TkWinSetUserData(hwnd, lpData);

    if (tsdPtr->debugFlag) {
	tsdPtr->debugInterp = (Tcl_Interp *) chooseDirSharedData->interp;
	Tcl_DoWhenIdle(SetTkDialog, (ClientData) hwnd);
    }
    chooseDirSharedData->utfRetDir[0] = '\0';
    switch (message) {
    case BFFM_VALIDATEFAILED:
	/*
	 * First save and check to see if it is a valid path name, if so then
	 * make that path the one shown in the window. Otherwise, it failed
	 * the check and should be treated as such. Use
	 * Set/GetCurrentDirectory which allows relative path names and names
	 * with forward slashes. Use Tcl_TranslateFileName to make sure names
	 * like ~ are converted correctly.
	 */

	if (Tcl_TranslateFileName(chooseDirSharedData->interp,
		(char *)lParam, &initDirString) == NULL) {
	    /*
	     * Should we expose the error (in the interp result) to the user
	     * at this point?
	     */
	    chooseDirSharedData->utfRetDir[0] = '\0';
	    return 1;
	}
	lstrcpyn(string, Tcl_DStringValue(&initDirString), MAX_PATH);
	Tcl_DStringFree(&initDirString);

	if (SetCurrentDirectory((char *)string) == 0) {
	    LPTSTR lpFilePart[MAX_PATH];

	    /*
	     * Get the full path name to the user entry, at this point it
	     * doesn't exist so see if it is supposed to. Otherwise just
	     * return it.
	     */

	    GetFullPathName(string, MAX_PATH,
		    chooseDirSharedData->utfRetDir, /*unused*/ lpFilePart);
	    if (chooseDirSharedData->mustExist) {
		/*
		 * User HAS to select a valid directory.
		 */

		wsprintf(selDir, TEXT("Directory '%.200s' does not exist,\nplease select or enter an existing directory."), chooseDirSharedData->utfRetDir);
		MessageBox(NULL, selDir, NULL, MB_ICONEXCLAMATION|MB_OK);
		chooseDirSharedData->utfRetDir[0] = '\0';
		return 1;
	    }
	} else {
	    /*
	     * Changed to new folder OK, return immediatly with the
	     * current directory in utfRetDir.
	     */
	    GetCurrentDirectory(MAX_PATH, chooseDirSharedData->utfRetDir);
	    return 0;
	}
	return 0;

    case BFFM_SELCHANGED:
	/*
	 * Set the status window to the currently selected path. And enable
	 * the OK button if a file system folder, otherwise disable the OK
	 * button for things like server names. Perhaps a new switch
	 * -enablenonfolders can be used to allow non folders to be selected.
	 *
	 * Not called when user changes edit box directly.
	 */

	if (SHGetPathFromIDList((LPITEMIDLIST) lParam, selDir)) {
	    SendMessage(hwnd, BFFM_SETSTATUSTEXT, 0, (LPARAM) selDir);
	    // enable the OK button
	    SendMessage(hwnd, BFFM_ENABLEOK, 0, (LPARAM) 1);
	    SetCurrentDirectory(selDir);
	} else {
	    // disable the OK button
	    SendMessage(hwnd, BFFM_ENABLEOK, 0, (LPARAM) 0);
	}
	UpdateWindow(hwnd);
	return 1;

    case BFFM_INITIALIZED: {
	/*
	 * Directory browser intializing - tell it where to start from, user
	 * specified parameter.
	 */

	char *initDir = chooseDirSharedData->utfInitDir;

	SetCurrentDirectory(initDir);
	if (*initDir == '\\') {
	    /*
	     * BFFM_SETSELECTION only understands UNC paths as pidls,
	     * so convert path to pidl using IShellFolder interface.
	     */

	    LPMALLOC pMalloc;
	    LPSHELLFOLDER psfFolder;

	    if (SUCCEEDED(SHGetMalloc(&pMalloc))) {
		if (SUCCEEDED(SHGetDesktopFolder(&psfFolder))) {
		    LPITEMIDLIST pidlMain;
		    ULONG ulCount, ulAttr;
		    Tcl_DString ds;

		    Tcl_UtfToExternalDString(TkWinGetUnicodeEncoding(),
			    initDir, -1, &ds);
		    if (SUCCEEDED(psfFolder->lpVtbl->ParseDisplayName(
			    psfFolder, hwnd, NULL, (WCHAR *)
			    Tcl_DStringValue(&ds), &ulCount,&pidlMain,&ulAttr))
			    && (pidlMain != NULL)) {
			SendMessage(hwnd, BFFM_SETSELECTION, FALSE,
				(LPARAM)pidlMain);
			pMalloc->lpVtbl->Free(pMalloc, pidlMain);
		    }
		    psfFolder->lpVtbl->Release(psfFolder);
		    Tcl_DStringFree(&ds);
		}
		pMalloc->lpVtbl->Release(pMalloc);
	    }
	} else {
	    SendMessage(hwnd, BFFM_SETSELECTION, TRUE, (LPARAM)initDir);
	}
	SendMessage(hwnd, BFFM_ENABLEOK, 0, (LPARAM) 1);
	break;
    }

    }
    return 0;
}

/*
 *----------------------------------------------------------------------
 *
 * Tk_MessageBoxObjCmd --
 *
 *	This function implements the MessageBox window for the Windows
 *	platform. See the user documentation for details on what it does.
 *
 * Results:
 *	See user documentation.
 *
 * Side effects:
 *	None. The MessageBox window will be destroy before this function
 *	returns.
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
    Tk_Window tkwin, parent;
    HWND hWnd;
    Tcl_Obj *messageObj, *titleObj, *detailObj, *tmpObj;
    int defaultBtn, icon, type;
    int i, oldMode, winCode;
    UINT flags;
    static CONST char *optionStrings[] = {
	"-default",	"-detail",	"-icon",	"-message",
	"-parent",	"-title",	"-type",	NULL
    };
    enum options {
	MSG_DEFAULT,	MSG_DETAIL,	MSG_ICON,	MSG_MESSAGE,
	MSG_PARENT,	MSG_TITLE,	MSG_TYPE
    };
    ThreadSpecificData *tsdPtr = (ThreadSpecificData *)
	    Tcl_GetThreadData(&dataKey, sizeof(ThreadSpecificData));

    (void) TkWinGetUnicodeEncoding();
    tkwin = (Tk_Window) clientData;

    defaultBtn = -1;
    detailObj = NULL;
    icon = MB_ICONINFORMATION;
    messageObj = NULL;
    parent = tkwin;
    titleObj = NULL;
    type = MB_OK;

    for (i = 1; i < objc; i += 2) {
	int index;
	char *string;
	Tcl_Obj *optionPtr, *valuePtr;

	optionPtr = objv[i];
	valuePtr = objv[i + 1];

	if (Tcl_GetIndexFromObj(interp, optionPtr, optionStrings, "option",
		TCL_EXACT, &index) != TCL_OK) {
	    return TCL_ERROR;
	}
	if (i + 1 == objc) {
	    string = Tcl_GetString(optionPtr);
	    Tcl_AppendResult(interp, "value for \"", string, "\" missing",
		    NULL);
	    return TCL_ERROR;
	}

	switch ((enum options) index) {
	case MSG_DEFAULT:
	    defaultBtn = TkFindStateNumObj(interp, optionPtr, buttonMap,
		    valuePtr);
	    if (defaultBtn < 0) {
		return TCL_ERROR;
	    }
	    break;

	case MSG_DETAIL:
	    detailObj = valuePtr;
	    break;

	case MSG_ICON:
	    icon = TkFindStateNumObj(interp, optionPtr, iconMap, valuePtr);
	    if (icon < 0) {
		return TCL_ERROR;
	    }
	    break;

	case MSG_MESSAGE:
	    messageObj = valuePtr;
	    break;

	case MSG_PARENT:
	    parent = Tk_NameToWindow(interp, Tcl_GetString(valuePtr), tkwin);
	    if (parent == NULL) {
		return TCL_ERROR;
	    }
	    break;

	case MSG_TITLE:
	    titleObj = valuePtr;
	    break;

	case MSG_TYPE:
	    type = TkFindStateNumObj(interp, optionPtr, typeMap, valuePtr);
	    if (type < 0) {
		return TCL_ERROR;
	    }
	    break;
	}
    }

    Tk_MakeWindowExist(parent);
    hWnd = Tk_GetHWND(Tk_WindowId(parent));

    flags = 0;
    if (defaultBtn >= 0) {
	int defaultBtnIdx = -1;

	for (i = 0; i < NUM_TYPES; i++) {
	    if (type == allowedTypes[i].type) {
		int j;

		for (j = 0; j < 3; j++) {
		    if (allowedTypes[i].btnIds[j] == defaultBtn) {
			defaultBtnIdx = j;
			break;
		    }
		}
		if (defaultBtnIdx < 0) {
		    Tcl_AppendResult(interp, "invalid default button \"",
			    TkFindStateString(buttonMap, defaultBtn),
			    "\"", NULL);
		    return TCL_ERROR;
		}
		break;
	    }
	}
	flags = buttonFlagMap[defaultBtnIdx];
    }

    flags |= icon | type | MB_SYSTEMMODAL;

    tmpObj = messageObj ? Tcl_DuplicateObj(messageObj)
	    : Tcl_NewUnicodeObj(NULL, 0);
    Tcl_IncrRefCount(tmpObj);
    if (detailObj) {
	Tcl_AppendUnicodeToObj(tmpObj, L"\n\n", 2);
	Tcl_AppendObjToObj(tmpObj, detailObj);
    }

    oldMode = Tcl_SetServiceMode(TCL_SERVICE_ALL);

    /*
     * MessageBoxW exists for all platforms. Use it to allow unicode error
     * message to be displayed correctly where possible by the OS.
     *
     * In order to have the parent window icon reflected in a MessageBox, we
     * have to create a hook that will trigger when the MessageBox is being
     * created.
     */

    tsdPtr->hSmallIcon = TkWinGetIcon(parent, ICON_SMALL);
    tsdPtr->hBigIcon   = TkWinGetIcon(parent, ICON_BIG);
    tsdPtr->hMsgBoxHook = SetWindowsHookEx(WH_CBT, MsgBoxCBTProc, NULL,
	    GetCurrentThreadId());
    winCode = MessageBoxW(hWnd, Tcl_GetUnicode(tmpObj),
	    titleObj ? Tcl_GetUnicode(titleObj) : L"", flags);
    UnhookWindowsHookEx(tsdPtr->hMsgBoxHook);
    (void) Tcl_SetServiceMode(oldMode);

    /*
     * Ensure that hWnd is enabled, because it can happen that we have updated
     * the wrapper of the parent, which causes us to leave this child disabled
     * (Windows loses sync).
     */

    EnableWindow(hWnd, 1);

    Tcl_DecrRefCount(tmpObj);

    Tcl_SetResult(interp, TkFindStateString(buttonMap, winCode), TCL_STATIC);
    return TCL_OK;
}

static LRESULT CALLBACK
MsgBoxCBTProc(
    int nCode,
    WPARAM wParam,
    LPARAM lParam)
{
    ThreadSpecificData *tsdPtr = (ThreadSpecificData *)
	Tcl_GetThreadData(&dataKey, sizeof(ThreadSpecificData));

    if (nCode == HCBT_CREATEWND) {
	/*
	 * Window owned by our task is being created. Since the hook is
	 * installed just before the MessageBox call and removed after the
	 * MessageBox call, the window being created is either the message box
	 * or one of its controls. Check that the class is WC_DIALOG to ensure
	 * that it's the one we want.
	 */

	LPCBT_CREATEWND lpcbtcreate = (LPCBT_CREATEWND)lParam;

	if (WC_DIALOG == lpcbtcreate->lpcs->lpszClass) {
	    HWND hwnd = (HWND) wParam;
	    SendMessage(hwnd, WM_SETICON, ICON_SMALL,
		    (LPARAM) tsdPtr->hSmallIcon);
	    SendMessage(hwnd, WM_SETICON, ICON_BIG, (LPARAM) tsdPtr->hBigIcon);
	}
    }

    /*
     * Call the next hook proc, if there is one
     */

    return CallNextHookEx(tsdPtr->hMsgBoxHook, nCode, wParam, lParam);
}

static void
SetTkDialog(
    ClientData clientData)
{
    ThreadSpecificData *tsdPtr = (ThreadSpecificData *)
	    Tcl_GetThreadData(&dataKey, sizeof(ThreadSpecificData));
    char buf[32];

    sprintf(buf, "0x%p", (HWND) clientData);
    Tcl_SetVar(tsdPtr->debugInterp, "tk_dialog", buf, TCL_GLOBAL_ONLY);
}

/*
 * Factored out a common pattern in use in this file.
 */
static char *
ConvertExternalFilename(
    Tcl_Encoding encoding,
    char *filename,
    Tcl_DString *dsPtr)
{
    char *p;

    Tcl_ExternalToUtfDString(encoding, filename, -1, dsPtr);
    for (p = Tcl_DStringValue(dsPtr); *p != '\0'; p++) {
	/*
	 * Change the pathname to the Tcl "normalized" pathname, where back
	 * slashes are used instead of forward slashes
	 */

	if (*p == '\\') {
	    *p = '/';
	}
    }
    return Tcl_DStringValue(dsPtr);
}

/*
 * Local Variables:
 * mode: c
 * c-basic-offset: 4
 * fill-column: 78
 * End:
 */
