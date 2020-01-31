/*
 * tkMacOSXMenubutton.c --
 *
 *	This file implements the Macintosh specific portion of the
 *	menubutton widget.
 *
 * Copyright (c) 1996 by Sun Microsystems, Inc.
 * Copyright 2001, Apple Computer, Inc.
 * Copyright (c) 2006-2007 Daniel A. Steffen <das@users.sourceforge.net>
 *
 * See the file "license.terms" for information on usage and redistribution
 * of this file, and for a DISCLAIMER OF ALL WARRANTIES.
 *
 * RCS: @(#) $Id: tkMacOSXMenubutton.c,v 1.18 2007/12/13 15:27:10 dgp Exp $
 */

#include "tkMacOSXPrivate.h"
#include "tkMenu.h"
#include "tkMenubutton.h"
#include "tkMacOSXFont.h"
#include "tkMacOSXDebug.h"

#define kShadowOffset	(3)	/* amount to offset shadow from frame */
#define kTriangleWidth	(11)	/* width of the triangle */
#define kTriangleHeight (6)	/* height of the triangle */
#define kTriangleMargin (5)	/* margin around triangle */

#define TK_POPUP_OFFSET 32	/* size of popup marker */

#define FIRST_DRAW	    2
#define ACTIVE		    4

MODULE_SCOPE int TkMacOSXGetNewMenuID(Tcl_Interp *interp, TkMenu *menuInstPtr,
	int cascade, short *menuIDPtr);
MODULE_SCOPE void TkMacOSXFreeMenuID(short menuID);

typedef struct {
    SInt16 initialValue;
    SInt16 minValue;
    SInt16 maxValue;
    SInt16 procID;
    int isBevel;
} MenuButtonControlParams;

typedef struct {
    int len;
    Str255 title;
    ControlFontStyleRec style;
} ControlTitleParams;

/*
 * Declaration of Mac specific button structure.
 */

typedef struct MacMenuButton {
    TkMenuButton info;		/* Generic button info. */
    WindowRef windowRef;
    ControlRef userPane;
    ControlRef control;
    MenuRef menuRef;
    unsigned long userPaneBackground;
    int flags;
    MenuButtonControlParams params;
    ControlTitleParams titleParams;
    ControlButtonContentInfo bevelButtonContent;
    OpenCPicParams picParams;
} MacMenuButton;

/*
 * Forward declarations for procedures defined later in this file:
 */

static OSStatus SetUserPaneDrawProc(ControlRef control,
	ControlUserPaneDrawProcPtr upp);
static OSStatus SetUserPaneSetUpSpecialBackgroundProc(ControlRef control,
	ControlUserPaneBackgroundProcPtr upp);
static void UserPaneDraw(ControlRef control, ControlPartCode cpc);
static void UserPaneBackgroundProc(ControlHandle,
	ControlBackgroundPtr info);
static int MenuButtonInitControl (MacMenuButton *mbPtr, Rect *paneRect,
	Rect *cntrRect );
static void MenuButtonEventProc(ClientData clientData, XEvent *eventPtr);
static int UpdateControlColors(MacMenuButton *mbPtr);
static void ComputeMenuButtonControlParams(TkMenuButton *mbPtr,
	MenuButtonControlParams * paramsPtr);
static void ComputeControlTitleParams(TkMenuButton *mbPtr,
	ControlTitleParams *paramsPtr);
static void CompareControlTitleParams(ControlTitleParams *p1Ptr,
	ControlTitleParams *p2Ptr, int *titleChanged, int *styleChanged);

/*
 * The structure below defines menubutton class behavior by means of
 * procedures that can be invoked from generic window code.
 */

Tk_ClassProcs tkpMenubuttonClass = {
    sizeof(Tk_ClassProcs),	/* size */
    TkMenuButtonWorldChanged,	/* worldChangedProc */
};


/*
 *----------------------------------------------------------------------
 *
 * TkpCreateMenuButton --
 *
 *	Allocate a new TkMenuButton structure.
 *
 * Results:
 *	Returns a newly allocated TkMenuButton structure.
 *
 * Side effects:
 *	Registers an event handler for the widget.
 *
 *----------------------------------------------------------------------
 */

TkMenuButton *
TkpCreateMenuButton(
    Tk_Window tkwin)
{
    MacMenuButton *mbPtr = (MacMenuButton *) ckalloc(sizeof(MacMenuButton));

    Tk_CreateEventHandler(tkwin, ActivateMask,
	    MenuButtonEventProc, (ClientData) mbPtr);
    mbPtr->flags = 0;
    mbPtr->userPaneBackground = PIXEL_MAGIC << 24;
    mbPtr->userPane = NULL;
    mbPtr->control = NULL;
    mbPtr->menuRef = NULL;
    bzero(&mbPtr->params, sizeof(mbPtr->params));
    bzero(&mbPtr->titleParams, sizeof(mbPtr->titleParams));

    return (TkMenuButton *) mbPtr;
}

/*
 *----------------------------------------------------------------------
 *
 * TkpDisplayMenuButton --
 *
 *	This procedure is invoked to display a menubutton widget.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	Commands are output to X to display the menubutton in its
 *	current mode.
 *
 *----------------------------------------------------------------------
 */

void
TkpDisplayMenuButton(
    ClientData clientData)	/* Information about widget. */
{
    TkMenuButton *butPtr = (TkMenuButton *) clientData;
    Tk_Window tkwin = butPtr->tkwin;
    TkWindow *winPtr;
    Pixmap pixmap;
    MacMenuButton *mbPtr = (MacMenuButton *) butPtr;
    CGrafPtr destPort, savePort;
    Boolean portChanged = false;
    int hasImageOrBitmap = 0, width, height;
    OSStatus err;
    ControlButtonGraphicAlignment theAlignment;
    Rect paneRect, cntrRect;
    int active, enabled;

    butPtr->flags &= ~REDRAW_PENDING;
    if ((butPtr->tkwin == NULL) || !Tk_IsMapped(tkwin)) {
	return;
    }
    pixmap = (Pixmap) Tk_WindowId(tkwin);
    TkMacOSXSetUpClippingRgn(Tk_WindowId(tkwin));

    winPtr = (TkWindow *)butPtr->tkwin;
    paneRect.left = winPtr->privatePtr->xOff;
    paneRect.top = winPtr->privatePtr->yOff;
    paneRect.right = paneRect.left+Tk_Width(butPtr->tkwin);
    paneRect.bottom = paneRect.top+Tk_Height(butPtr->tkwin);

    cntrRect = paneRect;

    cntrRect.left += butPtr->inset;
    cntrRect.top += butPtr->inset;
    cntrRect.right -= butPtr->inset;
    cntrRect.bottom -= butPtr->inset;

    if (mbPtr->userPane) {
	MenuButtonControlParams params;
	bzero(&params, sizeof(params));
	ComputeMenuButtonControlParams(butPtr, &params);
	if (
#ifdef TK_REBUILD_TOPLEVEL
	    (winPtr->flags & TK_REBUILD_TOPLEVEL) ||
#endif
	    bcmp(&params,&mbPtr->params,sizeof(params))) {
	    if (mbPtr->userPane) {
		DisposeControl(mbPtr->userPane);
		mbPtr->userPane = NULL;
		mbPtr->control = NULL;
	    }
	}
    }
    if (!mbPtr->userPane) {
	if (MenuButtonInitControl(mbPtr, &paneRect, &cntrRect)) {
	    TkMacOSXDbgMsg("Init Control failed");
	    return;
	}
    }
    SetControlBounds(mbPtr->userPane, &paneRect);
    SetControlBounds(mbPtr->control, &cntrRect);

    if (butPtr->image != None) {
	Tk_SizeOfImage(butPtr->image, &width, &height);
	hasImageOrBitmap = 1;
    } else if (butPtr->bitmap != None) {
	Tk_SizeOfBitmap(butPtr->display, butPtr->bitmap, &width, &height);
	hasImageOrBitmap = 1;
    }

    /*
     * We need to cache the title and its style
     */

    if (!(mbPtr->flags & FIRST_DRAW)) {
	ControlTitleParams titleParams;
	int titleChanged;
	int styleChanged;

	ComputeControlTitleParams(butPtr, &titleParams);
	CompareControlTitleParams(&titleParams, &mbPtr->titleParams,
		&titleChanged, &styleChanged);
	if (titleChanged) {
	    CFStringRef cf = CFStringCreateWithCString(NULL,
		  (char*) titleParams.title, kCFStringEncodingUTF8);

	    if (hasImageOrBitmap) {
		SetControlTitleWithCFString(mbPtr->control, cf);
	    } else {
		SetMenuItemTextWithCFString(mbPtr->menuRef, 1, cf);
	    }
	    CFRelease(cf);
	    bcopy(titleParams.title, mbPtr->titleParams.title,
		    titleParams.len + 1);
	    mbPtr->titleParams.len = titleParams.len;
	}
	if ((titleChanged||styleChanged) && titleParams .len) {
	    if (hasImageOrBitmap) {
		err = ChkErr(SetControlFontStyle, mbPtr->control,
			&titleParams.style);
		if (err != noErr) {
		    return;
		}
	    }
	    bcopy(&titleParams.style, &mbPtr->titleParams.style,
		    sizeof(titleParams.style));
	}
    }
    if (hasImageOrBitmap) {
	{
	    destPort = TkMacOSXGetDrawablePort(Tk_WindowId(tkwin));
	    portChanged = QDSwapPort(destPort, &savePort);
	    mbPtr->picParams.version = -2;
	    mbPtr->picParams.hRes = 0x00480000;
	    mbPtr->picParams.vRes = 0x00480000;
	    mbPtr->picParams.srcRect.top = 0;
	    mbPtr->picParams.srcRect.left = 0;
	    mbPtr->picParams.srcRect.bottom = height;
	    mbPtr->picParams.srcRect.right = width;
	    mbPtr->picParams.reserved1 = 0;
	    mbPtr->picParams.reserved2 = 0;
	    mbPtr->bevelButtonContent.contentType = kControlContentPictHandle;
	    mbPtr->bevelButtonContent.u.picture = OpenCPicture(&mbPtr->picParams);
	    if (!mbPtr->bevelButtonContent.u.picture) {
		TkMacOSXDbgMsg("OpenCPicture failed");
	    }
	    tkPictureIsOpen = 1;

	    /*
	     * TO DO - There is one case where XCopyPlane calls CopyDeepMask,
	     * which does not get recorded in the picture. So the bitmap code
	     * will fail in that case.
	     */
	}
	if (butPtr->image != NULL) {
	    Tk_RedrawImage(butPtr->image, 0, 0, width, height, pixmap, 0, 0);
	} else {
	    GC gc;
	    
	    if (butPtr->state == STATE_DISABLED) {
		gc = butPtr->disabledGC;
	    } else if (butPtr->state == STATE_ACTIVE) {
		gc = butPtr->activeTextGC;
	    } else {
		gc = butPtr->normalTextGC;
	    }
	    XCopyPlane(butPtr->display, butPtr->bitmap, pixmap, gc, 0, 0,
		    width, height, 0, 0, 1);
	}
	{
	    ClosePicture();
	    tkPictureIsOpen = 0;
	    if (portChanged) {
		QDSwapPort(savePort, NULL);
	    }
	}
	ChkErr(SetControlData, mbPtr->control, kControlButtonPart,
		kControlBevelButtonContentTag,
		sizeof(ControlButtonContentInfo),
		(char *) &mbPtr->bevelButtonContent);
	switch (butPtr->anchor) {
	    case TK_ANCHOR_N:
		theAlignment = kControlBevelButtonAlignTop;
		break;
	    case TK_ANCHOR_NE:
		theAlignment = kControlBevelButtonAlignTopRight;
		break;
	    case TK_ANCHOR_E:
		theAlignment = kControlBevelButtonAlignRight;
		break;
	    case TK_ANCHOR_SE:
		theAlignment = kControlBevelButtonAlignBottomRight;
		break;
	    case TK_ANCHOR_S:
		theAlignment = kControlBevelButtonAlignBottom;
		break;
	    case TK_ANCHOR_SW:
		theAlignment = kControlBevelButtonAlignBottomLeft;
		break;
	    case TK_ANCHOR_W:
		theAlignment = kControlBevelButtonAlignLeft;
		break;
	    case TK_ANCHOR_NW:
		theAlignment = kControlBevelButtonAlignTopLeft;
		break;
	    case TK_ANCHOR_CENTER:
		theAlignment = kControlBevelButtonAlignCenter;
		break;
	}

	ChkErr(SetControlData, mbPtr->control, kControlButtonPart,
		kControlBevelButtonGraphicAlignTag,
		sizeof(ControlButtonGraphicAlignment), (char *) &theAlignment);
    }
    active = ((mbPtr->flags & ACTIVE) != 0);
    if (active != IsControlActive(mbPtr->control)) {
	if (active) {
	    ChkErr(ActivateControl, mbPtr->control);
	} else {
	    ChkErr(DeactivateControl, mbPtr->control);
	}
    }
    enabled = !(butPtr->state == STATE_DISABLED);
    if (enabled != IsControlEnabled(mbPtr->control)) {
	if (enabled) {
	    ChkErr(EnableControl, mbPtr->control);
	} else {
	    ChkErr(DisableControl, mbPtr->control);
	}
    }
    if (active && enabled) {
	if (butPtr->state == STATE_ACTIVE) {
	    if (hasImageOrBitmap) {
		HiliteControl(mbPtr->control, kControlButtonPart);
	    } else {
		HiliteControl(mbPtr->control, kControlLabelPart);
	    }
	} else {
	    HiliteControl(mbPtr->control, kControlNoPart);
	}
    }
    UpdateControlColors(mbPtr);
    if (mbPtr->flags & FIRST_DRAW) {
	ShowControl(mbPtr->control);
	ShowControl(mbPtr->userPane);
	mbPtr->flags ^= FIRST_DRAW;
    } else {
	SetControlVisibility(mbPtr->control, true, true);
	Draw1Control(mbPtr->userPane);
    }
    if (hasImageOrBitmap) {
	if (mbPtr->bevelButtonContent.contentType ==
		kControlContentPictHandle) {
	    KillPicture(mbPtr->bevelButtonContent.u.picture);
	}
    }
}

/*
 *----------------------------------------------------------------------
 *
 * TkpDestroyMenuButton --
 *
 *	Free data structures associated with the menubutton control.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	Restores the default control state.
 *
 *----------------------------------------------------------------------
 */

void
TkpDestroyMenuButton(
    TkMenuButton *mbPtr)
{
    MacMenuButton *macMbPtr = (MacMenuButton *) mbPtr;

    if (macMbPtr->userPane) {
	DisposeControl(macMbPtr->userPane);
	macMbPtr->userPane = NULL;
    }
    if (macMbPtr->menuRef) {
	short menuID = GetMenuID(macMbPtr->menuRef);

	TkMacOSXFreeMenuID(menuID);
	DisposeMenu(macMbPtr->menuRef);
	macMbPtr->menuRef = NULL;
    }
}

/*
 *----------------------------------------------------------------------
 *
 * TkpComputeMenuButtonGeometry --
 *
 *	After changes in a menu button's text or bitmap, this procedure
 *	recomputes the menu button's geometry and passes this information
 *	along to the geometry manager for the window.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	The menu button's window may change size.
 *
 *----------------------------------------------------------------------
 */

void
TkpComputeMenuButtonGeometry(mbPtr)
    register TkMenuButton *mbPtr;	/* Widget record for menu button. */
{
    int width, height, mm, pixels;
    int hasImageOrBitmap = 0;

    mbPtr->inset = mbPtr->highlightWidth + mbPtr->borderWidth;
    if (mbPtr->image != None) {
	Tk_SizeOfImage(mbPtr->image, &width, &height);
	hasImageOrBitmap = 1;
    } else if (mbPtr->bitmap != None) {
	Tk_SizeOfBitmap(mbPtr->display, mbPtr->bitmap, &width, &height);
	hasImageOrBitmap = 1;
    } else {
	hasImageOrBitmap = 0;
	Tk_FreeTextLayout(mbPtr->textLayout);
	mbPtr->textLayout = Tk_ComputeTextLayout(mbPtr->tkfont, mbPtr->text,
		-1, mbPtr->wrapLength, mbPtr->justify, 0, &mbPtr->textWidth,
		&mbPtr->textHeight);
	width = mbPtr->textWidth;
	height = mbPtr->textHeight;
	if (mbPtr->width > 0) {
	    width = mbPtr->width * Tk_TextWidth(mbPtr->tkfont, "0", 1);
	}
	if (mbPtr->height > 0) {
	    Tk_FontMetrics fm;

	    Tk_GetFontMetrics(mbPtr->tkfont, &fm);
	    height = mbPtr->height * fm.linespace;
	}
	width += 2*mbPtr->padX;
	height += 2*mbPtr->padY;
    }
    if (hasImageOrBitmap) {
	if (mbPtr->width > 0) {
	    width = mbPtr->width;
	}
	if (mbPtr->height > 0) {
	    height = mbPtr->height;
	}
	mbPtr->inset = mbPtr->highlightWidth + 2;
	width += (2 * mbPtr->borderWidth + 4);
	height += (2 * mbPtr->borderWidth + 4);
    } else {
	width += TK_POPUP_OFFSET;
    }
    if (mbPtr->indicatorOn) {
	mm = WidthMMOfScreen(Tk_Screen(mbPtr->tkwin));
	pixels = WidthOfScreen(Tk_Screen(mbPtr->tkwin));
	mbPtr->indicatorHeight = kTriangleHeight;
	mbPtr->indicatorWidth = kTriangleWidth + kTriangleMargin;
	width += mbPtr->indicatorWidth;
    } else {
	mbPtr->indicatorHeight = 0;
	mbPtr->indicatorWidth = 0;
    }

    Tk_GeometryRequest(mbPtr->tkwin, (int) (width + 2*mbPtr->inset),
	    (int) (height + 2*mbPtr->inset));
    Tk_SetInternalBorder(mbPtr->tkwin, mbPtr->inset);
}

/*
 *----------------------------------------------------------------------
 *
 * ComputeMenuButtonControlParams --
 *
 *	This procedure computes the various parameters used
 *	when creating a Carbon control (NewControl)
 *	These are determined by the various tk menu button parameters
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	Sets the control initialisation parameters
 *
 *----------------------------------------------------------------------
 */

static void
ComputeMenuButtonControlParams(
    TkMenuButton *mbPtr,
    MenuButtonControlParams *paramsPtr)
{
    int fakeMenuID = 256;

    /*
     * Determine ProcID based on button type and dimensions
     *
     * We need to set minValue to some non-zero value,
     * Otherwise, the markers do not show up
     */

    paramsPtr->minValue = kControlBehaviorMultiValueMenu;
    paramsPtr->maxValue = 0;
    if (mbPtr->image || mbPtr->bitmap) {
	paramsPtr->isBevel = 1;
	if (mbPtr->borderWidth <= 2) {
	    paramsPtr->procID = kControlBevelButtonSmallBevelProc;
	} else if (mbPtr->borderWidth == 3) {
	    paramsPtr->procID = kControlBevelButtonNormalBevelProc;
	} else {
	    paramsPtr->procID = kControlBevelButtonLargeBevelProc;
	}
	if (mbPtr->indicatorOn) {
	    paramsPtr->initialValue = fakeMenuID;
	} else {
	    paramsPtr->initialValue = 0;
	}
    } else {
	paramsPtr->isBevel = 0;
	paramsPtr->procID = kControlPopupButtonProc
		+ kControlPopupVariableWidthVariant;
	paramsPtr->minValue = -12345;
	paramsPtr->maxValue = -1;
	paramsPtr->initialValue = 0;
    }
}

/*
 *----------------------------------------------------------------------
 *
 * returns 0 if same, 1 otherwise
 *
 *----------------------------------------------------------------------
 */

static void
CompareControlTitleParams(
    ControlTitleParams *p1Ptr,
    ControlTitleParams *p2Ptr,
    int *titleChanged,
    int *styleChanged)
{
    if (p1Ptr->len != p2Ptr->len) {
	*titleChanged = 1;
    } else if (bcmp(p1Ptr->title,p2Ptr->title,p1Ptr->len)) {
	*titleChanged = 1;
    } else {
	*titleChanged = 0;
    }

    if (p1Ptr->len && p2Ptr->len) {
	*styleChanged = bcmp(&p1Ptr->style, &p2Ptr->style,
		sizeof(p2Ptr->style));
    } else {
	*styleChanged = p1Ptr->len||p2Ptr->len;
    }
}

static void
ComputeControlTitleParams(
    TkMenuButton *butPtr,
    ControlTitleParams *paramsPtr)
{
    Tk_Font font;

    paramsPtr->len = TkFontGetFirstTextLayout(butPtr->textLayout, &font,
	    (char*) paramsPtr->title);
    paramsPtr->title[paramsPtr->len] = 0;
    if (paramsPtr->len) {
	TkMacOSXInitControlFontStyle(font,&paramsPtr->style);
    }
}

/*
 *----------------------------------------------------------------------
 *
 * MenuButtonInitControl --
 *
 *	This procedure initialises a Carbon control
 *
 * Results:
 *	0 on success, 1 on failure.
 *
 * Side effects:
 *	A background pane control and the control itself is created
 *	The contol is embedded in the background control
 *	The background control is embedded in the root control
 *	of the containing window
 *	The creation parameters for the control are also computed
 *
 *----------------------------------------------------------------------
 */
int
MenuButtonInitControl(
    MacMenuButton *mbPtr,	/* Mac button. */
    Rect *paneRect,
    Rect *cntrRect)
{
    OSStatus err;
    TkMenuButton *butPtr = (TkMenuButton *) mbPtr;
    SInt16 procID, initialValue, minValue, maxValue;
    Boolean initiallyVisible;
    SInt32 controlReference;
    short menuID;
    ControlRef rootControl =
	    TkMacOSXGetRootControl(Tk_WindowId(butPtr->tkwin));

    mbPtr->windowRef = TkMacOSXDrawableWindow(Tk_WindowId(butPtr->tkwin));

    /*
     * Set up the user pane
     */

    initiallyVisible = false;
    initialValue = kControlSupportsEmbedding | kControlHasSpecialBackground;
    minValue = 0;
    maxValue = 1;
    procID = kControlUserPaneProc;
    controlReference = (SInt32)mbPtr;
    mbPtr->userPane = NewControl(mbPtr->windowRef, paneRect, "\p",
	    initiallyVisible, initialValue, minValue, maxValue, procID,
	    controlReference);
    if (!mbPtr->userPane) {
	TkMacOSXDbgMsg("Failed to create user pane control");
	return 1;
    }
    err = ChkErr(EmbedControl, mbPtr->userPane, rootControl);
    if (err != noErr) {
	return 1;
    }
    SetUserPaneSetUpSpecialBackgroundProc(mbPtr->userPane,
	    UserPaneBackgroundProc);
    SetUserPaneDrawProc(mbPtr->userPane,UserPaneDraw);
    initiallyVisible = false;
    ComputeMenuButtonControlParams(butPtr,&mbPtr->params);

    /*
     * Do this only if we are using bevel buttons.
     */

    ComputeControlTitleParams(butPtr, &mbPtr->titleParams);
    mbPtr->control = NewControl(mbPtr->windowRef,
	    cntrRect, "\p" /* mbPtr->titleParams.title */,
	    initiallyVisible, mbPtr->params.initialValue,
	    mbPtr->params.minValue, mbPtr->params.maxValue,
	    mbPtr->params.procID, controlReference);
    if (!mbPtr->control) {
	TkMacOSXDbgMsg("Failed to create control of type %d",
		mbPtr->params.procID);
	return 1;
    }
    err = ChkErr(EmbedControl, mbPtr->control, mbPtr->userPane);
    if (err != noErr ) {
	return 1;
    }
    if (mbPtr->params.isBevel) {
	CFStringRef cf = CFStringCreateWithCString(NULL,
		(char*) mbPtr->titleParams.title, kCFStringEncodingUTF8);

	SetControlTitleWithCFString(mbPtr->control, cf);
	CFRelease(cf);
	if (mbPtr->titleParams.len) {
	    err = ChkErr(SetControlFontStyle, mbPtr->control,
		    &mbPtr->titleParams.style);
	    if (err != noErr) {
		return 1;
	    }
	}
    } else {
	CFStringRef cfStr;

	err = TkMacOSXGetNewMenuID(mbPtr->info.interp, (TkMenu *) mbPtr, 0,
		&menuID);
	if (err != TCL_OK) {
	    return 1;
	}
	err = ChkErr(CreateNewMenu, menuID, kMenuAttrDoNotUseUserCommandKeys,
		&(mbPtr->menuRef));
	if (err != noErr) {
	    return 1;
	}
	cfStr = CFStringCreateWithCString(NULL, Tk_PathName(mbPtr->info.tkwin),
		kCFStringEncodingUTF8);
	if (!cfStr) {
	    TkMacOSXDbgMsg("CFStringCreateWithCString failed");
	    return 1;
	}
	err = ChkErr(SetMenuTitleWithCFString, mbPtr->menuRef, cfStr);
	CFRelease(cfStr);
	if (err != noErr) {
	    return 1;
	}
	cfStr = CFStringCreateWithCString(NULL,
		(char*) mbPtr->titleParams.title, kCFStringEncodingUTF8);
	AppendMenuItemText(mbPtr->menuRef, "\px");
	if (cfStr) {
	    SetMenuItemTextWithCFString(mbPtr->menuRef, 1, cfStr);
	    CFRelease(cfStr);
	}
	ChkErr(SetControlData, mbPtr->control, kControlNoPart,
		kControlPopupButtonMenuRefTag, sizeof(mbPtr->menuRef),
		&mbPtr->menuRef);
	SetControlMinimum(mbPtr->control, 1);
	SetControlMaximum(mbPtr->control, 1);
	SetControlValue(mbPtr->control, 1);
    }
    mbPtr->flags |= FIRST_DRAW;
    if (IsWindowActive(mbPtr->windowRef)) {
	mbPtr->flags |= ACTIVE;
    }
    return 0;
}

/*
 *--------------------------------------------------------------
 *
 * SetUserPane
 *
 *	Utility function to add a UserPaneDrawProc
 *	to a userPane control. From MoreControls code
 *	from Apple DTS.
 *
 * Results:
 *	MacOS system error.
 *
 * Side effects:
 *	The user pane gets a new UserPaneDrawProc.
 *
 *--------------------------------------------------------------
 */
OSStatus
SetUserPaneDrawProc(
    ControlRef control,
    ControlUserPaneDrawProcPtr upp)
{
    ControlUserPaneDrawUPP myControlUserPaneDrawUPP =
	    NewControlUserPaneDrawUPP(upp);

    return SetControlData(control, kControlNoPart,kControlUserPaneDrawProcTag,
	    sizeof(myControlUserPaneDrawUPP), (Ptr)&myControlUserPaneDrawUPP);
}

/*
 *--------------------------------------------------------------
 *
 * SetUserPaneSetUpSpecialBackgroundProc --
 *
 *	Utility function to add a UserPaneBackgroundProc
 *	to a userPane control
 *
 * Results:
 *	MacOS system error.
 *
 * Side effects:
 *	The user pane gets a new UserPaneBackgroundProc.
 *
 *--------------------------------------------------------------
 */

OSStatus
SetUserPaneSetUpSpecialBackgroundProc(
    ControlRef control,
    ControlUserPaneBackgroundProcPtr upp)
{
    ControlUserPaneBackgroundUPP myControlUserPaneBackgroundUPP =
	    NewControlUserPaneBackgroundUPP(upp);

    return SetControlData(control, kControlNoPart,
	kControlUserPaneBackgroundProcTag,
	sizeof(myControlUserPaneBackgroundUPP),
	(Ptr) &myControlUserPaneBackgroundUPP);
}

/*
 *--------------------------------------------------------------
 *
 * UserPaneDraw --
 *
 *	This function draws the background of the user pane that will
 *	lie under checkboxes and radiobuttons.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	The user pane gets updated to the current color.
 *
 *--------------------------------------------------------------
 */

void
UserPaneDraw(
    ControlRef control,
    ControlPartCode cpc)
{
    Rect contrlRect;
    MacMenuButton * mbPtr =
	    (MacMenuButton *)(intptr_t)GetControlReference(control);
    CGrafPtr port;

    GetPort(&port);
    GetControlBounds(control,&contrlRect);
    TkMacOSXSetColorInPort(mbPtr->userPaneBackground, 0, NULL, port);
    EraseRect (&contrlRect);
}

/*
 *--------------------------------------------------------------
 *
 * UserPaneBackgroundProc --
 *
 *	This function sets up the background of the user pane that will
 *	lie under checkboxes and radiobuttons.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	The user pane background gets set to the current color.
 *
 *--------------------------------------------------------------
 */

void
UserPaneBackgroundProc(
    ControlHandle control,
    ControlBackgroundPtr info)
{
    MacMenuButton *mbPtr =
	    (MacMenuButton *)(intptr_t)GetControlReference(control);

    if (info->colorDevice) {
	CGrafPtr port;

	GetPort(&port);
	TkMacOSXSetColorInPort(mbPtr->userPaneBackground, 0, NULL, port);
    }
}

/*
 *--------------------------------------------------------------
 *
 * UpdateControlColors --
 *
 *	This function will review the colors used to display
 *	a Macintosh button. If any non-standard colors are
 *	used we create a custom palette for the button, populate
 *	with the colors for the button and install the palette.
 *
 *	Under Appearance, we just set the pointer that will be
 *	used by the UserPaneDrawProc.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	The Macintosh control may get a custom palette installed.
 *
 *--------------------------------------------------------------
 */

static int
UpdateControlColors(
    MacMenuButton *mbPtr)
{
    XColor *xcolor;
    TkMenuButton * butPtr = (TkMenuButton *) mbPtr;

    /*
     * Under Appearance we cannot change the background of the
     * button itself. However, the color we are setting is the color
     * of the containing userPane. This will be the color that peeks
     * around the rounded corners of the button.
     * We make this the highlightbackground rather than the background,
     * because if you color the background of a frame containing a
     * button, you usually also color the highlightbackground as well,
     * or you will get a thin grey ring around the button.
     */

    xcolor = Tk_3DBorderColor(butPtr->normalBorder);
    mbPtr->userPaneBackground = xcolor->pixel;

    return false;
}

/*
 *--------------------------------------------------------------
 *
 * MenuButtonEventProc --
 *
 *	This procedure is invoked by the Tk dispatcher for various
 *	events on buttons.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	When it gets exposed, it is redisplayed.
 *
 *--------------------------------------------------------------
 */

static void
MenuButtonEventProc(
    ClientData clientData,	/* Information about window. */
    XEvent *eventPtr)		/* Information about event. */
{
    TkMenuButton *buttonPtr = (TkMenuButton *) clientData;
    MacMenuButton *mbPtr = (MacMenuButton *) clientData;

    if (eventPtr->type == ActivateNotify
	    || eventPtr->type == DeactivateNotify) {
	if ((buttonPtr->tkwin == NULL) || (!Tk_IsMapped(buttonPtr->tkwin))) {
	    return;
	}
	if (eventPtr->type == ActivateNotify) {
	    mbPtr->flags |= ACTIVE;
	} else {
	    mbPtr->flags &= ~ACTIVE;
	}
	if ((buttonPtr->flags & REDRAW_PENDING) == 0) {
	    Tcl_DoWhenIdle(TkpDisplayMenuButton, (ClientData) buttonPtr);
	    buttonPtr->flags |= REDRAW_PENDING;
	}
    }
}
