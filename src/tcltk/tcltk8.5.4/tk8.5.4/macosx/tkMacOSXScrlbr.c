/*
 * tkMacOSXScrollbar.c --
 *
 *	This file implements the Macintosh specific portion of the scrollbar
 *	widget. The Macintosh scrollbar may also draw a windows grow
 *	region under certain cases.
 *
 * Copyright (c) 1996 by Sun Microsystems, Inc.
 * Copyright 2001, Apple Computer, Inc.
 * Copyright (c) 2006-2007 Daniel A. Steffen <das@users.sourceforge.net>
 *
 * See the file "license.terms" for information on usage and redistribution
 * of this file, and for a DISCLAIMER OF ALL WARRANTIES.
 *
 * RCS: @(#) $Id: tkMacOSXScrlbr.c,v 1.26 2007/12/13 15:27:10 dgp Exp $
 */

#include "tkMacOSXPrivate.h"
#include "tkScrollbar.h"
#include "tkMacOSXDebug.h"

#define MIN_SCROLLBAR_VALUE		0
#define SCROLLBAR_SCALING_VALUE		((double)(LONG_MAX>>1))

/*
 * Declaration of Mac specific scrollbar structure.
 */

typedef struct MacScrollbar {
    TkScrollbar info;		/* Generic scrollbar info */
    ControlRef	sbHandle;	/* Scrollbar control */
    int		macFlags;	/* Various flags; see below */
    Rect	eraseRect;	/* Rect to erase before drawing control */
} MacScrollbar;

/*
 * Flag bits for scrollbars on the Mac:
 *
 * ALREADY_DEAD:		Non-zero means this scrollbar has been
 *				destroyed, but has not been cleaned up.
 * IN_MODAL_LOOP:		Non-zero means this scrollbar is in the middle
 *				of a modal loop.
 * ACTIVE:			Non-zero means this window is currently
 *				active (in the foreground).
 */

#define ALREADY_DEAD		1
#define IN_MODAL_LOOP		2
#define ACTIVE			4

/*
 * Globals uses locally in this file.
 */
static ControlActionUPP scrollActionProc = NULL;	/* Pointer to func. */
static ControlActionUPP thumbActionProc = NULL;		/* Pointer to func. */
static Point mouseDownPoint;	/* Used to store the coordinates where the  */
				/* mouse was first pressed to begin	    */
				/* dragging the thumb, because		    */
				/* ThumbActionProc can't take any args.	    */

typedef struct ScrollbarMetrics {
    SInt32 width, minHeight, minThumbHeight;
    short topArrowHeight, bottomArrowHeight;
    ControlSize size;
} ScrollbarMetrics;

static ScrollbarMetrics metrics[2] = {
    {15, 54, 26, 14, 14, kControlSizeNormal}, /* kThemeScrollBarMedium */
    {11, 40, 20, 10, 10, kControlSizeSmall},  /* kThemeScrollBarSmall  */
};

/*
 * This variable holds the default width for a scrollbar in string form for
 * use in a Tk_ConfigSpec.
 */

static char defWidth[TCL_INTEGER_SPACE];

/*
 * Forward declarations for procedures defined later in this file:
 */

static pascal void ScrollbarActionProc(ControlRef theControl,
	ControlPartCode partCode);
static pascal void ThumbActionProc(ControlRef theControl,
	ControlPartCode partCode);
static int ScrollbarBindProc(ClientData clientData, Tcl_Interp *interp,
	XEvent *eventPtr, Tk_Window tkwin, KeySym keySym);
static void ScrollbarEventProc(ClientData clientData, XEvent *eventPtr);
static void UpdateControlValues(MacScrollbar *macScrollPtr);

/*
 * The class procedure table for the scrollbar widget. Leave the proc fields
 * initialized to NULL, which should happen automatically because of the scope
 * at which the variable is declared.
 */

Tk_ClassProcs tkpScrollbarProcs = {
    sizeof(Tk_ClassProcs)	/* size */
};

/*
 *----------------------------------------------------------------------
 *
 * TkMacOSXInitScrollbarMetrics --
 *
 *	This function initializes the current system metrics for a
 *	scrollbar.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	Updates the geometry cache info for all scrollbars.
 *
 *----------------------------------------------------------------------
 */

void
TkMacOSXInitScrollbarMetrics(void)
{
    const short height = 100, width = 50;
    ThemeTrackDrawInfo info = {0, {0, 0, height, width}, 0, 1, 0, 0,
	    kThemeTrackShowThumb, kThemeTrackActive, 0, {{1, 0}}};
    Rect bounds;
    Tk_ConfigSpec *specPtr;

    ChkErr(GetThemeMetric, kThemeMetricScrollBarWidth, &metrics[0].width);
    ChkErr(GetThemeMetric, kThemeMetricScrollBarMinThumbHeight,
	    &metrics[0].minThumbHeight);
    info.kind = kThemeScrollBarMedium;
    ChkErr(GetThemeTrackDragRect, &info, &bounds);
    metrics[0].topArrowHeight = bounds.top;
    metrics[0].bottomArrowHeight = height - bounds.bottom;
    metrics[0].minHeight = metrics[0].minThumbHeight +
	    metrics[0].topArrowHeight + metrics[0].bottomArrowHeight;
    ChkErr(GetThemeMetric, kThemeMetricSmallScrollBarWidth, &metrics[1].width);
    ChkErr(GetThemeMetric, kThemeMetricSmallScrollBarMinThumbHeight,
	    &metrics[1].minThumbHeight);
    info.kind = kThemeScrollBarSmall;
    ChkErr(GetThemeTrackDragRect, &info, &bounds);
    metrics[1].topArrowHeight = bounds.top;
    metrics[1].bottomArrowHeight = height - bounds.bottom;
    metrics[1].minHeight = metrics[1].minThumbHeight +
	    metrics[1].topArrowHeight + metrics[1].bottomArrowHeight;

    sprintf(defWidth, "%ld", metrics[0].width);
    for (specPtr = tkpScrollbarConfigSpecs; specPtr->type != TK_CONFIG_END;
	    specPtr++) {
	if (specPtr->offset == Tk_Offset(TkScrollbar, width)) {
	    specPtr->defValue = defWidth;
	}
    }
}

/*
 *----------------------------------------------------------------------
 *
 * TkpCreateScrollbar --
 *
 *	Allocate a new TkScrollbar structure.
 *
 * Results:
 *	Returns a newly allocated TkScrollbar structure.
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */

TkScrollbar *
TkpCreateScrollbar(
    Tk_Window tkwin)	/* New Tk Window. */
{
    static int initialized = 0;
    MacScrollbar * macScrollPtr;
    TkWindow *winPtr = (TkWindow *)tkwin;

    if (scrollActionProc == NULL) {
	scrollActionProc = NewControlActionUPP(ScrollbarActionProc);
	thumbActionProc =  NewControlActionUPP(ThumbActionProc);
    }
    if (!initialized) {
	TkMacOSXInitScrollbarMetrics();
	initialized = 1;
    }
    macScrollPtr = (MacScrollbar *) ckalloc(sizeof(MacScrollbar));
    macScrollPtr->sbHandle = NULL;
    macScrollPtr->macFlags = 0;
    SetRect(&macScrollPtr->eraseRect, 0, 0, 0, 0);

    Tk_CreateEventHandler(tkwin, ActivateMask|ExposureMask|
	StructureNotifyMask|FocusChangeMask,
	ScrollbarEventProc, (ClientData) macScrollPtr);

    if (!Tcl_GetAssocData(winPtr->mainPtr->interp, "TkScrollbar", NULL)) {
	Tcl_SetAssocData(winPtr->mainPtr->interp, "TkScrollbar", NULL,
		(ClientData)1);
	TkCreateBindingProcedure(winPtr->mainPtr->interp,
	    winPtr->mainPtr->bindingTable,
	    (ClientData)Tk_GetUid("Scrollbar"), "<ButtonPress>",
	    ScrollbarBindProc, NULL, NULL);
    }
    return (TkScrollbar *) macScrollPtr;
}

/*
 *--------------------------------------------------------------
 *
 * TkpDisplayScrollbar --
 *
 *	This procedure redraws the contents of a scrollbar window.
 *	It is invoked as a do-when-idle handler, so it only runs
 *	when there's nothing else for the application to do.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	Information appears on the screen.
 *
 *--------------------------------------------------------------
 */

void
TkpDisplayScrollbar(
    ClientData clientData)	/* Information about window. */
{
    TkScrollbar *scrollPtr = (TkScrollbar *) clientData;
    MacScrollbar *macScrollPtr = (MacScrollbar *) clientData;
    Tk_Window tkwin = scrollPtr->tkwin;
    CGrafPtr destPort, savePort;
    Boolean portChanged;
    WindowRef windowRef;

    if ((scrollPtr->tkwin == NULL) || !Tk_IsMapped(tkwin)) {
	goto done;
    }

    /*
     * Draw the focus or any 3D relief we may have.
     */
    if (scrollPtr->highlightWidth != 0) {
	GC fgGC, bgGC;

	bgGC = Tk_GCForColor(scrollPtr->highlightBgColorPtr,
	    Tk_WindowId(tkwin));

	if (scrollPtr->flags & GOT_FOCUS) {
	    fgGC = Tk_GCForColor(scrollPtr->highlightColorPtr,
		Tk_WindowId(tkwin));
	    TkpDrawHighlightBorder(tkwin, fgGC, bgGC, scrollPtr->highlightWidth,
		Tk_WindowId(tkwin));
	} else {
	    TkpDrawHighlightBorder(tkwin, bgGC, bgGC, scrollPtr->highlightWidth,
		Tk_WindowId(tkwin));
	}
    }
    Tk_Draw3DRectangle(tkwin, Tk_WindowId(tkwin), scrollPtr->bgBorder,
	scrollPtr->highlightWidth, scrollPtr->highlightWidth,
	Tk_Width(tkwin) - 2*scrollPtr->highlightWidth,
	Tk_Height(tkwin) - 2*scrollPtr->highlightWidth,
	scrollPtr->borderWidth, scrollPtr->relief);

    if (macScrollPtr->sbHandle == NULL) {
	Rect r = {0, 0, 1, 1};

	windowRef = TkMacOSXDrawableWindow(Tk_WindowId(tkwin));
	CreateScrollBarControl(windowRef, &r, 0, 0, 0, 0, true, NULL,
		&(macScrollPtr->sbHandle));
	SetControlReference(macScrollPtr->sbHandle, (SInt32) scrollPtr);

	if (IsWindowActive(windowRef)) {
	    macScrollPtr->macFlags |= ACTIVE;
	}
    }

    /*
     * Update the control values before we draw.
     */

    UpdateControlValues(macScrollPtr);

    /*
     * Set up port for drawing Macintosh control.
     */
    destPort = TkMacOSXGetDrawablePort(Tk_WindowId(tkwin));
    portChanged = QDSwapPort(destPort, &savePort);
    TkMacOSXSetUpClippingRgn(Tk_WindowId(tkwin));

    /*
     * Scrollbars do not erase the complete control bounds if they are wider
     * than the standard width, so manually erase the extra space.
     */

    if (!EmptyRect(&macScrollPtr->eraseRect)) {
	EraseRect(&macScrollPtr->eraseRect);
    }

    Draw1Control(macScrollPtr->sbHandle);

    if (portChanged) {
	QDSwapPort(savePort, NULL);
    }

    done:
    scrollPtr->flags &= ~REDRAW_PENDING;
}

/*
 *----------------------------------------------------------------------
 *
 * TkpConfigureScrollbar --
 *
 *	This procedure is called after the generic code has finished
 *	processing configuration options, in order to configure
 *	platform specific options.
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
TkpConfigureScrollbar(scrollPtr)
    register TkScrollbar *scrollPtr;	/* Information about widget; may or
					 * may not already have values for
					 * some fields. */
{
}

/*
 *----------------------------------------------------------------------
 *
 * TkpComputeScrollbarGeometry --
 *
 *	After changes in a scrollbar's size or configuration, this
 *	procedure recomputes various geometry information used in
 *	displaying the scrollbar.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	The scrollbar will be displayed differently.
 *
 *----------------------------------------------------------------------
 */

void
TkpComputeScrollbarGeometry(
    register TkScrollbar *scrollPtr)	/* Scrollbar whose geometry may
					 * have changed. */
{
    int variant, fieldLength;

    if (scrollPtr->highlightWidth < 0) {
	scrollPtr->highlightWidth = 0;
    }
    scrollPtr->inset = scrollPtr->highlightWidth + scrollPtr->borderWidth;
    variant = ((scrollPtr->vertical ? Tk_Width(scrollPtr->tkwin) :
	    Tk_Height(scrollPtr->tkwin)) - 2 * scrollPtr->inset
	    < metrics[0].width) ? 1 : 0;
    scrollPtr->arrowLength = (metrics[variant].topArrowHeight +
	    metrics[variant].bottomArrowHeight) / 2;
    fieldLength = (scrollPtr->vertical ? Tk_Height(scrollPtr->tkwin)
	    : Tk_Width(scrollPtr->tkwin))
	    - 2 * (scrollPtr->arrowLength + scrollPtr->inset);
    if (fieldLength < 0) {
	fieldLength = 0;
    }
    scrollPtr->sliderFirst = fieldLength * scrollPtr->firstFraction;
    scrollPtr->sliderLast = fieldLength * scrollPtr->lastFraction;

    /*
     * Adjust the slider so that some piece of it is always
     * displayed in the scrollbar and so that it has at least
     * a minimal width (so it can be grabbed with the mouse).
     */

    if (scrollPtr->sliderFirst > (fieldLength - 2*scrollPtr->borderWidth)) {
	scrollPtr->sliderFirst = fieldLength - 2*scrollPtr->borderWidth;
    }
    if (scrollPtr->sliderFirst < 0) {
	scrollPtr->sliderFirst = 0;
    }
    if (scrollPtr->sliderLast < (scrollPtr->sliderFirst +
	    metrics[variant].minThumbHeight)) {
	scrollPtr->sliderLast = scrollPtr->sliderFirst +
		metrics[variant].minThumbHeight;
    }
    if (scrollPtr->sliderLast > fieldLength) {
	scrollPtr->sliderLast = fieldLength;
    }
    scrollPtr->sliderFirst += scrollPtr->inset +
	    metrics[variant].topArrowHeight;
    scrollPtr->sliderLast += scrollPtr->inset +
	    metrics[variant].bottomArrowHeight;

    /*
     * Register the desired geometry for the window (leave enough space
     * for the two arrows plus a minimum-size slider, plus border around
     * the whole window, if any). Then arrange for the window to be
     * redisplayed.
     */

    if (scrollPtr->vertical) {
	Tk_GeometryRequest(scrollPtr->tkwin, scrollPtr->width +
		2 * scrollPtr->inset, 2 * (scrollPtr->arrowLength +
		scrollPtr->borderWidth + scrollPtr->inset) +
		metrics[variant].minThumbHeight);
    } else {
	Tk_GeometryRequest(scrollPtr->tkwin, 2 * (scrollPtr->arrowLength +
		scrollPtr->borderWidth + scrollPtr->inset) +
		metrics[variant].minThumbHeight, scrollPtr->width +
		2 * scrollPtr->inset);
    }
    Tk_SetInternalBorder(scrollPtr->tkwin, scrollPtr->inset);
}

/*
 *----------------------------------------------------------------------
 *
 * TkpDestroyScrollbar --
 *
 *	Free data structures associated with the scrollbar control.
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
TkpDestroyScrollbar(
    TkScrollbar *scrollPtr)	/* Scrollbar to destroy. */
{
    MacScrollbar *macScrollPtr = (MacScrollbar *)scrollPtr;

    if (macScrollPtr->sbHandle != NULL) {
	if (!(macScrollPtr->macFlags & IN_MODAL_LOOP)) {
	    DisposeControl(macScrollPtr->sbHandle);
	    macScrollPtr->sbHandle = NULL;
	}
    }
    macScrollPtr->macFlags |= ALREADY_DEAD;
}

/*
 *--------------------------------------------------------------
 *
 * TkpScrollbarPosition --
 *
 *	Determine the scrollbar element corresponding to a
 *	given position.
 *
 * Results:
 *	One of TOP_ARROW, TOP_GAP, etc., indicating which element
 *	of the scrollbar covers the position given by (x, y). If
 *	(x,y) is outside the scrollbar entirely, then OUTSIDE is
 *	returned.
 *
 * Side effects:
 *	None.
 *
 *--------------------------------------------------------------
 */

int
TkpScrollbarPosition(
    TkScrollbar *scrollPtr,	/* Scrollbar widget record. */
    int x, int y)		/* Coordinates within scrollPtr's
				 * window. */
{
    MacScrollbar *macScrollPtr = (MacScrollbar *) scrollPtr;
    CGrafPtr destPort, savePort;
    Boolean portChanged;
    int inactive = 0;
    ControlPartCode part;
    Point where = {y, x};
    Rect bounds;

    if ((x < scrollPtr->inset) || (x >= (Tk_Width(scrollPtr->tkwin) -
	    scrollPtr->inset)) || (y < scrollPtr->inset) ||
	    (y >= (Tk_Height(scrollPtr->tkwin) - scrollPtr->inset))) {
	return OUTSIDE;
    }

    /*
     * All of the calculations in this procedure mirror those in
     * DisplayScrollbar. Be sure to keep the two consistent. On the
     * Macintosh we use the OS call TestControl to do this mapping.
     * For TestControl to work, the scrollbar must be active and must
     * be in the current port.
     */

    destPort = TkMacOSXGetDrawablePort(Tk_WindowId(scrollPtr->tkwin));
    portChanged = QDSwapPort(destPort, &savePort);
    UpdateControlValues(macScrollPtr);
    if (!IsControlActive(macScrollPtr->sbHandle)) {
	inactive = true;
	ActivateControl(macScrollPtr->sbHandle);
    }
    TkMacOSXWinBounds((TkWindow *) scrollPtr->tkwin, &bounds);
    where.h += bounds.left;
    where.v += bounds.top;
    part = TestControl(((MacScrollbar *) scrollPtr)->sbHandle, where);
    if (inactive) {
	DeactivateControl(macScrollPtr->sbHandle);
    }
    if (portChanged) {
	QDSwapPort(savePort, NULL);
    }
    switch (part) {
	case kAppearancePartUpButton:
	    return TOP_ARROW;
	case kAppearancePartPageUpArea:
	    return TOP_GAP;
	case kAppearancePartIndicator:
	    return SLIDER;
	case kAppearancePartPageDownArea:
	    return BOTTOM_GAP;
	case kAppearancePartDownButton:
	    return BOTTOM_ARROW;
	default:
	    return OUTSIDE;
    }
}

/*
 *--------------------------------------------------------------
 *
 * ThumbActionProc --
 *
 *	Callback procedure used by the Macintosh toolbox call
 *	HandleControlClick. This call is used to track the
 *	thumb of the scrollbar. Unlike the
 *	ScrollbarActionProc function this function is called
 *	once and basically takes over tracking the scrollbar
 *	from the control. This is done to avoid conflicts with
 *	what the control plans to draw.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	May change the display.
 *
 *--------------------------------------------------------------
 */

static pascal void
ThumbActionProc(ControlRef theControl, ControlPartCode partCode)
{
    TkScrollbar *scrollPtr = (TkScrollbar *)(intptr_t)GetControlReference(
	    theControl);
    MacScrollbar *macScrollPtr = (MacScrollbar *) scrollPtr;
    Tcl_DString cmdString;
    int origValue, variant;
    short trackBarSize;
    double oldFirstFraction, newFirstFraction;
    char valueString[40];
    Point currentPoint = { 0, 0 };
    Rect trackRect;
    Tcl_Interp *interp;
    MouseTrackingResult trackingResult;
    OSStatus err;

    if (scrollPtr == NULL) {
	return;
    }

    Tcl_DStringInit(&cmdString);
    origValue = GetControl32BitValue(macScrollPtr->sbHandle);
    GetControlBounds(macScrollPtr->sbHandle, &trackRect);

    if (scrollPtr->vertical) {
	variant = (trackRect.right - trackRect.left) < metrics[0].width ? 1 : 0;
	trackBarSize = trackRect.bottom - trackRect.top -
		metrics[variant].topArrowHeight -
		metrics[variant].bottomArrowHeight;
	InsetRect(&trackRect, -25, -113);
    } else {
	variant = (trackRect.bottom - trackRect.top) < metrics[0].width ? 1 : 0;
	trackBarSize = trackRect.right - trackRect.left -
		metrics[variant].topArrowHeight -
		metrics[variant].bottomArrowHeight;
	InsetRect(&trackRect, -113, -25);
    }

    /*
     * Track the mouse while the button is held down. If the mouse is moved,
     * we calculate the value that should be passed to the "command" part of
     * the scrollbar. Since the mouse may move a distance too small to
     * cause a change to the first fraction, each calculation must be done
     * versus what the first fraction was when the mouse button was
     * initially pressed. Otherwise, moving the mouse too slowly will
     * cause the calculated fraction delta to be zero and the scrollbar
     * won't respond.
     */

    oldFirstFraction = scrollPtr->firstFraction;

    TkMacOSXTrackingLoop(1);
    do {
	err = ChkErr(TrackMouseLocationWithOptions, NULL,
		kTrackMouseLocationOptionDontConsumeMouseUp,
		kEventDurationForever, &currentPoint, NULL, &trackingResult);
	if ((err == noErr) && ((trackingResult == kMouseTrackingMouseDragged)
		|| (trackingResult == kMouseTrackingMouseMoved))) {

	   /*
	    * Calculate where the scrollbar should move to, based on
	    * where the mouse button was pressed and where the scrollbar
	    * initially was at that time. Note that PtInRect() will
	    * return false if currentPoint or trackRect are not in
	    * is not in current graphics port, which may happen if any
	    * of the waiting idle events change the port (e.g. with
	    * SetPort()) but fail to restore it before returning and the
	    * scrollbar will lock in place.
	    */
	    newFirstFraction = oldFirstFraction;
	    if (PtInRect(currentPoint, &trackRect)) {
		short pixDiff;

		if (scrollPtr->vertical) {
		    pixDiff = currentPoint.v - mouseDownPoint.v;
		} else {
		    pixDiff = currentPoint.h - mouseDownPoint.h;
		}
		newFirstFraction += (double)pixDiff / trackBarSize;
		if (newFirstFraction > 1.0) {
		    newFirstFraction = 1.0;
		} else if (newFirstFraction < 0.0) {
		    newFirstFraction = 0.0;
		}
	    }

	    /*
	     * Move the scrollbar thumb to the new first fraction given
	     * its position when initially pressed and how far the mouse
	     * has moved. Process waiting idle tasks afterward to allow
	     * for the display to update.
	     */

	    sprintf(valueString, "%g", newFirstFraction);
	    Tcl_DStringSetLength(&cmdString, 0);
	    Tcl_DStringAppend(&cmdString, scrollPtr->command,
		scrollPtr->commandSize);
	    Tcl_DStringAppendElement(&cmdString, "moveto");
	    Tcl_DStringAppendElement(&cmdString, valueString);
	    interp = scrollPtr->interp;
	    Tcl_Preserve((ClientData) interp);
	    Tcl_EvalEx(interp, Tcl_DStringValue(&cmdString),
		    Tcl_DStringLength(&cmdString), TCL_EVAL_GLOBAL);
	    Tcl_Release((ClientData) interp);
	    TkMacOSXRunTclEventLoop();
	}
    } while ((err == noErr) && trackingResult != kMouseTrackingMouseReleased);
    TkMacOSXTrackingLoop(0);
    Tcl_DStringFree(&cmdString);
    return;
}

/*
 *--------------------------------------------------------------
 *
 * ScrollbarActionProc --
 *
 *	Callback procedure used by the Macintosh toolbox call
 *	HandleControlClick. This call will update the display
 *	while the scrollbar is being manipulated by the user.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	May change the display.
 *
 *--------------------------------------------------------------
 */

static pascal void
ScrollbarActionProc(
    ControlRef theControl,	/* Handle to scrollbat control */
    ControlPartCode partCode)	/* Part of scrollbar that was "hit" */
{
    TkScrollbar *scrollPtr = (TkScrollbar *)(intptr_t)GetControlReference(
	    theControl);
    MacScrollbar *macScrollPtr = (MacScrollbar *) scrollPtr;
    Tcl_DString cmdString;

    Tcl_DStringInit(&cmdString);
    Tcl_DStringAppend(&cmdString, scrollPtr->command,
	    scrollPtr->commandSize);

    if ( partCode == kAppearancePartUpButton ||
	    partCode == kAppearancePartDownButton ) {
	Tcl_DStringAppendElement(&cmdString, "scroll");
	Tcl_DStringAppendElement(&cmdString,
		(partCode == kAppearancePartUpButton) ? "-1" : "1");
	Tcl_DStringAppendElement(&cmdString, "unit");
    } else if (partCode == kAppearancePartPageUpArea ||
	    partCode == kAppearancePartPageDownArea ) {
	Tcl_DStringAppendElement(&cmdString, "scroll");
	Tcl_DStringAppendElement(&cmdString,
		(partCode == kAppearancePartPageUpArea) ? "-1" : "1");
	Tcl_DStringAppendElement(&cmdString, "page");
    } else if (partCode == kAppearancePartIndicator) {
	char valueString[TCL_DOUBLE_SPACE];

	sprintf(valueString, "%g",
		(GetControl32BitValue(macScrollPtr->sbHandle) -
		MIN_SCROLLBAR_VALUE) / SCROLLBAR_SCALING_VALUE);
	Tcl_DStringAppendElement(&cmdString, "moveto");
	Tcl_DStringAppendElement(&cmdString, valueString);
    }
    Tcl_Preserve((ClientData) scrollPtr->interp);
    Tcl_EvalEx(scrollPtr->interp, Tcl_DStringValue(&cmdString),
	    Tcl_DStringLength(&cmdString), TCL_EVAL_GLOBAL);
    Tcl_Release((ClientData) scrollPtr->interp);
    Tcl_DStringFree(&cmdString);
    TkMacOSXRunTclEventLoop();
}

/*
 *--------------------------------------------------------------
 *
 * ScrollbarBindProc --
 *
 *	This procedure is invoked when the default <ButtonPress>
 *	binding on the Scrollbar bind tag fires.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	The event enters a modal loop.
 *
 *--------------------------------------------------------------
 */

static int
ScrollbarBindProc(
    ClientData clientData,	/* Not used. */
    Tcl_Interp *interp,		/* Interp with binding. */
    XEvent *eventPtr,		/* X event that triggered binding. */
    Tk_Window tkwin,		/* Target window for event. */
    KeySym keySym)		/* The KeySym if a key event. */
{
    TkWindow *winPtr = (TkWindow*)tkwin;
    TkScrollbar *scrollPtr = (TkScrollbar *) winPtr->instanceData;
    MacScrollbar *macScrollPtr = (MacScrollbar *) winPtr->instanceData;

    Tcl_Preserve((ClientData)scrollPtr);
    macScrollPtr->macFlags |= IN_MODAL_LOOP;

    if (eventPtr->type == ButtonPress) {
	Point where;
	Rect bounds;
	ControlPartCode part;
	CGrafPtr destPort, savePort;
	Boolean portChanged;
	Window window;

	/*
	 * To call Macintosh control routines we must have the port
	 * set to the window containing the control. We will then test
	 * which part of the control was hit and act accordingly.
	 */
	destPort = TkMacOSXGetDrawablePort(Tk_WindowId(scrollPtr->tkwin));
	portChanged = QDSwapPort(destPort, &savePort);
	TkMacOSXSetUpClippingRgn(Tk_WindowId(scrollPtr->tkwin));

	TkMacOSXWinBounds((TkWindow *) scrollPtr->tkwin, &bounds);
	where.h = eventPtr->xbutton.x + bounds.left;
	where.v = eventPtr->xbutton.y + bounds.top;
	part = TestControl(macScrollPtr->sbHandle, where);
	TkMacOSXTrackingLoop(1);
	if (part == kAppearancePartIndicator && scrollPtr->jump == false) {
	    /*
	     * Case 1: In thumb, no jump scrolling. Call track control
	     * with the thumb action proc which will do most of the work.
	     */
	    mouseDownPoint.h = where.h;
	    mouseDownPoint.v = where.v;
	    part = HandleControlClick(macScrollPtr->sbHandle, where,
		    TkMacOSXModifierState(), thumbActionProc);
	} else if (part == kAppearancePartIndicator) {
	    /*
	     * Case 2: in thumb with jump scrolling. Call HandleControlClick
	     * with a NULL action proc. Use the new value of the control
	     * to set update the control.
	     */
	    part = HandleControlClick(macScrollPtr->sbHandle, where,
		    TkMacOSXModifierState(), NULL);
	    if (part == kAppearancePartIndicator) {
		Tcl_DString cmdString;
		char valueString[TCL_DOUBLE_SPACE];

		sprintf(valueString, "%g",
			(GetControl32BitValue(macScrollPtr->sbHandle) -
			MIN_SCROLLBAR_VALUE) / SCROLLBAR_SCALING_VALUE);
		Tcl_DStringInit(&cmdString);
		Tcl_DStringAppend(&cmdString, scrollPtr->command,
			strlen(scrollPtr->command));
		Tcl_DStringAppendElement(&cmdString, "moveto");
		Tcl_DStringAppendElement(&cmdString, valueString);

		interp = scrollPtr->interp;
		Tcl_Preserve((ClientData) interp);
		Tcl_EvalEx(interp, Tcl_DStringValue(&cmdString),
			Tcl_DStringLength(&cmdString), TCL_EVAL_GLOBAL);
		Tcl_Release((ClientData) interp);
		Tcl_DStringFree(&cmdString);
		TkMacOSXRunTclEventLoop();
	    }
	} else if (part != 0) {
	    /*
	     * Case 3: in any other part of the scrollbar. We call
	     * HandleControlClick with the scrollActionProc which will do
	     * most all the work.
	     */
	    HandleControlClick(macScrollPtr->sbHandle, where,
		    TkMacOSXModifierState(), scrollActionProc);
	    /*
	     * Workaround for Carbon bug where the scrollbar down arrow
	     * sometimes gets "stuck" after the mousebutton has been released.
	     */
	    if (scrollPtr->tkwin) {
		TkMacOSXSetUpClippingRgn(Tk_WindowId(scrollPtr->tkwin));
	    }
	    Draw1Control(macScrollPtr->sbHandle);
	}
	TkMacOSXTrackingLoop(0);

	/*
	 * The HandleControlClick call will "eat" the ButtonUp event. We now
	 * generate a ButtonUp event so Tk will unset implicit grabs etc.
	 */

	if (scrollPtr->tkwin) {
	    window = Tk_WindowId(scrollPtr->tkwin);
	    TkGenerateButtonEventForXPointer(window);
	}

	if (portChanged) {
	    QDSwapPort(savePort, NULL);
	}
    }

    if (macScrollPtr->sbHandle && (macScrollPtr->macFlags & ALREADY_DEAD)) {
	DisposeControl(macScrollPtr->sbHandle);
	macScrollPtr->sbHandle = NULL;
    }
    macScrollPtr->macFlags &= ~IN_MODAL_LOOP;
    Tcl_Release((ClientData)scrollPtr);

    return TCL_OK;
}

/*
 *--------------------------------------------------------------
 *
 * ScrollbarEventProc --
 *
 *	This procedure is invoked by the Tk dispatcher for various
 *	events on scrollbars.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	When the window gets deleted, internal structures get
 *	cleaned up. When it gets exposed, it is redisplayed.
 *
 *--------------------------------------------------------------
 */

static void
ScrollbarEventProc(
    ClientData clientData,	/* Information about window. */
    XEvent *eventPtr)		/* Information about event. */
{
    TkScrollbar *scrollPtr = (TkScrollbar *) clientData;
    MacScrollbar *macScrollPtr = (MacScrollbar *) clientData;

    if (eventPtr->type == UnmapNotify) {
	TkMacOSXSetScrollbarGrow((TkWindow *) scrollPtr->tkwin, false);
    } else if (eventPtr->type == ActivateNotify) {
	macScrollPtr->macFlags |= ACTIVE;
	TkScrollbarEventuallyRedraw((ClientData) scrollPtr);
    } else if (eventPtr->type == DeactivateNotify) {
	macScrollPtr->macFlags &= ~ACTIVE;
	TkScrollbarEventuallyRedraw((ClientData) scrollPtr);
    } else {
	TkScrollbarEventProc(clientData, eventPtr);
    }
}

/*
 *--------------------------------------------------------------
 *
 * UpdateControlValues --
 *
 *	This procedure updates the Macintosh scrollbar control
 *	to display the values defined by the Tk scrollbar.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	The Macintosh control is updated.
 *
 *--------------------------------------------------------------
 */

static void
UpdateControlValues(
    MacScrollbar *macScrollPtr)		/* Scrollbar data struct. */
{
    TkScrollbar *scrollPtr = (TkScrollbar *) macScrollPtr;
    Tk_Window tkwin = scrollPtr->tkwin;
    MacDrawable * macDraw = (MacDrawable *) Tk_WindowId(scrollPtr->tkwin);
    double dViewSize;
    Rect contrlRect, portRect;
    int variant, active;
    short width, height;

    contrlRect.left   = macDraw->xOff + scrollPtr->inset;
    contrlRect.top    = macDraw->yOff + scrollPtr->inset;
    contrlRect.right  = macDraw->xOff + Tk_Width(tkwin) - scrollPtr->inset;
    contrlRect.bottom = macDraw->yOff + Tk_Height(tkwin) - scrollPtr->inset;

    GetPortBounds (GetWindowPort(GetControlOwner(macScrollPtr->sbHandle)),
	    &portRect);

    /*
     * If the scrollbar is flush against the bottom right hand corner then
     * we leave space to draw the grow region for the window.
     */
    if (portRect.bottom == contrlRect.bottom &&
	    portRect.right == contrlRect.right) {
	TkMacOSXSetScrollbarGrow((TkWindow *) tkwin, true);
	if (macDraw->toplevel &&
		TkMacOSXResizable(macDraw->toplevel->winPtr)) {
	    int growSize;

	    switch (TkMacOSXWindowClass(macDraw->toplevel->winPtr)) {
		case kFloatingWindowClass:
		case kUtilityWindowClass:
		    growSize = metrics[1].width - 1;
		    break;
		case kDocumentWindowClass:
		case kMovableAlertWindowClass:
		case kMovableModalWindowClass:
		default:
		    growSize = metrics[0].width - 1;
		    break;
	    }
	    if (scrollPtr->vertical) {
		contrlRect.bottom -= growSize;
	    } else {
		contrlRect.right -= growSize;
	    }
	}
    } else {
	TkMacOSXSetScrollbarGrow((TkWindow *) tkwin, false);
    }

    if (IsControlVisible (macScrollPtr->sbHandle)) {
	SetControlVisibility(macScrollPtr->sbHandle, false, false);
    }

    if (scrollPtr->vertical) {
	width  = contrlRect.right - contrlRect.left;
	height = contrlRect.bottom - contrlRect.top;
    } else {
	width  = contrlRect.bottom - contrlRect.top;
	height = contrlRect.right - contrlRect.left;
    }
    variant = width < metrics[0].width ? 1 : 0;
    SetControlData(macScrollPtr->sbHandle, kControlEntireControl,
	    kControlSizeTag, sizeof(ControlSize),
	    &(metrics[variant].size));

    macScrollPtr->eraseRect = contrlRect;
    if (scrollPtr->vertical) {
	macScrollPtr->eraseRect.left += metrics[variant].width;
    } else {
	macScrollPtr->eraseRect.top  += metrics[variant].width;
    }

    /*
     * Ensure we set scrollbar control bounds only once all size
     * adjustments have been computed.
     */

    SetControlBounds(macScrollPtr->sbHandle, &contrlRect);

    /*
     * Given the Tk parameters for the fractions of the start and
     * end of the thumb, the following calculation determines the
     * location for the Macintosh thumb.
     * The Aqua scroll control works as follows.
     * The scrollbar's value is the position of the left (or top) side of
     * the view area in the content area being scrolled.
     * The maximum value of the control is therefore the dimension of
     * the content area less the size of the view area.
     * Since these values are all integers, and Tk gives the thumb position
     * as fractions, we have introduced a scaling factor.
     */

    dViewSize = (scrollPtr->lastFraction - scrollPtr->firstFraction)
	    * SCROLLBAR_SCALING_VALUE;
    SetControl32BitMinimum(macScrollPtr->sbHandle, MIN_SCROLLBAR_VALUE);
    SetControl32BitMaximum(macScrollPtr->sbHandle, MIN_SCROLLBAR_VALUE +
	    SCROLLBAR_SCALING_VALUE - dViewSize);
    SetControlViewSize(macScrollPtr->sbHandle, dViewSize);
    SetControl32BitValue(macScrollPtr->sbHandle, MIN_SCROLLBAR_VALUE +
	    SCROLLBAR_SCALING_VALUE * scrollPtr->firstFraction);

    if((scrollPtr->firstFraction <= 0.0 && scrollPtr->lastFraction >= 1.0)
	    || height <= metrics[variant].minHeight) {
	/* Disable scrollbar */
	SetControl32BitMaximum(macScrollPtr->sbHandle, MIN_SCROLLBAR_VALUE);
    }
    active = ((macScrollPtr->macFlags & ACTIVE) != 0);
    if (active != IsControlActive(macScrollPtr->sbHandle)) {
	if (active) {
	    ActivateControl(macScrollPtr->sbHandle);
	} else {
	    DeactivateControl(macScrollPtr->sbHandle);
	}
    }
    SetControlVisibility(macScrollPtr->sbHandle, true, false);
}
