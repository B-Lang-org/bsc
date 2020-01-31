/*
 * tkMacOSXWindowEvent.c --
 *
 *	This file defines the routines for both creating and handling
 *	Window Manager class events for Tk.
 *
 * Copyright 2001, Apple Computer, Inc.
 * Copyright (c) 2005-2007 Daniel A. Steffen <das@users.sourceforge.net>
 *
 * See the file "license.terms" for information on usage and redistribution of
 * this file, and for a DISCLAIMER OF ALL WARRANTIES.
 *
 *	The following terms apply to all files originating from Apple
 *	Computer, Inc. ("Apple") and associated with the software
 *	unless explicitly disclaimed in individual files.
 *
 *
 *	Apple hereby grants permission to use, copy, modify,
 *	distribute, and license this software and its documentation
 *	for any purpose, provided that existing copyright notices are
 *	retained in all copies and that this notice is included
 *	verbatim in any distributions. No written agreement, license,
 *	or royalty fee is required for any of the authorized
 *	uses. Modifications to this software may be copyrighted by
 *	their authors and need not follow the licensing terms
 *	described here, provided that the new terms are clearly
 *	indicated on the first page of each file where they apply.
 *
 *
 *	IN NO EVENT SHALL APPLE, THE AUTHORS OR DISTRIBUTORS OF THE
 *	SOFTWARE BE LIABLE TO ANY PARTY FOR DIRECT, INDIRECT, SPECIAL,
 *	INCIDENTAL, OR CONSEQUENTIAL DAMAGES ARISING OUT OF THE USE OF
 *	THIS SOFTWARE, ITS DOCUMENTATION, OR ANY DERIVATIVES THEREOF,
 *	EVEN IF APPLE OR THE AUTHORS HAVE BEEN ADVISED OF THE
 *	POSSIBILITY OF SUCH DAMAGE.  APPLE, THE AUTHORS AND
 *	DISTRIBUTORS SPECIFICALLY DISCLAIM ANY WARRANTIES, INCLUDING,
 *	BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY,
 *	FITNESS FOR A PARTICULAR PURPOSE, AND NON-INFRINGEMENT.	 THIS
 *	SOFTWARE IS PROVIDED ON AN "AS IS" BASIS, AND APPLE,THE
 *	AUTHORS AND DISTRIBUTORS HAVE NO OBLIGATION TO PROVIDE
 *	MAINTENANCE, SUPPORT, UPDATES, ENHANCEMENTS, OR MODIFICATIONS.
 *
 *	GOVERNMENT USE: If you are acquiring this software on behalf
 *	of the U.S. government, the Government shall have only
 *	"Restricted Rights" in the software and related documentation
 *	as defined in the Federal Acquisition Regulations (FARs) in
 *	Clause 52.227.19 (c) (2).  If you are acquiring the software
 *	on behalf of the Department of Defense, the software shall be
 *	classified as "Commercial Computer Software" and the
 *	Government shall have only "Restricted Rights" as defined in
 *	Clause 252.227-7013 (c) (1) of DFARs.  Notwithstanding the
 *	foregoing, the authors grant the U.S. Government and others
 *	acting in its behalf permission to use and distribute the
 *	software in accordance with the terms specified in this
 *	license.
 *
 * RCS: @(#) $Id: tkMacOSXWindowEvent.c,v 1.31.2.1 2008/06/19 00:11:17 das Exp $
 */

#include "tkMacOSXPrivate.h"
#include "tkMacOSXWm.h"
#include "tkMacOSXEvent.h"
#include "tkMacOSXDebug.h"

/*
#ifdef TK_MAC_DEBUG
#define TK_MAC_DEBUG_CLIP_REGIONS
#endif
*/

/*
 * Declaration of functions used only in this file
 */

static int GenerateUpdateEvent(Window window);
static int GenerateUpdates(HIMutableShapeRef updateRgn, CGRect *updateBounds,
	TkWindow *winPtr);
static int GenerateActivateEvents(Window window, int activeFlag);
static void ClearPort(CGrafPtr port, HIShapeRef updateRgn);


/*
 *----------------------------------------------------------------------
 *
 * TkMacOSXProcessApplicationEvent --
 *
 *	This processes Application level events, mainly activate
 *	and deactivate.
 *
 * Results:
 *	0.
 *
 * Side effects:
 *	Hide or reveal floating windows.
 *
 *----------------------------------------------------------------------
 */

MODULE_SCOPE int
TkMacOSXProcessApplicationEvent(
	TkMacOSXEvent *eventPtr,
	MacEventStatus *statusPtr)
{
    Tcl_CmdInfo dummy;

    /*
     * This is a bit of a hack. We get "show" events both when we come back
     * from being hidden, and whenever we are activated. I only want to run
     * the "show" proc when we have been hidden already, not as a substitute
     * for <Activate>. So I use this toggle...
     */
    static int toggleHide = 0;

    switch (eventPtr->eKind) {
	case kEventAppActivated:
	    ShowFloatingWindows();
	    break;
	case kEventAppDeactivated:
	    TkSuspendClipboard();
	    HideFloatingWindows();
	    break;
	case kEventAppQuit:
	    statusPtr->stopProcessing = 1;
	    break;
	case kEventAppHidden:
	    if (toggleHide == 0) {
		toggleHide = 1;
		if (eventPtr->interp && Tcl_GetCommandInfo(eventPtr->interp,
			"::tk::mac::OnHide", &dummy)) {
		    Tcl_GlobalEval(eventPtr->interp, "::tk::mac::OnHide");
		}
	    }
	    statusPtr->stopProcessing = 1;
	    break;
	case kEventAppShown:
	    if (toggleHide == 1) {
		toggleHide = 0;
		if (eventPtr->interp && Tcl_GetCommandInfo(eventPtr->interp,
			"::tk::mac::OnShow", &dummy)) {
		    Tcl_GlobalEval(eventPtr->interp, "::tk::mac::OnShow");
		}
	    }
	    statusPtr->stopProcessing = 1;
	    break;
	case kEventAppAvailableWindowBoundsChanged: {
	    static UInt32 prevId = 0;
	    UInt32 id;
	    OSStatus err;

	    err = ChkErr(GetEventParameter, eventPtr->eventRef,
		    kEventParamTransactionID, typeUInt32,
		    NULL, sizeof(id), NULL, &id);
	    if (err != noErr || id != prevId) {
		TkDisplay *dispPtr = TkGetDisplayList();

		prevId = id;
		TkMacOSXDisplayChanged(dispPtr->display);
	    }
	    /*
	     * Should we call ::tk::mac::OnDisplayChanged?
	     */
	    break;
	}
	default:
	    break;
    }
    return 0;
}

/*
 *----------------------------------------------------------------------
 *
 * TkMacOSXProcessAppearanceEvent --
 *
 *	This processes Appearance events.
 *
 * Results:
 *	0.
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */

MODULE_SCOPE int
TkMacOSXProcessAppearanceEvent(
	TkMacOSXEvent *eventPtr,
	MacEventStatus *statusPtr)
{
    switch (eventPtr->eKind) {
	case kEventAppearanceScrollBarVariantChanged:
	    TkMacOSXInitScrollbarMetrics();
	    break;
	default:
	    break;
    }
    return 0;
}

/*
 *----------------------------------------------------------------------
 *
 * TkMacOSXProcessWindowEvent --
 *
 *	This processes Window level events, mainly activate
 *	and deactivate.
 *
 * Results:
 *	0.
 *
 * Side effects:
 *	Cause Windows to be moved forward or backward in the
 *	window stack.
 *
 *----------------------------------------------------------------------
 */

MODULE_SCOPE int
TkMacOSXProcessWindowEvent(
	TkMacOSXEvent * eventPtr,
	MacEventStatus * statusPtr)
{
    OSStatus err;
    WindowRef whichWindow;
    Window window;
    int eventFound = false;
    TkDisplay *dispPtr;
    TkWindow *winPtr;

    switch (eventPtr->eKind) {
	case kEventWindowActivated:
	case kEventWindowDeactivated:
	case kEventWindowUpdate:
	case kEventWindowExpanding:
	case kEventWindowBoundsChanged:
	case kEventWindowDragStarted:
	case kEventWindowDragCompleted:
	case kEventWindowConstrain:
	case kEventWindowGetRegion:
	case kEventWindowDrawContent:
	    break;
	default:
	    return 0;
	    break;
    }
    err = ChkErr(GetEventParameter, eventPtr->eventRef,
	    kEventParamDirectObject, typeWindowRef, NULL, sizeof(whichWindow),
	    NULL, &whichWindow);
    if (err != noErr) {
	return 0;
    }

    window = TkMacOSXGetXWindow(whichWindow);
    dispPtr = TkGetDisplayList();
    winPtr = (TkWindow *)Tk_IdToWindow(dispPtr->display, window);

    switch (eventPtr->eKind) {
	case kEventWindowActivated:
	case kEventWindowDeactivated:
	    if (window != None) {
		int activate = (eventPtr->eKind == kEventWindowActivated);

		eventFound |= GenerateActivateEvents(window, activate);
		eventFound |= TkMacOSXGenerateFocusEvent(window, activate);
		if (winPtr) {
		    TkMacOSXEnterExitFullscreen(winPtr, activate);
		}
		statusPtr->stopProcessing = 1;
	    }
	    break;
	case kEventWindowUpdate:
	    if (window != None && GenerateUpdateEvent(window)) {
		eventFound = true;
		statusPtr->stopProcessing = 1;
	    }
	    break;
	case kEventWindowExpanding:
	    if (winPtr) {
		winPtr->wmInfoPtr->hints.initial_state =
			TkMacOSXIsWindowZoomed(winPtr) ? ZoomState : 
			NormalState;
		Tk_MapWindow((Tk_Window) winPtr);
		/*
		 * Need to process all Tk events generated by Tk_MapWindow()
		 * before returning to ensure all children are mapped, as
		 * otherwise the Activate event that follows Expanding would
		 * not be processed by any unmapped children.
		 */
		while (Tcl_ServiceEvent(TCL_WINDOW_EVENTS)) {};
		while (Tcl_DoOneEvent(TCL_IDLE_EVENTS)) {};
	    }
	    break;
	case kEventWindowBoundsChanged:
	    if (winPtr) {
		WmInfo *wmPtr = winPtr->wmInfoPtr;
		UInt32 attr;
		Rect bounds;
		int x = -1, y = -1, width = -1, height = -1, flags = 0;

		ChkErr(GetEventParameter, eventPtr->eventRef,
			kEventParamAttributes, typeUInt32,
			NULL, sizeof(attr), NULL, &attr);
		ChkErr(GetEventParameter, eventPtr->eventRef,
			kEventParamCurrentBounds, typeQDRectangle,
			NULL, sizeof(bounds), NULL, &bounds);
		if (attr & kWindowBoundsChangeOriginChanged) {
		    x = bounds.left - wmPtr->xInParent;
		    y = bounds.top	- wmPtr->yInParent;
		    flags |= TK_LOCATION_CHANGED;
		}
		if (attr & kWindowBoundsChangeSizeChanged) {
		    width = bounds.right  - bounds.left;
		    height = bounds.bottom - bounds.top;
		    flags |= TK_SIZE_CHANGED;
		}
		TkMacOSXInvalClipRgns((Tk_Window) winPtr);
		TkMacOSXInvalidateWindow((MacDrawable *) window,
			TK_PARENT_WINDOW);
		TkGenWMConfigureEvent((Tk_Window)winPtr, x, y, width,
			height, flags);
		if (attr & kWindowBoundsChangeUserResize ||
			attr & kWindowBoundsChangeUserDrag) {
		    TkMacOSXRunTclEventLoop();
		}
		if (wmPtr->attributes & kWindowResizableAttribute) {
		    HIViewRef growBoxView;

		    err = HIViewFindByID(HIViewGetRoot(whichWindow),
			    kHIViewWindowGrowBoxID, &growBoxView);
		    if (err == noErr) {
			ChkErr(HIViewSetNeedsDisplay, growBoxView, true);
		    }
		}
	    }
	    break;
	case kEventWindowDragStarted:
	    if (!(TkMacOSXModifierState() & cmdKey)) { 
		TkMacOSXBringWindowForward(whichWindow);
	    }
	    TkMacOSXTrackingLoop(1);
	    break;
	case kEventWindowDragCompleted: {
	    Rect maxBounds, bounds, strWidths;
	    int h = 0, v = 0;

	    TkMacOSXTrackingLoop(0);
	    ChkErr(GetWindowGreatestAreaDevice, whichWindow,
		    kWindowDragRgn, NULL, &maxBounds);
	    ChkErr(GetWindowBounds, whichWindow, kWindowStructureRgn,
		    &bounds);
	    ChkErr(GetWindowStructureWidths, whichWindow, &strWidths);
	    if (bounds.left > maxBounds.right - strWidths.left) {
		h = maxBounds.right
			- (strWidths.left ? strWidths.left : 40)
			- bounds.left;
	    } else if (bounds.right < maxBounds.left
		    + strWidths.right) {
		h = maxBounds.left
			+ (strWidths.right ? strWidths.right : 40)
			- bounds.right;
	    }
	    if (bounds.top > maxBounds.bottom - strWidths.top) {
		v = maxBounds.bottom
			- (strWidths.top ? strWidths.top : 40)
			- bounds.top;
	    } else if (bounds.bottom < maxBounds.top
		    + strWidths.bottom) {
		v = maxBounds.top
			+ (strWidths.bottom ? strWidths.bottom : 40)
			- bounds.bottom;
	    } else if (strWidths.top && bounds.top < maxBounds.top) {
		v = maxBounds.top - bounds.top;
	    }
	    if (h || v) {
		OffsetRect(&bounds, h, v);
		ChkErr(SetWindowBounds, whichWindow,
		    kWindowStructureRgn, &bounds);
	    }
	    break;
	}
	case kEventWindowConstrain:
	    if (winPtr && (winPtr->wmInfoPtr->flags & WM_FULLSCREEN) &&
		    TkMacOSXMakeFullscreen(winPtr, whichWindow, 1,
		    NULL) == TCL_OK) {
		statusPtr->stopProcessing = 1;
	    }
	    break;
	case kEventWindowGetRegion:
	    if (winPtr && (winPtr->wmInfoPtr->flags & WM_TRANSPARENT)) {
		WindowRegionCode code;

		statusPtr->stopProcessing = (CallNextEventHandler(
			eventPtr->callRef, eventPtr->eventRef) == noErr);
		err = ChkErr(GetEventParameter, eventPtr->eventRef,
			kEventParamWindowRegionCode, typeWindowRegionCode,
			NULL, sizeof(code), NULL, &code);
		if (err == noErr && code == kWindowOpaqueRgn) {
		    RgnHandle rgn;

		    err = ChkErr(GetEventParameter, eventPtr->eventRef,
			    kEventParamRgnHandle, typeQDRgnHandle, NULL,
			    sizeof(rgn), NULL, &rgn);
		    if (err == noErr) {
			SetEmptyRgn(rgn);
			statusPtr->stopProcessing = 1;
		    }
		}
	    }
	    break;
	case kEventWindowDrawContent:
	    if (winPtr && (winPtr->wmInfoPtr->flags & WM_TRANSPARENT)) {
		CGrafPtr port;

		GetPort(&port);
		ClearPort(port, NULL);
	    }
	    break;
    }

    return eventFound;
}

/*
 *----------------------------------------------------------------------
 *
 * GenerateUpdateEvent --
 *
 *	Given a Macintosh window update event this function generates
 *	all the Expose XEvents needed by Tk.
 *
 * Results:
 *	True if event(s) are generated - false otherwise.
 *
 * Side effects:
 *	Additional events may be place on the Tk event queue.
 *
 *----------------------------------------------------------------------
 */
static int
GenerateUpdateEvent(Window window)
{
    WindowRef macWindow;
    TkDisplay *dispPtr;
    TkWindow  *winPtr;
    int result = 0;
    CGRect updateBounds;
    HIShapeRef rgn;
    HIMutableShapeRef updateRgn;
    int dx, dy;

    dispPtr = TkGetDisplayList();
    winPtr = (TkWindow *)Tk_IdToWindow(dispPtr->display, window);

    if (winPtr ==NULL ){
	return result;
    }
    macWindow = TkMacOSXDrawableWindow(window);
    TK_IF_MAC_OS_X_API (5, HIWindowCopyShape,
	ChkErr(HIWindowCopyShape, macWindow, kWindowUpdateRgn,
		kHICoordSpaceWindow, &rgn);
	dx = -winPtr->wmInfoPtr->xInParent;
	dy = -winPtr->wmInfoPtr->yInParent;
    ) TK_ELSE_MAC_OS_X (5,
	Rect bounds;

	TkMacOSXCheckTmpQdRgnEmpty();
	ChkErr(GetWindowRegion, macWindow, kWindowUpdateRgn, tkMacOSXtmpQdRgn);
	rgn = HIShapeCreateWithQDRgn(tkMacOSXtmpQdRgn);
	SetEmptyRgn(tkMacOSXtmpQdRgn);
	ChkErr(GetWindowBounds, macWindow, kWindowContentRgn, &bounds);
	dx = -bounds.left;
	dy = -bounds.top;
    ) TK_ENDIF
    updateRgn = HIShapeCreateMutableCopy(rgn);
    CFRelease(rgn);
    ChkErr(HIShapeOffset, updateRgn, dx, dy);
    HIShapeGetBounds(updateRgn, &updateBounds);
#ifdef TK_MAC_DEBUG_CLIP_REGIONS
    TkMacOSXDebugFlashRegion(window, updateRgn);
#endif /* TK_MAC_DEBUG_CLIP_REGIONS */
    BeginUpdate(macWindow);
    if (winPtr->wmInfoPtr->flags & WM_TRANSPARENT) {
	ClearPort(TkMacOSXGetDrawablePort(window), updateRgn);
    }
    result = GenerateUpdates(updateRgn, &updateBounds, winPtr);
    EndUpdate(macWindow);
    CFRelease(updateRgn);
    if (result) {
	/*
	 * Ensure there are no pending idle-time redraws that could prevent
	 * the just posted Expose events from generating new redraws.
	 */

	Tcl_DoOneEvent(TCL_IDLE_EVENTS|TCL_DONT_WAIT);
    }
    return result;
 }

/*
 *----------------------------------------------------------------------
 *
 * GenerateUpdates --
 *
 *	Given a Macintosh update region and a Tk window this function
 *	geneates a X Expose event for the window if it is within the
 *	update region. The function will then recursivly have each
 *	damaged window generate Expose events for its child windows.
 *
 * Results:
 *	True if event(s) are generated - false otherwise.
 *
 * Side effects:
 *	Additional events may be place on the Tk event queue.
 *
 *----------------------------------------------------------------------
 */

static int
GenerateUpdates(
    HIMutableShapeRef updateRgn,
    CGRect *updateBounds,
    TkWindow *winPtr)
{
    TkWindow *childPtr;
    XEvent event;
    CGRect bounds, damageBounds;
    HIShapeRef boundsRgn, damageRgn;

    TkMacOSXWinCGBounds(winPtr, &bounds);
    if (!CGRectIntersectsRect(bounds, *updateBounds)) {
	return 0;
    }
    TK_IF_MAC_OS_X_API (4, HIShapeIntersectsRect,
	if (!HIShapeIntersectsRect(updateRgn, &bounds)) {
	    return 0;
	}
    ) TK_ENDIF

    /*
     * Compute the bounding box of the area that the damage occured in.
     */

    boundsRgn = HIShapeCreateWithRect(&bounds);
    damageRgn = HIShapeCreateIntersection(updateRgn, boundsRgn);
    if (HIShapeIsEmpty(damageRgn)) {
	CFRelease(damageRgn);
	CFRelease(boundsRgn);
	return 0;
    }
    HIShapeGetBounds(damageRgn, &damageBounds);
    ChkErr(TkMacOSHIShapeUnion, boundsRgn, updateRgn, updateRgn);
    HIShapeGetBounds(updateRgn, updateBounds);
    CFRelease(damageRgn);
    CFRelease(boundsRgn);

    event.xany.serial = Tk_Display(winPtr)->request;
    event.xany.send_event = false;
    event.xany.window = Tk_WindowId(winPtr);
    event.xany.display = Tk_Display(winPtr);
    event.type = Expose;
    event.xexpose.x = damageBounds.origin.x - bounds.origin.x;
    event.xexpose.y = damageBounds.origin.y - bounds.origin.y;
    event.xexpose.width = damageBounds.size.width;
    event.xexpose.height = damageBounds.size.height;
    event.xexpose.count = 0;
    Tk_QueueWindowEvent(&event, TCL_QUEUE_TAIL);

    /*
     * Generate updates for the children of this window
     */

    for (childPtr = winPtr->childList; childPtr != NULL;
	    childPtr = childPtr->nextPtr) {
	if (!Tk_IsMapped(childPtr) || Tk_IsTopLevel(childPtr)) {
	    continue;
	}
	GenerateUpdates(updateRgn, updateBounds, childPtr);
    }

    /*
     * Generate updates for any contained windows
     */

    if (Tk_IsContainer(winPtr)) {
	childPtr = TkpGetOtherWindow(winPtr);
	if (childPtr != NULL && Tk_IsMapped(childPtr)) {
	    GenerateUpdates(updateRgn, updateBounds, childPtr);
	}

	/*
	 * TODO: Here we should handle out of process embedding.
	 */
    }

    return 1;
}

/*
 *----------------------------------------------------------------------
 *
 * GenerateActivateEvents --
 *
 *	Given a Macintosh window activate event this function generates all the
 *	X Activate events needed by Tk.
 *
 * Results:
 *	True if event(s) are generated - false otherwise.
 *
 * Side effects:
 *	Additional events may be place on the Tk event queue.
 *
 *----------------------------------------------------------------------
 */

int
GenerateActivateEvents(
    Window window,		  /* Root X window for event. */
    int activeFlag )
{
    TkWindow *winPtr;
    TkDisplay *dispPtr;

    dispPtr = TkGetDisplayList();
    winPtr = (TkWindow *) Tk_IdToWindow(dispPtr->display, window);
    if (winPtr == NULL || winPtr->window == None) {
	return false;
    }

    TkGenerateActivateEvents(winPtr,activeFlag);
    return true;
}

/*
 *----------------------------------------------------------------------
 *
 * TkMacOSXGenerateFocusEvent --
 *
 *	Given a Macintosh window activate event this function generates all the
 *	X Focus events needed by Tk.
 *
 * Results:
 *	True if event(s) are generated - false otherwise.
 *
 * Side effects:
 *	Additional events may be place on the Tk event queue.
 *
 *----------------------------------------------------------------------
 */

MODULE_SCOPE int
TkMacOSXGenerateFocusEvent(
    Window window,		/* Root X window for event. */
    int activeFlag )
{
    XEvent event;
    Tk_Window tkwin;
    TkDisplay *dispPtr;

    dispPtr = TkGetDisplayList();
    tkwin = Tk_IdToWindow(dispPtr->display, window);
    if (tkwin == NULL) {
	return false;
    }

    /*
     * Don't send focus events to windows of class help or to
     * windows with the kWindowNoActivatesAttribute.
     */
    if (((TkWindow *)tkwin)->wmInfoPtr->macClass == kHelpWindowClass ||
	    ((TkWindow *)tkwin)->wmInfoPtr->attributes &
		    kWindowNoActivatesAttribute) {
	return false;
    }

    /*
     * Generate FocusIn and FocusOut events. This event
     * is only sent to the toplevel window.
     */

    if (activeFlag) {
	event.xany.type = FocusIn;
    } else {
	event.xany.type = FocusOut;
    }

    event.xany.serial = dispPtr->display->request;
    event.xany.send_event = False;
    event.xfocus.display = dispPtr->display;
    event.xfocus.window = window;
    event.xfocus.mode = NotifyNormal;
    event.xfocus.detail = NotifyDetailNone;

    Tk_QueueWindowEvent(&event, TCL_QUEUE_TAIL);
    return true;
}

/*
 *----------------------------------------------------------------------
 *
 * TkGenWMConfigureEvent --
 *
 *	Generate a ConfigureNotify event for Tk. Depending on the
 *	value of flag the values of width/height, x/y, or both may
 *	be changed.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	A ConfigureNotify event is sent to Tk.
 *
 *----------------------------------------------------------------------
 */

void
TkGenWMConfigureEvent(
    Tk_Window tkwin,
    int x,
    int y,
    int width,
    int height,
    int flags)
{
    XEvent event;
    WmInfo *wmPtr;
    TkWindow *winPtr = (TkWindow *) tkwin;

    if (tkwin == NULL) {
	return;
    }

    event.type = ConfigureNotify;
    event.xconfigure.serial = Tk_Display(tkwin)->request;
    event.xconfigure.send_event = False;
    event.xconfigure.display = Tk_Display(tkwin);
    event.xconfigure.event = Tk_WindowId(tkwin);
    event.xconfigure.window = Tk_WindowId(tkwin);
    event.xconfigure.border_width = winPtr->changes.border_width;
    event.xconfigure.override_redirect = winPtr->atts.override_redirect;
    if (winPtr->changes.stack_mode == Above) {
	event.xconfigure.above = winPtr->changes.sibling;
    } else {
	event.xconfigure.above = None;
    }

    if (!(flags & TK_LOCATION_CHANGED)) {
	x = Tk_X(tkwin);
	y = Tk_Y(tkwin);
    }
    if (!(flags & TK_SIZE_CHANGED)) {
	width = Tk_Width(tkwin);
	height = Tk_Height(tkwin);
    }
    event.xconfigure.x = x;
    event.xconfigure.y = y;
    event.xconfigure.width = width;
    event.xconfigure.height = height;

    Tk_QueueWindowEvent(&event, TCL_QUEUE_TAIL);

    /*
     * Update window manager information.
     */
    if (Tk_IsTopLevel(winPtr)) {
	wmPtr = winPtr->wmInfoPtr;
	if (flags & TK_LOCATION_CHANGED) {
	    wmPtr->x = x;
	    wmPtr->y = y;
	    wmPtr->flags &= ~(WM_NEGATIVE_X | WM_NEGATIVE_Y);
	}
	if ((flags & TK_SIZE_CHANGED) && !(wmPtr->flags & WM_SYNC_PENDING) &&
		((width != Tk_Width(tkwin)) || (height != Tk_Height(tkwin)))) {
	    if ((wmPtr->width == -1) && (width == winPtr->reqWidth)) {
		/*
		 * Don't set external width, since the user didn't change it
		 * from what the widgets asked for.
		 */
	    } else {
		if (wmPtr->gridWin != NULL) {
		    wmPtr->width = wmPtr->reqGridWidth
			+ (width - winPtr->reqWidth)/wmPtr->widthInc;
		    if (wmPtr->width < 0) {
			wmPtr->width = 0;
		    }
		} else {
		    wmPtr->width = width;
		}
	    }
	    if ((wmPtr->height == -1) && (height == winPtr->reqHeight)) {
		/*
		 * Don't set external height, since the user didn't change it
		 * from what the widgets asked for.
		 */
	    } else {
		if (wmPtr->gridWin != NULL) {
		    wmPtr->height = wmPtr->reqGridHeight
			+ (height - winPtr->reqHeight)/wmPtr->heightInc;
		    if (wmPtr->height < 0) {
			wmPtr->height = 0;
		    }
		} else {
		    wmPtr->height = height;
		}
	    }
	    wmPtr->configWidth = width;
	    wmPtr->configHeight = height;
	}
    }

    /*
     * Now set up the changes structure. Under X we wait for the
     * ConfigureNotify to set these values. On the Mac we know imediatly that
     * this is what we want - so we just set them. However, we need to
     * make sure the windows clipping region is marked invalid so the
     * change is visible to the subwindow.
     */
    winPtr->changes.x = x;
    winPtr->changes.y = y;
    winPtr->changes.width = width;
    winPtr->changes.height = height;
    TkMacOSXInvalClipRgns(tkwin);
}

/*
 *----------------------------------------------------------------------
 *
 * TkGenWMDestroyEvent --
 *
 *	Generate a WM Destroy event for Tk.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	A WM_PROTOCOL/WM_DELETE_WINDOW event is sent to Tk.
 *
 *----------------------------------------------------------------------
 */

void
TkGenWMDestroyEvent(
    Tk_Window tkwin)
{
    XEvent event;

    event.xany.serial = Tk_Display(tkwin)->request;
    event.xany.send_event = False;
    event.xany.display = Tk_Display(tkwin);

    event.xclient.window = Tk_WindowId(tkwin);
    event.xclient.type = ClientMessage;
    event.xclient.message_type = Tk_InternAtom(tkwin, "WM_PROTOCOLS");
    event.xclient.format = 32;
    event.xclient.data.l[0] = Tk_InternAtom(tkwin, "WM_DELETE_WINDOW");
    Tk_QueueWindowEvent(&event, TCL_QUEUE_TAIL);
}

/*
 *----------------------------------------------------------------------
 *
 * TkWmProtocolEventProc --
 *
 *	This procedure is called by the Tk_HandleEvent whenever a
 *	ClientMessage event arrives whose type is "WM_PROTOCOLS".
 *	This procedure handles the message from the window manager
 *	in an appropriate fashion.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	Depends on what sort of handler, if any, was set up for the
 *	protocol.
 *
 *----------------------------------------------------------------------
 */

void
TkWmProtocolEventProc(
    TkWindow *winPtr,		/* Window to which the event was sent. */
    XEvent *eventPtr)		/* X event. */
{
    WmInfo *wmPtr;
    ProtocolHandler *protPtr;
    Tcl_Interp *interp;
    Atom protocol;
    int result;

    wmPtr = winPtr->wmInfoPtr;
    if (wmPtr == NULL) {
	return;
    }
    protocol = (Atom) eventPtr->xclient.data.l[0];
    for (protPtr = wmPtr->protPtr; protPtr != NULL;
		protPtr = protPtr->nextPtr) {
	if (protocol == protPtr->protocol) {
	    Tcl_Preserve((ClientData) protPtr);
	    interp = protPtr->interp;
	    Tcl_Preserve((ClientData) interp);
	    result = Tcl_GlobalEval(interp, protPtr->command);
	    if (result != TCL_OK) {
		Tcl_AddErrorInfo(interp, "\n    (command for \"");
		Tcl_AddErrorInfo(interp,
			Tk_GetAtomName((Tk_Window) winPtr, protocol));
		Tcl_AddErrorInfo(interp, "\" window manager protocol)");
		Tk_BackgroundError(interp);
	    }
	    Tcl_Release((ClientData) interp);
	    Tcl_Release((ClientData) protPtr);
	    return;
	}
    }

    /*
     * No handler was present for this protocol. If this is a
     * WM_DELETE_WINDOW message then just destroy the window.
     */

    if (protocol == Tk_InternAtom((Tk_Window) winPtr, "WM_DELETE_WINDOW")) {
	Tk_DestroyWindow((Tk_Window) winPtr);
    }
}

/*
 *----------------------------------------------------------------------
 *
 * Tk_MacOSXIsAppInFront --
 *
 *	Returns 1 if this app is the foreground app.
 *
 * Results:
 *	1 if app is in front, 0 otherwise.
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */

int
Tk_MacOSXIsAppInFront(void)
{
    OSStatus err;
    ProcessSerialNumber frontPsn, ourPsn = {0, kCurrentProcess};
    Boolean isFrontProcess = true;

    err = ChkErr(GetFrontProcess, &frontPsn);
    if (err == noErr) {
	ChkErr(SameProcess, &frontPsn, &ourPsn, &isFrontProcess);
    }
    
    return (isFrontProcess == true);
}

/*
 *----------------------------------------------------------------------
 *
 * ClearPort --
 *
 *	Clear (i.e. fill with transparent color) the given port.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */
static void
ClearPort(
    CGrafPtr port,
    HIShapeRef updateRgn)
{
    CGContextRef context;
    Rect bounds;
    CGRect rect;

    GetPortBounds(port, &bounds);
    QDBeginCGContext(port, &context);
    SyncCGContextOriginWithPort(context, port);
    CGContextConcatCTM(context, CGAffineTransformMake(1.0, 0.0, 0.0, -1.0, 0.0,
	    bounds.bottom - bounds.top));
    if (updateRgn) {
	ChkErr(HIShapeReplacePathInCGContext, updateRgn, context);
	CGContextEOClip(context);
    }
    rect = CGRectMake(0, 0, bounds.right, bounds.bottom);
    CGContextClearRect(context, rect);
    QDEndCGContext(port, &context);
}
