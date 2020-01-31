/*
 * tkMacOSXMouseEvent.c --
 *
 *	This file implements functions that decode & handle mouse events
 *	on MacOS X.
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
 * RCS: @(#) $Id: tkMacOSXMouseEvent.c,v 1.34 2007/12/13 15:27:10 dgp Exp $
 */

#include "tkMacOSXPrivate.h"
#include "tkMacOSXWm.h"
#include "tkMacOSXEvent.h"
#include "tkMacOSXDebug.h"

typedef struct {
    WindowRef	   whichWin;
    WindowRef	   activeNonFloating;
    WindowPartCode windowPart;
    unsigned int   state;
    long	   delta;
    Window	   window;
    Point	   global;
    Point	   local;
} MouseEventData;

/*
 * Declarations of static variables used in this file.
 */

static int gEatButtonUp = 0;	   /* 1 if we need to eat the next up event */

/*
 * Declarations of functions used only in this file.
 */

static void BringWindowForward(WindowRef wRef, int isFrontProcess,
	int frontWindowOnly);
static int GeneratePollingEvents(MouseEventData * medPtr);
static int GenerateMouseWheelEvent(MouseEventData * medPtr);
static int GenerateButtonEvent(MouseEventData * medPtr);
static int GenerateToolbarButtonEvent(MouseEventData * medPtr);
static int HandleWindowTitlebarMouseDown(MouseEventData * medPtr, Tk_Window tkwin);
static unsigned int ButtonModifiers2State(UInt32 buttonState, UInt32 keyModifiers);
static Tk_Window GetGrabWindowForWindow(Tk_Window tkwin);

static int TkMacOSXGetEatButtonUp(void);
static void TkMacOSXSetEatButtonUp(int f);


/*
 *----------------------------------------------------------------------
 *
 * TkMacOSXProcessMouseEvent --
 *
 *	This routine processes the event in eventPtr, and
 *	generates the appropriate Tk events from it.
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
TkMacOSXProcessMouseEvent(TkMacOSXEvent *eventPtr, MacEventStatus * statusPtr)
{
    Tk_Window tkwin;
    Point where, where2;
    int result;
    TkDisplay * dispPtr;
    OSStatus err;
    MouseEventData mouseEventData, * medPtr = &mouseEventData;
    int isFrontProcess;

    switch (eventPtr->eKind) {
	case kEventMouseDown:
	case kEventMouseUp:
	case kEventMouseMoved:
	case kEventMouseDragged:
	case kEventMouseWheelMoved:
	    break;
	default:
	    return false;
	    break;
    }
    err = ChkErr(GetEventParameter, eventPtr->eventRef,
	    kEventParamMouseLocation,
	    typeQDPoint, NULL,
	    sizeof(where), NULL,
	    &where);
    if (err != noErr) {
	GetGlobalMouse(&where);
    }
    err = ChkErr(GetEventParameter, eventPtr->eventRef,
	    kEventParamWindowRef,
	    typeWindowRef, NULL,
	    sizeof(WindowRef), NULL,
	    &medPtr->whichWin);
    if (err == noErr) {
	err = ChkErr(GetEventParameter, eventPtr->eventRef,
		kEventParamWindowPartCode,
		typeWindowPartCode, NULL,
		sizeof(WindowPartCode), NULL,
		&medPtr->windowPart);
    }
    if (err != noErr) {
	medPtr->windowPart = FindWindow(where, &medPtr->whichWin);
    }
    medPtr->window = TkMacOSXGetXWindow(medPtr->whichWin);
    if (medPtr->whichWin != NULL && medPtr->window == None) {
	return false;
    }
    if (eventPtr->eKind == kEventMouseDown) {
	if (IsWindowActive(medPtr->whichWin) && IsWindowPathSelectEvent(
		medPtr->whichWin, eventPtr->eventRef)) {
	    ChkErr(WindowPathSelect, medPtr->whichWin, NULL, NULL);
	    return false;
	}
	if (medPtr->windowPart == inProxyIcon) {
	    TkMacOSXTrackingLoop(1);
	    err = ChkErr(TrackWindowProxyDrag, medPtr->whichWin, where);
	    TkMacOSXTrackingLoop(0);
	    if (err == errUserWantsToDragWindow) {
		medPtr->windowPart = inDrag;
	    } else {
		return false;
	    }
	}
    }
    isFrontProcess = Tk_MacOSXIsAppInFront();
    if (isFrontProcess) {
	medPtr->state = ButtonModifiers2State(GetCurrentEventButtonState(),
		GetCurrentEventKeyModifiers());
    } else {
	medPtr->state = ButtonModifiers2State(GetCurrentButtonState(),
		GetCurrentKeyModifiers());
    }
    medPtr->global = where;
    err = ChkErr(GetEventParameter, eventPtr->eventRef,
	    kEventParamWindowMouseLocation,
	    typeQDPoint, NULL,
	    sizeof(Point), NULL,
	    &medPtr->local);
    if (err == noErr) {
	if (medPtr->whichWin) {
	    Rect widths;
	    GetWindowStructureWidths(medPtr->whichWin, &widths);
	    medPtr->local.h -=	widths.left;
	    medPtr->local.v -=	widths.top;
	}
    } else {
	medPtr->local = where;
	if (medPtr->whichWin) {
	    QDGlobalToLocalPoint(GetWindowPort(medPtr->whichWin),
		    &medPtr->local);
	}
    }
    medPtr->activeNonFloating = ActiveNonFloatingWindow();
    dispPtr = TkGetDisplayList();
    tkwin = Tk_IdToWindow(dispPtr->display, medPtr->window);

    if (eventPtr->eKind != kEventMouseDown) {
	int res = false;

	switch (eventPtr->eKind) {
	    case kEventMouseUp:
		/*
		 * The window manager only needs to know about mouse down
		 * events and sometimes we need to "eat" the mouse up.
		 * Otherwise, we just pass the event to Tk.
		 */
		if (TkMacOSXGetEatButtonUp()) {
		    TkMacOSXSetEatButtonUp(false);
		} else {
		    res = GenerateButtonEvent(medPtr);
		}
		break;
	    case kEventMouseWheelMoved:
		err = ChkErr(GetEventParameter, eventPtr->eventRef,
			kEventParamMouseWheelDelta, typeLongInteger, NULL,
			sizeof(long), NULL, &medPtr->delta);
		if (err != noErr ) {
		    statusPtr->err = 1;
		} else {
		    EventMouseWheelAxis axis;
		    err = ChkErr(GetEventParameter, eventPtr->eventRef,
			    kEventParamMouseWheelAxis, typeMouseWheelAxis,
			    NULL, sizeof(EventMouseWheelAxis), NULL, &axis);
		    if (err == noErr && axis == kEventMouseWheelAxisX) {
			 medPtr->state |= ShiftMask;
		    }
		    res = GenerateMouseWheelEvent(medPtr);
		}
		break;
	    case kEventMouseMoved:
	    case kEventMouseDragged:
		res = GeneratePollingEvents(medPtr);
		break;
	    default:
		Tcl_Panic("Unknown mouse event !");
	}
	if (res) {
		statusPtr->stopProcessing = 1;
	}
	return res;
    }
    TkMacOSXSetEatButtonUp(false);
    if (medPtr->whichWin) {
	/*
	 * We got a mouse down in a window
	 * See if this is the activate click
	 * This click moves the window forward. We don't want
	 * the corresponding mouse-up to be reported to the application
	 * or else it will mess up some Tk scripts.
	 */

	if (!(TkpIsWindowFloating(medPtr->whichWin))
		&& (medPtr->whichWin != medPtr->activeNonFloating
		|| !isFrontProcess)) {
	    int frontWindowOnly = 1;
	    int cmdDragGrow = ((medPtr->windowPart == inDrag ||
		    medPtr->windowPart == inGrow) && medPtr->state & Mod1Mask);

	    if (!cmdDragGrow) {
		Tk_Window grabWin = GetGrabWindowForWindow(tkwin);

		frontWindowOnly = !grabWin;
		if (grabWin && grabWin != tkwin) {
		    TkMacOSXSetEatButtonUp(true);
		    BringWindowForward(TkMacOSXDrawableWindow(
			    ((TkWindow*)grabWin)->window), isFrontProcess,
			    frontWindowOnly);
		    return false;
		}
	    }

	    /*
	     * Clicks in the titlebar widgets are handled without bringing the
	     * window forward.
	     */
	    if ((result = HandleWindowTitlebarMouseDown(medPtr, tkwin)) != -1) {
		statusPtr->stopProcessing = 1;
		return result;
	    } else {
		/*
		 * Only windows with the kWindowNoActivatesAttribute can
		 * receive mouse events in the background.
		 */
		if (!(((TkWindow *)tkwin)->wmInfoPtr->attributes &
			kWindowNoActivatesAttribute)) {
		    /*
		     * Allow background window dragging & growing with Command
		     * down.
		     */
		    if (!cmdDragGrow) {
			TkMacOSXSetEatButtonUp(true);
			BringWindowForward(medPtr->whichWin, isFrontProcess,
				frontWindowOnly);
		    }
		    /*
		     * Allow dragging & growing of windows that were/are in the
		     * background.
		     */
		    if (!(medPtr->windowPart == inDrag ||
			    medPtr->windowPart == inGrow)) {
			return false;
		    }
		}
	    }
	} else {
	    if ((result = HandleWindowTitlebarMouseDown(medPtr, tkwin)) != -1) {
		statusPtr->stopProcessing = 1;
		return result;
	    }
	}
	switch (medPtr->windowPart) {
	    case inDrag: {
		WindowAttributes attributes;

		GetWindowAttributes(medPtr->whichWin, &attributes);
		if (!(attributes & kWindowAsyncDragAttribute)) {
		    TkMacOSXTrackingLoop(1);
		    DragWindow(medPtr->whichWin, where, NULL);
		    TkMacOSXTrackingLoop(0);
		    where2.h = where2.v = 0;
		    QDLocalToGlobalPoint(GetWindowPort(medPtr->whichWin),
			    &where2);
		    if (EqualPt(where, where2)) {
			return false;
		    }
		    return true;
		}
		break;
	    }
	    case inGrow:
		/*
		 * Generally the content region is the domain of Tk
		 * sub-windows. However, one exception is the grow
		 * region. A button down in this area will be handled
		 * by the window manager. Note: this means that Tk
		 * may not get button down events in this area!
		 */
		if (TkMacOSXGrowToplevel(medPtr->whichWin, where) == true) {
		    statusPtr->stopProcessing = 1;
		    return true;
		} else {
		    return GenerateButtonEvent(medPtr);
		}
		break;
	    case inContent:
		return GenerateButtonEvent(medPtr);
		break;
	    default:
		return false;
		break;
	}
    }
    return false;
}

/*
 *----------------------------------------------------------------------
 *
 * HandleWindowTitlebarMouseDown --
 *
 *	Handle clicks in window titlebar.
 *
 * Results:
 *	1 if event was handled, 0 if event was not handled,
 *	-1 if MouseDown was not in window titlebar.
 *
 * Side effects:
 *	Additional events may be place on the Tk event queue.
 *
 *----------------------------------------------------------------------
 */

int
HandleWindowTitlebarMouseDown(MouseEventData * medPtr, Tk_Window tkwin)
{
    int result = INT_MAX;

    switch (medPtr->windowPart) {
	case inGoAway:
	case inCollapseBox:
	case inZoomIn:
	case inZoomOut:
	case inToolbarButton:
	    if (!IsWindowActive(medPtr->whichWin)) {
		WindowRef frontWindow = FrontNonFloatingWindow();
		WindowModality frontWindowModality = kWindowModalityNone;

		if (frontWindow && frontWindow != medPtr->whichWin) {
		    ChkErr(GetWindowModality, frontWindow,
			    &frontWindowModality, NULL);
		}
		if (frontWindowModality == kWindowModalityAppModal) {
		    result  = 0;
		}
	    }
	    break;
	default:
	    result = -1;
	    break;
    }
    
    if (result == INT_MAX) {
	result = 0;
	TkMacOSXTrackingLoop(1);
	switch (medPtr->windowPart) {
	    case inGoAway:
		if (TrackGoAway(medPtr->whichWin, medPtr->global) && tkwin) {
		    TkGenWMDestroyEvent(tkwin);
		    result = 1;
		}
		break;
	    case inCollapseBox:
		if (TrackBox(medPtr->whichWin, medPtr->global,
			medPtr->windowPart) && tkwin) {
		    TkpWmSetState((TkWindow *)tkwin, IconicState);
		    result = 1;
		}
		break;
	    case inZoomIn:
	    case inZoomOut:
		if (TrackBox(medPtr->whichWin, medPtr->global,
			medPtr->windowPart)) {
		    result = TkMacOSXZoomToplevel(medPtr->whichWin,
			    medPtr->windowPart);
		}
		break;
	    case inToolbarButton:
		if (TrackBox(medPtr->whichWin, medPtr->global,
			medPtr->windowPart)) {
		    result = GenerateToolbarButtonEvent(medPtr);
		}
		break;
	}
	TkMacOSXTrackingLoop(0);
    }

    return result;
}

/*
 *----------------------------------------------------------------------
 *
 * GeneratePollingEvents --
 *
 *	This function polls the mouse position and generates X Motion,
 *	Enter & Leave events. The cursor is also updated at this
 *	time.
 *
 * Results:
 *	True if event(s) are generated - false otherwise.
 *
 * Side effects:
 *	Additional events may be place on the Tk event queue.
 *	The cursor may be changed.
 *
 *----------------------------------------------------------------------
 */

static int
GeneratePollingEvents(MouseEventData * medPtr)
{
    Tk_Window tkwin, rootwin, grabWin;
    int local_x, local_y;
    TkDisplay *dispPtr;


    grabWin = TkMacOSXGetCapture();

    if ((!TkpIsWindowFloating(medPtr->whichWin)
	    && (medPtr->activeNonFloating != medPtr->whichWin))) {
	/*
	 * If the window for this event is not floating, and is not the
	 * active non-floating window, don't generate polling events.
	 * We don't send events to backgrounded windows. So either send
	 * it to the grabWin, or NULL if there is no grabWin.
	 */

	tkwin = grabWin;
    } else {
	/*
	 * First check whether the toplevel containing this mouse
	 * event is the grab window. If not, then send the event
	 * to the grab window. Otherwise, set tkWin to the subwindow
	 * which most closely contains the mouse event.
	 */

	dispPtr = TkGetDisplayList();
	rootwin = Tk_IdToWindow(dispPtr->display, medPtr->window);
	if ((rootwin == NULL)
		|| ((grabWin != NULL) && (rootwin != grabWin))) {
	    tkwin = grabWin;
	} else {
	    tkwin = Tk_TopCoordsToWindow(rootwin,
		    medPtr->local.h, medPtr->local.v,
		    &local_x, &local_y);
	}
    }

    /*
     * The following call will generate the appropiate X events and
     * adjust any state that Tk must remember.
     */

    Tk_UpdatePointer(tkwin, medPtr->global.h, medPtr->global.v,
	    medPtr->state);

    return true;
}

/*
 *----------------------------------------------------------------------
 *
 * BringWindowForward --
 *
 *	Bring this background window to the front.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	The window is brought forward.
 *
 *----------------------------------------------------------------------
 */

static void
BringWindowForward(
    WindowRef wRef,
    int isFrontProcess,
    int frontWindowOnly)
{
    if (wRef && !TkpIsWindowFloating(wRef) && IsValidWindowPtr(wRef)) {
	WindowRef frontWindow = FrontNonFloatingWindow();
	WindowModality frontWindowModality = kWindowModalityNone;
	
	if (frontWindow && frontWindow != wRef) {
	    ChkErr(GetWindowModality, frontWindow, &frontWindowModality, NULL);
	}
	if (frontWindowModality != kWindowModalityAppModal) {
	    Window window = TkMacOSXGetXWindow(wRef);

	    if (window != None) {
		TkDisplay *dispPtr = TkGetDisplayList();
		TkWindow * winPtr = (TkWindow *)Tk_IdToWindow(dispPtr->display,
			window);

		if (winPtr && winPtr->wmInfoPtr &&
			winPtr->wmInfoPtr->master != None) {
		    TkWindow *masterWinPtr = (TkWindow *)Tk_IdToWindow(
			    dispPtr->display, winPtr->wmInfoPtr->master);

		    if (masterWinPtr && masterWinPtr->window != None &&
			    TkMacOSXHostToplevelExists(masterWinPtr)) {
			WindowRef masterMacWin =
				TkMacOSXDrawableWindow(masterWinPtr->window);

			if (masterMacWin) {
			    BringToFront(masterMacWin);
			}
		    }
		}
	    }
	    SelectWindow(wRef);
	} else {
	    frontWindowOnly = 0;
	}
    }
    if (!isFrontProcess) {
	ProcessSerialNumber ourPsn = {0, kCurrentProcess};

	ChkErr(SetFrontProcessWithOptions, &ourPsn, frontWindowOnly ?
	    kSetFrontProcessFrontWindowOnly : 0);
    }
}

/*
 *----------------------------------------------------------------------
 *
 * TkMacOSXBringWindowForward --
 *
 *	Bring this window to the front in response to a mouse click. If
 *	a grab is in effect, bring the grab window to the front instead.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	The window is brought forward.
 *
 *----------------------------------------------------------------------
 */

void
TkMacOSXBringWindowForward(
    WindowRef wRef)
{
    TkDisplay *dispPtr = TkGetDisplayList();
    Tk_Window tkwin = Tk_IdToWindow(dispPtr->display,TkMacOSXGetXWindow(wRef));
    Tk_Window grabWin = GetGrabWindowForWindow(tkwin);

    if (grabWin && grabWin != tkwin) {
	wRef = TkMacOSXDrawableWindow(((TkWindow*)grabWin)->window);
    }
    TkMacOSXSetEatButtonUp(true);
    BringWindowForward(wRef, Tk_MacOSXIsAppInFront(), !grabWin);
}

/*
 *----------------------------------------------------------------------
 *
 * GetGrabWindowForWindow --
 *
 *	Get the grab window for the given window, if any.
 *
 * Results:
 *	Grab Tk_Window or None.
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */

Tk_Window
GetGrabWindowForWindow(
    Tk_Window tkwin) 
{
    Tk_Window grabWin = TkMacOSXGetCapture();

    if (!grabWin) {
	int grabState = TkGrabState((TkWindow*)tkwin);

	if (grabState != TK_GRAB_NONE && grabState != TK_GRAB_IN_TREE) {
	    grabWin = (Tk_Window) (((TkWindow*)tkwin)->dispPtr->grabWinPtr);
	}
    }
    
    return grabWin;
}

/*
 *----------------------------------------------------------------------
 *
 * GenerateMouseWheelEvent --
 *
 *	Generates a "MouseWheel" Tk event.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	Places a mousewheel event on the event queue.
 *
 *----------------------------------------------------------------------
 */

static int
GenerateMouseWheelEvent(MouseEventData * medPtr)
{
    Tk_Window tkwin, rootwin;
    TkDisplay *dispPtr;
    TkWindow  *winPtr;
    XEvent xEvent;

    dispPtr = TkGetDisplayList();
    rootwin = Tk_IdToWindow(dispPtr->display, medPtr->window);
    if (rootwin == NULL) {
	tkwin = NULL;
    } else {
	tkwin = Tk_TopCoordsToWindow(rootwin,
		medPtr->local.h, medPtr->local.v,
		&xEvent.xbutton.x, &xEvent.xbutton.y);
    }

    /*
     * The following call will generate the appropiate X events and
     * adjust any state that Tk must remember.
     */

    if (!tkwin) {
	tkwin = TkMacOSXGetCapture();
    }
    if (!tkwin) {
	return false;
    }
    winPtr = (TkWindow *) tkwin;
    xEvent.type = MouseWheelEvent;
    xEvent.xkey.keycode = medPtr->delta;
    xEvent.xbutton.x_root = medPtr->global.h;
    xEvent.xbutton.y_root = medPtr->global.v;
    xEvent.xbutton.state = medPtr->state;
    xEvent.xany.serial = LastKnownRequestProcessed(winPtr->display);
    xEvent.xany.send_event = false;
    xEvent.xany.display = winPtr->display;
    xEvent.xany.window = Tk_WindowId(winPtr);
    Tk_QueueWindowEvent(&xEvent, TCL_QUEUE_TAIL);

    return true;
}

/*
 *----------------------------------------------------------------------
 *
 * TkMacOSXGetEatButtonUp --
 *
 * Results:
 *	Returns the flag indicating if we need to eat the
 *	next mouse up event
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */
int
TkMacOSXGetEatButtonUp(void)
{
    return gEatButtonUp;
}

/*
 *----------------------------------------------------------------------
 *
 * TkMacOSXSetEatButtonUp --
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	Sets the flag indicating if we need to eat the
 *	next mouse up event
 *
 *----------------------------------------------------------------------
 */
void
TkMacOSXSetEatButtonUp(int f)
{
    gEatButtonUp = f;
}

/*
 *----------------------------------------------------------------------
 *
 * TkMacOSXKeyModifiers --
 *
 *	Returns the current state of the modifier keys.
 *
 * Results:
 *	An OS Modifier state.
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */

EventModifiers
TkMacOSXModifierState(void)
{
    UInt32 keyModifiers;
    int isFrontProcess = (GetCurrentEvent() && Tk_MacOSXIsAppInFront());

    keyModifiers = isFrontProcess ? GetCurrentEventKeyModifiers() :
	    GetCurrentKeyModifiers();

    return (EventModifiers)(keyModifiers & USHRT_MAX);
}

/*
 *----------------------------------------------------------------------
 *
 * TkMacOSXButtonKeyState --
 *
 *	Returns the current state of the button & modifier keys.
 *
 * Results:
 *	A bitwise inclusive OR of a subset of the following:
 *	Button1Mask, ShiftMask, LockMask, ControlMask, Mod*Mask.
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */

unsigned int
TkMacOSXButtonKeyState(void)
{
    UInt32 buttonState = 0, keyModifiers;
    int isFrontProcess = (GetCurrentEvent() && Tk_MacOSXIsAppInFront());

    if (!TkMacOSXGetEatButtonUp()) {
	buttonState = isFrontProcess ? GetCurrentEventButtonState() :
		GetCurrentButtonState();
    }
    keyModifiers = isFrontProcess ? GetCurrentEventKeyModifiers() :
	    GetCurrentKeyModifiers();

    return ButtonModifiers2State(buttonState, keyModifiers);
}

/*
 *----------------------------------------------------------------------
 *
 * ButtonModifiers2State --
 *
 *	Converts Carbon mouse button state and modifier values into a Tk
 *	button/modifier state.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */

static unsigned int
ButtonModifiers2State(UInt32 buttonState, UInt32 keyModifiers)
{
    unsigned int state;

    /* Tk supports at most 5 buttons */
    state = (buttonState & ((1<<5) - 1)) << 8;

    if (keyModifiers & alphaLock) {
	state |= LockMask;
    }
    if (keyModifiers & shiftKey) {
	state |= ShiftMask;
    }
    if (keyModifiers & controlKey) {
	state |= ControlMask;
    }
    if (keyModifiers & cmdKey) {
	state |= Mod1Mask;		/* command key */
    }
    if (keyModifiers & optionKey) {
	state |= Mod2Mask;		/* option key */
    }
    if (keyModifiers & kEventKeyModifierNumLockMask) {
	state |= Mod3Mask;
    }
    if (keyModifiers & kEventKeyModifierFnMask) {
	state |= Mod4Mask;
    }

    return state;
}

/*
 *----------------------------------------------------------------------
 *
 * XQueryPointer --
 *
 *	Check the current state of the mouse. This is not a complete
 *	implementation of this function. It only computes the root
 *	coordinates and the current mask.
 *
 * Results:
 *	Sets root_x_return, root_y_return, and mask_return. Returns
 *	true on success.
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */

Bool
XQueryPointer(
    Display* display,
    Window w,
    Window* root_return,
    Window* child_return,
    int* root_x_return,
    int* root_y_return,
    int* win_x_return,
    int* win_y_return,
    unsigned int* mask_return)
{
    int getGlobal = (root_x_return && root_y_return);
    int getLocal = (win_x_return && win_y_return);

    if (getGlobal || getLocal) {
	Point where, local;
	OSStatus err = noErr;
	int gotMouseLoc = 0;
	EventRef ev = GetCurrentEvent();

	if (ev && getLocal) {
	    err = ChkErr(GetEventParameter, ev, kEventParamWindowMouseLocation,
		    typeQDPoint, NULL, sizeof(Point), NULL, &local);
	    gotMouseLoc = (err == noErr);
	}
	if (getGlobal || !gotMouseLoc) {
	    if (ev) {
		err = ChkErr(GetEventParameter, ev, kEventParamMouseLocation,
			typeQDPoint, NULL, sizeof(Point), NULL, &where);
	    }
	    if (!ev || err != noErr) {
		GetGlobalMouse(&where);
	    }
	}
	if (getLocal) {
	    WindowRef whichWin;
	    if (ev) {
		err = ChkErr(GetEventParameter, ev, kEventParamWindowRef,
			typeWindowRef, NULL, sizeof(WindowRef), NULL,
			&whichWin);
	    }
	    if (!ev || err != noErr) {
		FindWindow(where, &whichWin);
	    }
	    if (gotMouseLoc) {
		if (whichWin) {
		    Rect widths;

		    ChkErr(GetWindowStructureWidths, whichWin, &widths);
		    local.h -= widths.left;
		    local.v -= widths.top;
		}
	    } else {
		local = where;
		if (whichWin) {
		    QDGlobalToLocalPoint(GetWindowPort(whichWin), &local);
		}
	    }
	}
	if (getGlobal) {
	    *root_x_return = where.h;
	    *root_y_return = where.v;
	}
	if (getLocal) {
	    *win_x_return = local.h;
	    *win_y_return = local.v;
	}
    }
    if (mask_return) {
	*mask_return = TkMacOSXButtonKeyState();
    }
    return True;
}

/*
 *----------------------------------------------------------------------
 *
 * TkGenerateButtonEventForXPointer --
 *
 *	This procedure generates an X button event for the current
 *	pointer state as reported by XQueryPointer().
 *
 * Results:
 *	True if event(s) are generated - false otherwise.
 *
 * Side effects:
 *	Additional events may be place on the Tk event queue.
 *	Grab state may also change.
 *
 *----------------------------------------------------------------------
 */

MODULE_SCOPE int
TkGenerateButtonEventForXPointer(
    Window window)	  /* X Window containing button event. */
{
    MouseEventData med;
    int global_x, global_y, local_x, local_y;

    bzero(&med, sizeof(MouseEventData));
    XQueryPointer(NULL, None, NULL, NULL, &global_x, &global_y,
	    &local_x, &local_y, &med.state);
    med.global.h = global_x;
    med.global.v = global_y;
    med.local.h = local_x;
    med.local.v = local_y;
    med.window = window;
    med.activeNonFloating = ActiveNonFloatingWindow();

    return GenerateButtonEvent(&med);
}

/*
 *----------------------------------------------------------------------
 *
 * TkGenerateButtonEvent --
 *
 *	Given a global x & y position and the button key status this
 *	procedure generates the appropiate X button event. It also
 *	handles the state changes needed to implement implicit grabs.
 *
 * Results:
 *	True if event(s) are generated - false otherwise.
 *
 * Side effects:
 *	Additional events may be place on the Tk event queue.
 *	Grab state may also change.
 *
 *----------------------------------------------------------------------
 */

int
TkGenerateButtonEvent(
    int x,		  /* X location of mouse */
    int y,		  /* Y location of mouse */
    Window window,	  /* X Window containing button event. */
    unsigned int state)	  /* Button Key state suitable for X event */
{
    MouseEventData med;

    bzero(&med, sizeof(MouseEventData));
    med.state = state;
    med.window = window;
    med.global.h = x;
    med.global.v = y;
    FindWindow(med.global, &med.whichWin);
    med.activeNonFloating = ActiveNonFloatingWindow();
    med.local = med.global;
    QDGlobalToLocalPoint(GetWindowPort(med.whichWin), &med.local);

    return GenerateButtonEvent(&med);
}

/*
 *----------------------------------------------------------------------
 *
 * GenerateButtonEvent --
 *
 *	Generate an X button event from a MouseEventData structure.
 *	Handles the state changes needed to implement implicit grabs.
 *
 * Results:
 *	True if event(s) are generated - false otherwise.
 *
 * Side effects:
 *	Additional events may be place on the Tk event queue.
 *	Grab state may also change.
 *
 *----------------------------------------------------------------------
 */

static int
GenerateButtonEvent(MouseEventData * medPtr)
{
    Tk_Window tkwin;
    int dummy;
    TkDisplay *dispPtr;

#if UNUSED
    /*
     * ButtonDown events will always occur in the front
     * window. ButtonUp events, however, may occur anywhere
     * on the screen. ButtonUp events should only be sent
     * to Tk if in the front window or during an implicit grab.
     */
    if ((medPtr->activeNonFloating == NULL)
	    || ((!(TkpIsWindowFloating(medPtr->whichWin))
	    && (medPtr->activeNonFloating != medPtr->whichWin))
	    && TkMacOSXGetCapture() == NULL)) {
	return false;
    }
#endif

    dispPtr = TkGetDisplayList();
    tkwin = Tk_IdToWindow(dispPtr->display, medPtr->window);

    if (tkwin != NULL) {
	tkwin = Tk_TopCoordsToWindow(tkwin, medPtr->local.h, medPtr->local.v,
		&dummy, &dummy);
    }

    Tk_UpdatePointer(tkwin, medPtr->global.h, medPtr->global.v, medPtr->state);

    return true;
}

/*
 *----------------------------------------------------------------------
 *
 * GenerateToolbarButtonEvent --
 *
 *	Generates a "ToolbarButton" virtual event.
 *	This can be used to manage disappearing toolbars.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	Places a virtual event on the event queue.
 *
 *----------------------------------------------------------------------
 */

static int
GenerateToolbarButtonEvent(MouseEventData * medPtr)
{
    Tk_Window rootwin, tkwin = NULL;
    TkDisplay *dispPtr;
    TkWindow  *winPtr;
    XVirtualEvent event;

    dispPtr = TkGetDisplayList();
    rootwin = Tk_IdToWindow(dispPtr->display, medPtr->window);
    if (rootwin) {
	tkwin = Tk_TopCoordsToWindow(rootwin,
		medPtr->local.h, medPtr->local.v, &event.x, &event.y);
    }
    if (!tkwin) {
	return true;
    }
    winPtr = (TkWindow *)tkwin;

    bzero(&event, sizeof(XVirtualEvent));
    event.type = VirtualEvent;
    event.serial = LastKnownRequestProcessed(winPtr->display);
    event.send_event = false;
    event.display = winPtr->display;
    event.event = winPtr->window;
    event.root = XRootWindow(winPtr->display, 0);
    event.subwindow = None;
    event.time = TkpGetMS();
    event.x_root = medPtr->global.h;
    event.y_root = medPtr->global.v;
    event.state = medPtr->state;
    event.same_screen = true;
    event.name = Tk_GetUid("ToolbarButton");

    Tk_QueueWindowEvent((XEvent *) &event, TCL_QUEUE_TAIL);
    return true;
}
