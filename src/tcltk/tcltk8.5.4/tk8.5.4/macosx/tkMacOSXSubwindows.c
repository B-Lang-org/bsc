/*
 * tkMacOSXSubwindows.c --
 *
 *	Implements subwindows for the macintosh version of Tk.
 *
 * Copyright (c) 1995-1997 Sun Microsystems, Inc.
 * Copyright 2001, Apple Computer, Inc.
 * Copyright (c) 2006-2008 Daniel A. Steffen <das@users.sourceforge.net>
 *
 * See the file "license.terms" for information on usage and redistribution
 * of this file, and for a DISCLAIMER OF ALL WARRANTIES.
 *
 * RCS: @(#) $Id: tkMacOSXSubwindows.c,v 1.27.2.1 2008/06/19 00:14:21 das Exp $
 */

#include "tkMacOSXPrivate.h"
#include "tkMacOSXDebug.h"
#include "tkMacOSXWm.h"

/*
#ifdef TK_MAC_DEBUG
#define TK_MAC_DEBUG_CLIP_REGIONS
#endif
*/

/*
 * Prototypes for functions used only in this file.
 */

static void MoveResizeWindow(MacDrawable *macWin);
static void GenerateConfigureNotify(TkWindow *winPtr, int includeWin);
static void UpdateOffsets(TkWindow *winPtr, int deltaX, int deltaY);
static void NotifyVisibility(TkWindow *winPtr, XEvent *eventPtr);


/*
 *----------------------------------------------------------------------
 *
 * XDestroyWindow --
 *
 *	Dealocates the given X Window.
 *
 * Results:
 *	The window id is returned.
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */

void
XDestroyWindow(
    Display* display,		/* Display. */
    Window window)		/* Window. */
{
    MacDrawable *macWin = (MacDrawable *) window;

    /*
     * Remove any dangling pointers that may exist if
     * the window we are deleting is being tracked by
     * the grab code.
     */

    TkPointerDeadWindow(macWin->winPtr);
    macWin->toplevel->referenceCount--;

    if (Tk_IsTopLevel(macWin->winPtr)) {
	WindowRef winRef;
	/*
	 * We are relying on the Activate Mac OS event to pass the
	 * focus away from a window that is getting Destroyed to the
	 * Front non-floating window. BUT we don't get activate events
	 * when a floating window is destroyed - since the front non-floating
	 * window doesn't in fact get activated... So maybe we can check here
	 * and if we are destroying a floating window, we can pass the focus
	 * back to the front non-floating window...
	 */

	if (macWin->grafPtr != NULL) {
	    TkWindow *focusPtr = TkGetFocusWin(macWin->winPtr);
	    if (focusPtr == NULL || (focusPtr->mainPtr->winPtr == macWin->winPtr)) {
		winRef = TkMacOSXDrawableWindow(window);
		if (TkpIsWindowFloating (winRef)) {
		    Window window;

		    window = TkMacOSXGetXWindow(ActiveNonFloatingWindow());
		    if (window != None) {
			TkMacOSXGenerateFocusEvent(window, 1);
		    }
		}
	    }
	}
	if (macWin->visRgn) {
	    CFRelease(macWin->visRgn);
	}
	if (macWin->aboveVisRgn) {
	    CFRelease(macWin->aboveVisRgn);
	}

	/*
	 * Delete the Mac window and remove it from the windowTable.
	 * The window could be NULL if the window was never mapped.
	 * However, we don't do this for embedded windows, they don't
	 * go in the window list, and they do not own their portPtr's.
	 */

	if (!(Tk_IsEmbedded(macWin->winPtr))) {
	    WindowRef winRef = TkMacOSXDrawableWindow(window);

	    if (winRef) {
		TkMacOSXWindowList *listPtr, *prevPtr;
		WindowGroupRef group;

		if (GetWindowProperty(winRef, 'Tk  ', 'TsGp', sizeof(group),
			NULL, &group) == noErr) {
		    TkDisplay *dispPtr = TkGetDisplayList();
		    ItemCount i = CountWindowGroupContents(group,
			    kWindowGroupContentsReturnWindows);

		    while (i > 0) {
			WindowRef macWin;
			
			ChkErr(GetIndexedWindow, group, i--, 0, &macWin);
			if (macWin) {
			    WindowGroupRef newGroup = NULL;
			    Window window = TkMacOSXGetXWindow(macWin);

			    if (window != None) {
				TkWindow * winPtr = (TkWindow *)Tk_IdToWindow(
					dispPtr->display, window);

				if (winPtr && winPtr->wmInfoPtr) {
				    newGroup = GetWindowGroupOfClass(
					    winPtr->wmInfoPtr->macClass);
				}
			    }
			    if (!newGroup) {
				newGroup = GetWindowGroupOfClass(
					kDocumentWindowClass);
			    }
			    ChkErr(SetWindowGroup, macWin, newGroup);
			}

		    }
		    ChkErr(SetWindowGroupOwner, group, NULL);
		    ChkErr(ReleaseWindowGroup, group);
		}
		TkMacOSXUnregisterMacWindow(winRef);
		DisposeWindow(winRef);

		for (listPtr = tkMacOSXWindowListPtr, prevPtr = NULL;
			tkMacOSXWindowListPtr != NULL;
			prevPtr = listPtr, listPtr = listPtr->nextPtr) {
		    if (listPtr->winPtr == macWin->winPtr) {
			if (prevPtr == NULL) {
			    tkMacOSXWindowListPtr = listPtr->nextPtr;
			} else {
			    prevPtr->nextPtr = listPtr->nextPtr;
			}
			ckfree((char *) listPtr);
			break;
		    }
		}
	    }
	}

	macWin->grafPtr = NULL;

	/*
	 * Delay deletion of a toplevel data structure untill all
	 * children have been deleted.
	 */
	if (macWin->toplevel->referenceCount == 0) {
	    ckfree((char *) macWin->toplevel);
	}
    } else {
	TkMacOSXInvalidateWindow(macWin, TK_PARENT_WINDOW);
	if (macWin->winPtr->parentPtr != NULL) {
	    TkMacOSXInvalClipRgns((Tk_Window) macWin->winPtr->parentPtr);
	}
	if (macWin->visRgn) {
	    CFRelease(macWin->visRgn);
	}
	if (macWin->aboveVisRgn) {
	    CFRelease(macWin->aboveVisRgn);
	}

	if (macWin->toplevel->referenceCount == 0) {
	    ckfree((char *) macWin->toplevel);
	}
	ckfree((char *) macWin);
    }
}

/*
 *----------------------------------------------------------------------
 *
 * XMapWindow --
 *
 *	Map the given X Window to the screen. See X window documentation
 *  for more details.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	The subwindow or toplevel may appear on the screen.
 *
 *----------------------------------------------------------------------
 */

void
XMapWindow(
    Display* display,		/* Display. */
    Window window)		/* Window. */
{
    MacDrawable *macWin = (MacDrawable *) window;
    XEvent event;

    /*
     * Under certain situations it's possible for this function to be
     * called before the toplevel window it's associated with has actually
     * been mapped. In that case we need to create the real Macintosh
     * window now as this function as well as other X functions assume that
     * the portPtr is valid.
     */
    if (!TkMacOSXHostToplevelExists(macWin->toplevel->winPtr)) {
	TkMacOSXMakeRealWindowExist(macWin->toplevel->winPtr);
    }

    display->request++;
    macWin->winPtr->flags |= TK_MAPPED;
    if (Tk_IsTopLevel(macWin->winPtr)) {
	if (!Tk_IsEmbedded(macWin->winPtr)) {
	    /*
	     * XXX This should be ShowSheetWindow for kSheetWindowClass
	     * XXX windows that have a wmPtr->master parent set.
	     */
	    WindowRef wRef = TkMacOSXDrawableWindow(window);

	    if ((macWin->winPtr->wmInfoPtr->macClass == kSheetWindowClass)
		    && (macWin->winPtr->wmInfoPtr->master != None)) {
		ShowSheetWindow(wRef, TkMacOSXDrawableWindow(
			macWin->winPtr->wmInfoPtr->master));
	    } else {
		ShowWindow(wRef);
	    }
	}
	TkMacOSXInvalClipRgns((Tk_Window) macWin->winPtr);

	/*
	 * We only need to send the MapNotify event
	 * for toplevel windows.
	 */

	event.xany.serial = display->request;
	event.xany.send_event = False;
	event.xany.display = display;

	event.xmap.window = window;
	event.xmap.type = MapNotify;
	event.xmap.event = window;
	event.xmap.override_redirect = macWin->winPtr->atts.override_redirect;
	Tk_QueueWindowEvent(&event, TCL_QUEUE_TAIL);
    } else {
	/*
	 * Generate damage for that area of the window
	 */

	TkMacOSXInvalClipRgns((Tk_Window) macWin->winPtr->parentPtr);
	TkMacOSXInvalidateWindow(macWin, TK_PARENT_WINDOW);
    }

    /*
     * Generate VisibilityNotify events for window and all mapped children.
     */

    event.xany.send_event = False;
    event.xany.display = display;
    event.xvisibility.type = VisibilityNotify;
    event.xvisibility.state = VisibilityUnobscured;
    NotifyVisibility(macWin->winPtr, &event);
}

/*
 *----------------------------------------------------------------------
 *
 * NotifyVisibility --
 *
 *	Recursively called helper proc for XMapWindow().
 
 * Results:
 *	None.
 *
 * Side effects:
 *	VisibilityNotify events are queued.
 *
 *----------------------------------------------------------------------
 */

static void
NotifyVisibility(
    TkWindow *winPtr,
    XEvent *eventPtr)
{
    if (winPtr->atts.event_mask & VisibilityChangeMask) {
	eventPtr->xany.serial = LastKnownRequestProcessed(winPtr->display);
	eventPtr->xvisibility.window = winPtr->window;
	Tk_QueueWindowEvent(eventPtr, TCL_QUEUE_TAIL);
    }
    for (winPtr = winPtr->childList; winPtr != NULL;
	    winPtr = winPtr->nextPtr) {
	if (winPtr->flags & TK_MAPPED) {
	    NotifyVisibility(winPtr, eventPtr);
	}
    }
}

/*
 *----------------------------------------------------------------------
 *
 * XUnmapWindow --
 *
 *	Unmap the given X Window to the screen. See X window
 *	documentation for more details.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	The subwindow or toplevel may be removed from the screen.
 *
 *----------------------------------------------------------------------
 */

void
XUnmapWindow(
    Display* display,		/* Display. */
    Window window)		/* Window. */
{
    MacDrawable *macWin = (MacDrawable *) window;
    XEvent event;

    display->request++;
    macWin->winPtr->flags &= ~TK_MAPPED;
    if (Tk_IsTopLevel(macWin->winPtr)) {
	if (!Tk_IsEmbedded(macWin->winPtr)
		&& macWin->winPtr->wmInfoPtr->hints.initial_state != IconicState) {
	    /*
	     * XXX This should be HideSheetWindow for kSheetWindowClass
	     * XXX windows that have a wmPtr->master parent set.
	     */
	    WindowRef wref = TkMacOSXDrawableWindow(window);

	    if ((macWin->winPtr->wmInfoPtr->macClass == kSheetWindowClass)
		    && (macWin->winPtr->wmInfoPtr->master != None)) {
		HideSheetWindow(wref);
	    } else {
		HideWindow(wref);
	    }
	}
	TkMacOSXInvalClipRgns((Tk_Window) macWin->winPtr);

	/*
	 * We only need to send the UnmapNotify event
	 * for toplevel windows.
	 */
	event.xany.serial = display->request;
	event.xany.send_event = False;
	event.xany.display = display;

	event.xunmap.type = UnmapNotify;
	event.xunmap.window = window;
	event.xunmap.event = window;
	event.xunmap.from_configure = false;
	Tk_QueueWindowEvent(&event, TCL_QUEUE_TAIL);
    } else {
	/*
	 * Generate damage for that area of the window.
	 */

	TkMacOSXInvalidateWindow(macWin, TK_PARENT_WINDOW);
	TkMacOSXInvalClipRgns((Tk_Window) macWin->winPtr->parentPtr);
    }
}

/*
 *----------------------------------------------------------------------
 *
 * XResizeWindow --
 *
 *	Resize a given X window. See X windows documentation for
 *	further details.
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
XResizeWindow(
    Display* display,		/* Display. */
    Window window,		/* Window. */
    unsigned int width,
    unsigned int height)
{
    MacDrawable *macWin = (MacDrawable *) window;

    display->request++;
    if (Tk_IsTopLevel(macWin->winPtr) && !Tk_IsEmbedded(macWin->winPtr)) {
	WindowRef w = TkMacOSXDrawableWindow(window);

	if (w) {
	    Rect bounds;

	    ChkErr(GetWindowBounds, w, kWindowContentRgn, &bounds);
	    bounds.right = bounds.left + width;
	    bounds.bottom = bounds.top + height;
	    ChkErr(SetWindowBounds, w, kWindowContentRgn, &bounds);
	}
    } else {
	MoveResizeWindow(macWin);
    }
}

/*
 *----------------------------------------------------------------------
 *
 * XMoveResizeWindow --
 *
 *	Move or resize a given X window. See X windows documentation
 *	for further details.
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
XMoveResizeWindow(
    Display* display,		/* Display. */
    Window window,		/* Window. */
    int x, int y,
    unsigned int width,
    unsigned int height)
{
    MacDrawable * macWin = (MacDrawable *) window;

    display->request++;
    if (Tk_IsTopLevel(macWin->winPtr) && !Tk_IsEmbedded(macWin->winPtr)) {
	WindowRef w = TkMacOSXDrawableWindow(window);

	if (w) {
	    Rect bounds;

	    bounds.left = x + macWin->winPtr->wmInfoPtr->xInParent;
	    bounds.right = bounds.left + width;
	    bounds.top = y + macWin->winPtr->wmInfoPtr->yInParent;
	    bounds.bottom = bounds.top + height;
	    ChkErr(SetWindowBounds, w, kWindowContentRgn, &bounds);
	}
    } else {
	MoveResizeWindow(macWin);
    }
}

/*
 *----------------------------------------------------------------------
 *
 * XMoveWindow --
 *
 *	Move a given X window. See X windows documentation for further
 *	details.
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
XMoveWindow(
    Display* display,		/* Display. */
    Window window,		/* Window. */
    int x,
    int y)
{
    MacDrawable *macWin = (MacDrawable *) window;

    display->request++;
    if (Tk_IsTopLevel(macWin->winPtr) && !Tk_IsEmbedded(macWin->winPtr)) {
	WindowRef w = TkMacOSXDrawableWindow(window);

	if (w) {
	    ChkErr(MoveWindowStructure, w, x, y);
	}
    } else {
	MoveResizeWindow(macWin);
    }
}

/*
 *----------------------------------------------------------------------
 *
 * MoveResizeWindow --
 *
 *	Helper proc for XResizeWindow, XMoveResizeWindow and XMoveWindow.
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
MoveResizeWindow(
    MacDrawable *macWin)
{
    int deltaX = 0, deltaY = 0, parentBorderwidth = 0;
    MacDrawable *macParent = NULL;
    CGrafPtr destPort = TkMacOSXGetDrawablePort((Drawable) macWin);

    /*
     * Find the Parent window, for an embedded window it will be its container.
     */
    if (Tk_IsEmbedded(macWin->winPtr)) {
	TkWindow *contWinPtr = TkpGetOtherWindow(macWin->winPtr);

	if (contWinPtr) {
	    macParent = contWinPtr->privatePtr;
	} else {
	    /*
	     * Here we should handle out of process embedding.
	     * At this point, we are assuming that the changes.x,y is not
	     * maintained, if you need the info get it from Tk_GetRootCoords,
	     * and that the toplevel sits at 0,0 when it is drawn.
	     */
	}
    } else {
	/*
	 * TODO: update all xOff & yOffs
	 */

	macParent = macWin->winPtr->parentPtr->privatePtr;
	parentBorderwidth = macWin->winPtr->parentPtr->changes.border_width;
    }
    if (macParent) {
	deltaX = macParent->xOff + parentBorderwidth +
		macWin->winPtr->changes.x - macWin->xOff;
	deltaY = macParent->yOff + parentBorderwidth +
		macWin->winPtr->changes.y - macWin->yOff;
    }
    if (destPort) {
	TkMacOSXInvalidateWindow(macWin, TK_PARENT_WINDOW);
	if (macParent) {
	    TkMacOSXInvalClipRgns((Tk_Window) macParent->winPtr);
	}
    }
    UpdateOffsets(macWin->winPtr, deltaX, deltaY);
    if (destPort) {
	TkMacOSXInvalidateWindow(macWin, TK_PARENT_WINDOW);
    }
    GenerateConfigureNotify(macWin->winPtr, 0);
}

/*
 *----------------------------------------------------------------------
 *
 * GenerateConfigureNotify --
 *
 *	Generates ConfigureNotify events for all the child widgets
 *	of the widget passed in the winPtr parameter. If includeWin
 *	is true, also generates ConfigureNotify event for the
 *	widget itself.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	ConfigureNotify events will be posted.
 *
 *----------------------------------------------------------------------
 */

static void
GenerateConfigureNotify (TkWindow *winPtr, int includeWin)
{
    TkWindow *childPtr;

    for (childPtr = winPtr->childList; childPtr != NULL;
			       childPtr = childPtr->nextPtr) {
	if (!Tk_IsMapped(childPtr) || Tk_IsTopLevel(childPtr)) {
	    continue;
	}
	GenerateConfigureNotify(childPtr, 1);
    }
    if (includeWin) {
	TkDoConfigureNotify(winPtr);
    }
}

/*
 *----------------------------------------------------------------------
 *
 * XRaiseWindow --
 *
 *	Change the stacking order of a window.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	Changes the stacking order of the specified window.
 *
 *----------------------------------------------------------------------
 */

void
XRaiseWindow(
    Display* display,		/* Display. */
    Window window)		/* Window. */
{
    MacDrawable *macWin = (MacDrawable *) window;

    display->request++;
    if (Tk_IsTopLevel(macWin->winPtr) && !Tk_IsEmbedded(macWin->winPtr)) {
	TkWmRestackToplevel(macWin->winPtr, Above, NULL);
    } else {
	/*
	 * TODO: this should generate damage
	 */
    }
}

#if 0
/*
 *----------------------------------------------------------------------
 *
 * XLowerWindow --
 *
 *	Change the stacking order of a window.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	Changes the stacking order of the specified window.
 *
 *----------------------------------------------------------------------
 */

void
XLowerWindow(
    Display* display,		/* Display. */
    Window window)		/* Window. */
{
    MacDrawable *macWin = (MacDrawable *) window;

    display->request++;
    if (Tk_IsTopLevel(macWin->winPtr) && !Tk_IsEmbedded(macWin->winPtr)) {
	TkWmRestackToplevel(macWin->winPtr, Below, NULL);
    } else {
	/*
	 * TODO: this should generate damage
	 */
    }
}
#endif

/*
 *----------------------------------------------------------------------
 *
 * XConfigureWindow --
 *
 *	Change the size, position, stacking, or border of the specified
 *	window.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	Changes the attributes of the specified window. Note that we
 *	ignore the passed in values and use the values stored in the
 *	TkWindow data structure.
 *
 *----------------------------------------------------------------------
 */

void
XConfigureWindow(
    Display* display,		/* Display. */
    Window w,			/* Window. */
    unsigned int value_mask,
    XWindowChanges* values)
{
    MacDrawable *macWin = (MacDrawable *) w;
    TkWindow *winPtr = macWin->winPtr;

    display->request++;

    /*
     * Change the shape and/or position of the window.
     */

    if (value_mask & (CWX|CWY|CWWidth|CWHeight)) {
	XMoveResizeWindow(display, w, winPtr->changes.x, winPtr->changes.y,
		winPtr->changes.width, winPtr->changes.height);
    }

    /*
     * Change the stacking order of the window. Tk actuall keeps all
     * the information we need for stacking order. All we need to do
     * is make sure the clipping regions get updated and generate damage
     * that will ensure things get drawn correctly.
     */

    if (value_mask & CWStackMode) {
	Rect bounds;
	WindowRef wRef = TkMacOSXDrawableWindow(w);

	if (wRef) {
	    TkMacOSXInvalClipRgns((Tk_Window) winPtr->parentPtr);
	    TkMacOSXWinBounds(winPtr, &bounds);
	    InvalWindowRect(wRef, &bounds);
	}
    }

    /* TkGenWMMoveRequestEvent(macWin->winPtr,
	    macWin->winPtr->changes.x, macWin->winPtr->changes.y); */
}

/*
 *----------------------------------------------------------------------
 *
 * TkMacOSXUpdateClipRgn --
 *
 *	This function updates the cliping regions for a given window
 *	and all of its children. Once updated the TK_CLIP_INVALID flag
 *	in the subwindow data structure is unset. The TK_CLIP_INVALID
 *	flag should always be unset before any drawing is attempted.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	The clip regions for the window and its children are updated.
 *
 *----------------------------------------------------------------------
 */

void
TkMacOSXUpdateClipRgn(
    TkWindow *winPtr)
{
    MacDrawable *macWin;

    if (winPtr == NULL) {
	return;
    }
    macWin = winPtr->privatePtr;
    if (macWin && macWin->flags & TK_CLIP_INVALID) {
	TkWindow *win2Ptr;

	if (Tk_IsMapped(winPtr)) {
	    int rgnChanged = 0;
	    CGRect bounds;
	    HIMutableShapeRef rgn;

	    /*
	     * Start with a region defined by the window bounds.
	     */

	    TkMacOSXWinCGBounds(winPtr, &bounds);
	    rgn = TkMacOSXHIShapeCreateMutableWithRect(&bounds);

	    /*
	     * Clip away the area of any windows that may obscure this
	     * window.
	     * For a non-toplevel window, first, clip to the parents visible
	     * clip region.
	     * Second, clip away any siblings that are higher in the
	     * stacking order.
	     * For an embedded toplevel, just clip to the container's visible
	     * clip region. Remember, we only allow one contained window
	     * in a frame, and don't support any other widgets in the frame
	     * either. This is not currently enforced, however.
	     */

	    if (!Tk_IsTopLevel(winPtr)) {
		TkMacOSXUpdateClipRgn(winPtr->parentPtr);
		if (winPtr->parentPtr) {
		    ChkErr(HIShapeIntersect,
			    winPtr->parentPtr->privatePtr->aboveVisRgn, rgn,
			    rgn);
		}
		win2Ptr = winPtr;
		while ((win2Ptr = win2Ptr->nextPtr)) {
		    if (Tk_IsTopLevel(win2Ptr) || !Tk_IsMapped(win2Ptr)) {
			continue;
		    }
		    TkMacOSXWinCGBounds(win2Ptr, &bounds);
		    ChkErr(TkMacOSHIShapeDifferenceWithRect, rgn, &bounds);
		}
	    } else if (Tk_IsEmbedded(winPtr)) {
		win2Ptr = TkpGetOtherWindow(winPtr);
		if (win2Ptr) {
		    TkMacOSXUpdateClipRgn(win2Ptr);
		    ChkErr(HIShapeIntersect,
			    win2Ptr->privatePtr->aboveVisRgn, rgn, rgn);
		} else if (tkMacOSXEmbedHandler != NULL) {
		    HIShapeRef visRgn;

		    TkMacOSXCheckTmpQdRgnEmpty();
		    tkMacOSXEmbedHandler->getClipProc((Tk_Window) winPtr,
			    tkMacOSXtmpQdRgn);
		    visRgn = HIShapeCreateWithQDRgn(tkMacOSXtmpQdRgn);
		    SetEmptyRgn(tkMacOSXtmpQdRgn);
		    ChkErr(HIShapeIntersect, visRgn, rgn, rgn);
		}

		/*
		 * TODO: Here we should handle out of process embedding.
		 */
	    } else if (winPtr->wmInfoPtr->attributes &
		    kWindowResizableAttribute) {
		HIViewRef growBoxView;
		OSErr err = HIViewFindByID(HIViewGetRoot(
			TkMacOSXDrawableWindow(winPtr->window)),
			kHIViewWindowGrowBoxID, &growBoxView);

		if (err == noErr) {
		    ChkErr(HIViewGetFrame, growBoxView, &bounds);
		    bounds = CGRectOffset(bounds,
			    -winPtr->wmInfoPtr->xInParent,
			    -winPtr->wmInfoPtr->yInParent);
		    ChkErr(TkMacOSHIShapeDifferenceWithRect, rgn, &bounds);
		}
	    }
	    macWin->aboveVisRgn = HIShapeCreateCopy(rgn);

	    /*
	     * The final clip region is the aboveVis region (or visible
	     * region) minus all the children of this window.
	     * If the window is a container, we must also subtract the region
	     * of the embedded window.
	     */

	    win2Ptr = winPtr->childList;
	    while (win2Ptr) {
		if (Tk_IsTopLevel(win2Ptr) || !Tk_IsMapped(win2Ptr)) {
		    win2Ptr = win2Ptr->nextPtr;
		    continue;
		}
		TkMacOSXWinCGBounds(win2Ptr, &bounds);
		ChkErr(TkMacOSHIShapeDifferenceWithRect, rgn, &bounds);
		rgnChanged = 1;
		win2Ptr = win2Ptr->nextPtr;
	    }

	    if (Tk_IsContainer(winPtr)) {
		win2Ptr = TkpGetOtherWindow(winPtr);
		if (win2Ptr) {
		    if (Tk_IsMapped(win2Ptr)) {
			TkMacOSXWinCGBounds(win2Ptr, &bounds);
			ChkErr(TkMacOSHIShapeDifferenceWithRect, rgn, &bounds);
			rgnChanged = 1;
		    }
		}

		/*
		 * TODO: Here we should handle out of process embedding.
		 */
	    }
	    if (rgnChanged) {
		HIShapeRef diffRgn = HIShapeCreateDifference(
			macWin->aboveVisRgn, rgn);

		if (!HIShapeIsEmpty(diffRgn)) {
		    macWin->visRgn = HIShapeCreateCopy(rgn);
		}
		CFRelease(diffRgn);
	    }
	    CFRelease(rgn);
	} else {
	    /*
	     * An unmapped window has empty clip regions to prevent any
	     * (erroneous) drawing into it or its children from becoming
	     * visible. [Bug 940117]
	     */

	    if (!Tk_IsTopLevel(winPtr)) {
		TkMacOSXUpdateClipRgn(winPtr->parentPtr);
	    } else if (Tk_IsEmbedded(winPtr)) {
		win2Ptr = TkpGetOtherWindow(winPtr);
		if (win2Ptr) {
		    TkMacOSXUpdateClipRgn(win2Ptr);
		}
	    }
	    macWin->aboveVisRgn = TkMacOSXHIShapeCreateEmpty();
	}
	if (!macWin->visRgn) {
	    macWin->visRgn = HIShapeCreateCopy(macWin->aboveVisRgn);
	}
	macWin->flags &= ~TK_CLIP_INVALID;

#ifdef TK_MAC_DEBUG_CLIP_REGIONS
	TkMacOSXDebugFlashRegion((Drawable) macWin, macWin->visRgn);
#endif /* TK_MAC_DEBUG_CLIP_REGIONS */
    }
}

/*
 *----------------------------------------------------------------------
 *
 * TkMacOSXVisableClipRgn --
 *
 *	This function returnd the Macintosh cliping region for the
 *	given window. A NULL Rgn means the window is not visible.
 *
 * Results:
 *	The region.
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */

RgnHandle
TkMacOSXVisableClipRgn(
    TkWindow *winPtr)
{
    static RgnHandle visQdRgn = NULL;

    if (visQdRgn == NULL) {
	visQdRgn = NewRgn();
    }
    if (winPtr->privatePtr->flags & TK_CLIP_INVALID) {
	TkMacOSXUpdateClipRgn(winPtr);
    }
    ChkErr(HIShapeGetAsQDRgn, winPtr->privatePtr->visRgn, visQdRgn);
    return visQdRgn;
}

/*
 *----------------------------------------------------------------------
 *
 * TkMacOSXInvalidateWindow --
 *
 *	This function makes the window as invalid will generate damage
 *	for the window.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	Damage is created.
 *
 *----------------------------------------------------------------------
 */

void
TkMacOSXInvalidateWindow(
    MacDrawable *macWin,	/* Make window that's causing damage. */
    int flag)			/* Should be TK_WINDOW_ONLY or
				 * TK_PARENT_WINDOW */
{
    WindowRef windowRef;
    HIShapeRef rgn;

    windowRef = TkMacOSXDrawableWindow((Drawable)macWin);
    if (macWin->flags & TK_CLIP_INVALID) {
	TkMacOSXUpdateClipRgn(macWin->winPtr);
    }
    rgn = (flag == TK_WINDOW_ONLY) ? macWin->visRgn : macWin->aboveVisRgn;
    if (!HIShapeIsEmpty(rgn)) {
	TkMacOSXCheckTmpQdRgnEmpty();
	ChkErr(HIShapeGetAsQDRgn, rgn, tkMacOSXtmpQdRgn);
	InvalWindowRgn(windowRef, tkMacOSXtmpQdRgn);
	SetEmptyRgn(tkMacOSXtmpQdRgn);
    }
#ifdef TK_MAC_DEBUG_CLIP_REGIONS
    TkMacOSXDebugFlashRegion((Drawable) macWin, rgn);
#endif /* TK_MAC_DEBUG_CLIP_REGIONS */
}

/*
 *----------------------------------------------------------------------
 *
 * TkMacOSXGetDrawableWindow --
 *
 *	This function returns the WindowRef for a given X drawable.
 *
 * Results:
 *	A WindowRef, or NULL for off screen pixmaps.
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */

WindowRef
TkMacOSXDrawableWindow(
    Drawable drawable)
{
    MacDrawable *macWin = (MacDrawable *) drawable;
    WindowRef result = NULL;

    if (!macWin || macWin->flags & TK_IS_PIXMAP) {
	result = NULL;
    } else {
	result = GetWindowFromPort(TkMacOSXGetDrawablePort(drawable));
    }
    return result;
}

/*
 *----------------------------------------------------------------------
 *
 * TkMacOSXGetDrawablePort --
 *
 *	This function returns the Graphics Port for a given X drawable.
 *
 * Results:
 *	A CGrafPort . Either an off screen pixmap or a Window.
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */

CGrafPtr
TkMacOSXGetDrawablePort(
    Drawable drawable)
{
    MacDrawable *macWin = (MacDrawable *) drawable;
    CGrafPtr resultPort = NULL;

    if (macWin) {
	if (macWin->toplevel) {
	    /*
	     * If the Drawable is in an embedded window, use the Port of its
	     * container.
	     *
	     * TRICKY POINT: we can have cases when a toplevel is being
	     * destroyed where the winPtr for the toplevel has been freed, but
	     * the children are not all the way destroyed. The children will
	     * call this function as they are being destroyed, but
	     * Tk_IsEmbedded will return garbage. So we check the copy of the
	     * TK_EMBEDDED flag we put into the toplevel's macWin flags.
	     */

	    if (macWin->toplevel->flags & TK_EMBEDDED) {
		TkWindow *contWinPtr;

		contWinPtr = TkpGetOtherWindow(macWin->toplevel->winPtr);

		if (contWinPtr != NULL) {
		    resultPort = TkMacOSXGetDrawablePort(
			(Drawable) contWinPtr->privatePtr);
		} else if (tkMacOSXEmbedHandler != NULL) {
		    resultPort = tkMacOSXEmbedHandler->getPortProc(
			    (Tk_Window) macWin->winPtr);
		}

		if (!resultPort) {
		    /*
		     * FIXME: So far as I can tell, the only time that this
		     * happens is when we are tearing down an embedded child
		     * interpreter, and most of the time, this is harmless...
		     * However, we really need to find why the embedding loses.
		     */
		    TkMacOSXDbgMsg("Couldn't find container");
		}

		/*
		 * TODO: Here we should handle out of process embedding.
		 */
	    } else {
		resultPort = macWin->toplevel->grafPtr;
	    }
	} else {
	    if ((macWin->flags & TK_IS_PIXMAP) && !macWin->grafPtr) {
		Rect bounds = {0, 0, macWin->size.height, macWin->size.width};

		ChkErr(NewGWorld, &macWin->grafPtr,
			(macWin->flags & TK_IS_BW_PIXMAP) ? 1 : 0,
			&bounds, NULL, NULL, 0
#ifdef __LITTLE_ENDIAN__
			| kNativeEndianPixMap
#endif
			);
	    }
	    resultPort = macWin->grafPtr;	
	}
    }

    return resultPort;
}

/*
 *----------------------------------------------------------------------
 *
 * TkMacOSXGetRootControl --
 *
 *	This function returns the Root Control for a given X drawable.
 *
 * Results:
 *	A ControlRef .
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */

ControlRef
TkMacOSXGetRootControl(
    Drawable drawable)
{
    /*
     * will probably need to fix this up for embedding
     */
    MacDrawable *macWin = (MacDrawable *) drawable;
    ControlRef result = NULL;

    if (macWin == NULL) {
	return NULL;
    }
    if (!(macWin->toplevel->flags & TK_EMBEDDED)) {
	return macWin->toplevel->rootControl;
    } else {
	TkWindow *contWinPtr;

	contWinPtr = TkpGetOtherWindow(macWin->toplevel->winPtr);

	if (contWinPtr != NULL) {
	    result = TkMacOSXGetRootControl(
		(Drawable) contWinPtr->privatePtr);
	} else if (tkMacOSXEmbedHandler != NULL) {
	    result = NULL;
	}
   }
    return result;
}

/*
 *----------------------------------------------------------------------
 *
 * TkMacOSXInvalClipRgns --
 *
 *	This function invalidates the clipping regions for a given
 *	window and all of its children. This function should be
 *	called whenever changes are made to subwindows that would
 *	affect the size or position of windows.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	The cliping regions for the window and its children are
 *	mark invalid. (Make sure they are valid before drawing.)
 *
 *----------------------------------------------------------------------
 */

void
TkMacOSXInvalClipRgns(
    Tk_Window tkwin)
{
    TkWindow *winPtr = (TkWindow *) tkwin;
    TkWindow *childPtr;
    MacDrawable *macWin = winPtr->privatePtr;

    /*
     * If already marked we can stop because all
     * decendants will also already be marked.
     */
    if (!macWin || macWin->flags & TK_CLIP_INVALID) {
	return;
    }

    macWin->flags |= TK_CLIP_INVALID;
    if (macWin->visRgn) {
	CFRelease(macWin->visRgn);
	macWin->visRgn = NULL;
    }
    if (macWin->aboveVisRgn) {
	CFRelease(macWin->aboveVisRgn);
	macWin->aboveVisRgn = NULL;
    }

    /*
     * Invalidate clip regions for all children &
     * their decendants - unless the child is a toplevel.
     */
    childPtr = winPtr->childList;
    while (childPtr) {
	if (!Tk_IsTopLevel(childPtr)) {
	    TkMacOSXInvalClipRgns((Tk_Window) childPtr);
	}
	childPtr = childPtr->nextPtr;
    }

    /*
     * Also, if the window is a container, mark its embedded window
     */

    if (Tk_IsContainer(winPtr)) {
	childPtr = TkpGetOtherWindow(winPtr);

	if (childPtr) {
	    TkMacOSXInvalClipRgns((Tk_Window) childPtr);
	}

	/*
	 * TODO: Here we should handle out of process embedding.
	 */
    }
}

/*
 *----------------------------------------------------------------------
 *
 * TkMacOSXWinBounds --
 *
 *	Given a Tk window this function determines the windows
 *	bounds in relation to the Macintosh window's coordinate
 *	system. This is also the same coordinate system as the
 *	Tk toplevel window in which this window is contained.
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
TkMacOSXWinBounds(
    TkWindow *winPtr,
    Rect *bounds)
{
    bounds->left = winPtr->privatePtr->xOff;
    bounds->top = winPtr->privatePtr->yOff;
    bounds->right = bounds->left + winPtr->changes.width;
    bounds->bottom = bounds->top + winPtr->changes.height;
}

/*
 *----------------------------------------------------------------------
 *
 * TkMacOSXWinCGBounds --
 *
 *	Given a Tk window this function determines the windows
 *	bounds in relation to the Macintosh window's coordinate
 *	system. This is also the same coordinate system as the
 *	Tk toplevel window in which this window is contained.
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
TkMacOSXWinCGBounds(
    TkWindow *winPtr,
    CGRect *bounds)
{
    bounds->origin.x = winPtr->privatePtr->xOff;
    bounds->origin.y = winPtr->privatePtr->yOff;
    bounds->size.width = winPtr->changes.width;
    bounds->size.height = winPtr->changes.height;
}

/*
 *----------------------------------------------------------------------
 *
 * UpdateOffsets --
 *
 *	Updates the X & Y offsets of the given TkWindow from the
 *	TopLevel it is a decendant of.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	The xOff & yOff fields for the Mac window datastructure
 *	is updated to the proper offset.
 *
 *----------------------------------------------------------------------
 */

static void
UpdateOffsets(
    TkWindow *winPtr,
    int deltaX,
    int deltaY)
{
    TkWindow *childPtr;

    if (winPtr->privatePtr == NULL) {
	/*
	 * We haven't called Tk_MakeWindowExist for this window yet. The
	 * offset information will be postponed and calulated at that
	 * time. (This will usually only happen when a mapped parent is
	 * being moved but has child windows that have yet to be mapped.)
	 */
	return;
    }

    winPtr->privatePtr->xOff += deltaX;
    winPtr->privatePtr->yOff += deltaY;

    childPtr = winPtr->childList;
    while (childPtr != NULL) {
	if (!Tk_IsTopLevel(childPtr)) {
	    UpdateOffsets(childPtr, deltaX, deltaY);
	}
	childPtr = childPtr->nextPtr;
    }

    if (Tk_IsContainer(winPtr)) {
	childPtr = TkpGetOtherWindow(winPtr);
	if (childPtr != NULL) {
	    UpdateOffsets(childPtr,deltaX,deltaY);
	}

	/*
	 * TODO: Here we should handle out of process embedding.
	 */
    }
}

/*
 *----------------------------------------------------------------------
 *
 * Tk_GetPixmap --
 *
 *	Creates an in memory drawing surface.
 *
 * Results:
 *	Returns a handle to a new pixmap.
 *
 * Side effects:
 *	Allocates a new Macintosh GWorld.
 *
 *----------------------------------------------------------------------
 */

Pixmap
Tk_GetPixmap(
    Display *display,	/* Display for new pixmap (can be null). */
    Drawable d,		/* Drawable where pixmap will be used (ignored). */
    int width,		/* Dimensions of pixmap. */
    int height,
    int depth)		/* Bits per pixel for pixmap. */
{
    MacDrawable *macPix;

    if (display != NULL) {
	display->request++;
    }
    macPix = (MacDrawable *) ckalloc(sizeof(MacDrawable));
    macPix->winPtr = NULL;
    macPix->xOff = 0;
    macPix->yOff = 0;
    macPix->visRgn = NULL;
    macPix->aboveVisRgn = NULL;
    macPix->drawRect = CGRectNull;
    macPix->referenceCount = 0;
    macPix->toplevel = NULL;
    macPix->flags = TK_IS_PIXMAP | (depth == 1 ? TK_IS_BW_PIXMAP : 0);
    macPix->grafPtr = NULL;
    macPix->context = NULL;
    macPix->size = CGSizeMake(width, height);
    {
	Rect bounds = {0, 0, height, width};

	ChkErr(NewGWorld, &macPix->grafPtr, depth == 1 ? 1 : 0, &bounds, NULL,
		NULL, 0
#ifdef __LITTLE_ENDIAN__
		| kNativeEndianPixMap
#endif
		);
    }

    return (Pixmap) macPix;
}

/*
 *----------------------------------------------------------------------
 *
 * Tk_FreePixmap --
 *
 *	Release the resources associated with a pixmap.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	Deletes the Macintosh GWorld created by Tk_GetPixmap.
 *
 *----------------------------------------------------------------------
 */

void
Tk_FreePixmap(
    Display *display,		/* Display. */
    Pixmap pixmap)		/* Pixmap to destroy */
{
    MacDrawable *macPix = (MacDrawable *) pixmap;

    display->request++;
    if (macPix->grafPtr) {
	DisposeGWorld(macPix->grafPtr);
    }
    if (macPix->context) {
	TkMacOSXDbgMsg("Cannot free CG backed Pixmap");
    }
    ckfree((char *) macPix);
}

/*
 * Local Variables:
 * mode: c
 * c-basic-offset: 4
 * fill-column: 79
 * coding: utf-8
 * End:
 */
