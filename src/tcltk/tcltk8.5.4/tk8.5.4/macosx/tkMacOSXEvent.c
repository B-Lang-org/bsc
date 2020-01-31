/*
 * tkMacOSXEvent.c --
 *
 *	This file contains the basic Mac OS X Event handling routines.
 *
 * Copyright (c) 1995-1997 Sun Microsystems, Inc.
 * Copyright 2001, Apple Computer, Inc.
 * Copyright (c) 2005-2007 Daniel A. Steffen <das@users.sourceforge.net>
 *
 * See the file "license.terms" for information on usage and redistribution
 * of this file, and for a DISCLAIMER OF ALL WARRANTIES.
 *
 * RCS: @(#) $Id: tkMacOSXEvent.c,v 1.23 2007/12/13 15:27:09 dgp Exp $
 */

#include "tkMacOSXPrivate.h"
#include "tkMacOSXEvent.h"
#include "tkMacOSXDebug.h"


/*
 *----------------------------------------------------------------------
 *
 * TkMacOSXFlushWindows --
 *
 *	This routine flushes all the Carbon windows of the application. It
 *	is called by XSync().
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	Flushes all Carbon windows
 *
 *----------------------------------------------------------------------
 */

MODULE_SCOPE void
TkMacOSXFlushWindows(void)
{
    WindowRef wRef = GetWindowList();

    while (wRef) {
	TK_IF_MAC_OS_X_API (3, HIWindowFlush,
	    ChkErr(HIWindowFlush, wRef);
	) TK_ELSE_MAC_OS_X (3,
	    CGrafPtr portPtr = GetWindowPort(wRef);

	    if (QDIsPortBuffered(portPtr)) {
		QDFlushPortBuffer(portPtr, NULL);
	    }
	) TK_ENDIF
	wRef = GetNextWindow(wRef);
    }
}

/*
 *----------------------------------------------------------------------
 *
 * TkMacOSXProcessEvent --
 *
 *	This dispatches a filtered Carbon event to the appropriate handler
 *
 *	Note on MacEventStatus.stopProcessing: Please be conservative in the
 *	individual handlers and don't assume the event is fully handled
 *	unless you *really* need to ensure that other handlers don't see the
 *	event anymore. Some OS manager or library might be interested in
 *	events even after they are already handled on the Tk level.
 *
 * Results:
 *	0 on success
 *	-1 on failure
 *
 * Side effects:
 *	Converts a Carbon event to a Tk event
 *
 *----------------------------------------------------------------------
 */

MODULE_SCOPE int
TkMacOSXProcessEvent(
    TkMacOSXEvent *eventPtr,
    MacEventStatus *statusPtr)
{
    switch (eventPtr->eClass) {
	case kEventClassMouse:
	    TkMacOSXProcessMouseEvent(eventPtr, statusPtr);
	    break;
	case kEventClassWindow:
	    TkMacOSXProcessWindowEvent(eventPtr, statusPtr);
	    break;
	case kEventClassKeyboard:
	    TkMacOSXProcessKeyboardEvent(eventPtr, statusPtr);
	    break;
	case kEventClassApplication:
	    TkMacOSXProcessApplicationEvent(eventPtr, statusPtr);
	    break;
	case kEventClassAppearance:
	    TkMacOSXProcessAppearanceEvent(eventPtr, statusPtr);
	    break;
	case kEventClassMenu:
	    TkMacOSXProcessMenuEvent(eventPtr, statusPtr);
	    break;
	case kEventClassCommand:
	    TkMacOSXProcessCommandEvent(eventPtr, statusPtr);
	    break;
	default: {
	    TkMacOSXDbgMsg("Unrecognised event: %s",
		    TkMacOSXCarbonEventToAscii(eventPtr->eventRef));
	    break;
	}
    }
    return 0;
}

/*
 *----------------------------------------------------------------------
 *
 * TkMacOSXProcessMenuEvent --
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
TkMacOSXProcessMenuEvent(
    TkMacOSXEvent *eventPtr,
    MacEventStatus *statusPtr)
{
    int menuContext;
    OSStatus err;

    switch (eventPtr->eKind) {
	case kEventMenuBeginTracking:
	case kEventMenuEndTracking:
	case kEventMenuOpening:
	case kEventMenuTargetItem:
	    break;
	default:
	    return 0;
	    break;
    }
    err = ChkErr(GetEventParameter, eventPtr->eventRef, kEventParamMenuContext,
	    typeUInt32, NULL, sizeof(menuContext), NULL, &menuContext);
    if (err == noErr && ((menuContext & kMenuContextMenuBarTracking) ||
	    (menuContext & kMenuContextPopUpTracking))) {
	switch (eventPtr->eKind) {
	    MenuRef menu;

	    case kEventMenuBeginTracking:
		TkMacOSXClearMenubarActive();

		/*
		 * Handle -postcommand
		 */

		TkMacOSXPreprocessMenu();
		TkMacOSXTrackingLoop(1);
		break;
	    case kEventMenuEndTracking:
		TkMacOSXTrackingLoop(0);
		break;
	    case kEventMenuOpening:
		err = ChkErr(GetEventParameter, eventPtr->eventRef,
			kEventParamDirectObject, typeMenuRef, NULL,
			sizeof(menu), NULL, &menu);
		if (err == noErr) {
		    TkMacOSXClearActiveMenu(menu);
		    return TkMacOSXGenerateParentMenuSelectEvent(menu);
		}
		break;
	    case kEventMenuTargetItem:
		err = ChkErr(GetEventParameter, eventPtr->eventRef,
			kEventParamDirectObject, typeMenuRef, NULL,
			sizeof(menu), NULL, &menu);
		if (err == noErr) {
		    MenuItemIndex index;

		    err = ChkErr(GetEventParameter, eventPtr->eventRef,
			    kEventParamMenuItemIndex, typeMenuItemIndex, NULL,
			    sizeof(index), NULL, &index);
		    if (err == noErr) {
			return TkMacOSXGenerateMenuSelectEvent(menu, index);
		    }
		}
		break;
	}
    }
    return 0;
}

/*
 *----------------------------------------------------------------------
 *
 * TkMacOSXProcessCommandEvent --
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
TkMacOSXProcessCommandEvent(
    TkMacOSXEvent *eventPtr,
    MacEventStatus * statusPtr)
{
    HICommand command;
    int menuContext;
    OSStatus err;

    switch (eventPtr->eKind) {
	case kEventCommandProcess:
	case kEventCommandUpdateStatus:
	    break;
	default:
	    return 0;
	    break;
    }
    err = ChkErr(GetEventParameter, eventPtr->eventRef,
	    kEventParamDirectObject, typeHICommand, NULL, sizeof(command),
	    NULL, &command);
    if (err == noErr && (command.attributes & kHICommandFromMenu)) {
	if (eventPtr->eKind == kEventCommandProcess) {
	    err = ChkErr(GetEventParameter, eventPtr->eventRef,
		    kEventParamMenuContext, typeUInt32, NULL,
		    sizeof(menuContext), NULL, &menuContext);
	    if (err == noErr && (menuContext & kMenuContextMenuBar) &&
		    (menuContext & kMenuContextMenuBarTracking)) {
		TkMacOSXHandleMenuSelect(GetMenuID(command.menu.menuRef),
			command.menu.menuItemIndex,
			(GetCurrentEventKeyModifiers() & optionKey) != 0);
		return 1;
	    }
	} else {
	    Tcl_CmdInfo dummy;
	    if (command.commandID == kHICommandPreferences && eventPtr->interp) {
		if (Tcl_GetCommandInfo(eventPtr->interp,
			"::tk::mac::ShowPreferences", &dummy)) {
		    if (!IsMenuItemEnabled(command.menu.menuRef,
			    command.menu.menuItemIndex)) {
			EnableMenuItem(command.menu.menuRef,
				command.menu.menuItemIndex);
		    }
		} else {
		    if (IsMenuItemEnabled(command.menu.menuRef,
			    command.menu.menuItemIndex)) {
			DisableMenuItem(command.menu.menuRef,
				command.menu.menuItemIndex);
		    }
		}
		statusPtr->stopProcessing = 1;
		return 1;
	    }
	}
    }
    return 0;
}
