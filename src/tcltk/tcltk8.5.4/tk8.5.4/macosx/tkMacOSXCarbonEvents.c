/*
 * tkMacOSXCarbonEvents.c --
 *
 *	This file implements functions that register for and handle
 *	various Carbon Events and Timers. Most carbon events of interest
 *	to TkAqua are processed in a handler registered on the dispatcher
 *	event target so that we get first crack at them before HIToolbox
 *	dispatchers/processes them further.
 *	As some events are sent directly to the focus or app event target
 *	and not dispatched normally, we also register a handler on the
 *	application event target.
 *
 * Copyright 2001, Apple Computer, Inc.
 * Copyright (c) 2005-2008 Daniel A. Steffen <das@users.sourceforge.net>
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
 * RCS: @(#) $Id: tkMacOSXCarbonEvents.c,v 1.19.2.1 2008/06/19 00:16:17 das Exp $
 */

#include "tkMacOSXPrivate.h"
#include "tkMacOSXEvent.h"
#include "tkMacOSXDebug.h"

/*
#ifdef TK_MAC_DEBUG
#define TK_MAC_DEBUG_CARBON_EVENTS
#endif
*/

/*
 * Declarations of functions used only in this file:
 */

static OSStatus CarbonEventHandlerProc(EventHandlerCallRef callRef,
	EventRef event, void *userData);
static OSStatus InstallStandardApplicationEventHandler(void);
static void CarbonTimerProc(EventLoopTimerRef timer, void *userData);

/*
 * Static data used by several functions in this file:
 */

static EventLoopTimerRef carbonTimer = NULL;
static int carbonTimerEnabled = 0;
static EventHandlerUPP carbonEventHandlerUPP = NULL;
static Tcl_Interp *carbonEventInterp = NULL;
static int inTrackingLoop = 0;

#if MAC_OS_X_VERSION_MIN_REQUIRED < 1050
/*
 * For InstallStandardApplicationEventHandler():
 */

static jmp_buf exitRaelJmpBuf;
static void ExitRaelEventHandlerProc(EventHandlerCallRef callRef,
	EventRef event, void *userData) __attribute__ ((__noreturn__));
#endif


/*
 *----------------------------------------------------------------------
 *
 * CarbonEventHandlerProc --
 *
 *	This procedure is the handler for all registered CarbonEvents.
 *
 * Results:
 *	OS status code.
 *
 * Side effects:
 *	Dispatches CarbonEvents.
 *
 *----------------------------------------------------------------------
 */

static OSStatus
CarbonEventHandlerProc(
    EventHandlerCallRef callRef,
    EventRef event,
    void *userData)
{
    OSStatus err = eventNotHandledErr;
    TkMacOSXEvent macEvent;
    MacEventStatus eventStatus;

    macEvent.eventRef = event;
    macEvent.eClass = GetEventClass(event);
    macEvent.eKind = GetEventKind(event);
    macEvent.interp = (Tcl_Interp *) userData;
    macEvent.callRef = callRef;
    bzero(&eventStatus, sizeof(eventStatus));

#ifdef TK_MAC_DEBUG_CARBON_EVENTS
    if (!(macEvent.eClass == kEventClassMouse && (
	    macEvent.eKind == kEventMouseMoved ||
	    macEvent.eKind == kEventMouseDragged))) {
	TkMacOSXDbgMsg("Started handling %s",
		TkMacOSXCarbonEventToAscii(event));
	TkMacOSXInitNamedDebugSymbol(HIToolbox, void, _DebugPrintEvent,
		EventRef inEvent);
	if (_DebugPrintEvent) {
	    /*
	     * Carbon-internal event debugging (c.f. Technote 2124)
	     */

	    _DebugPrintEvent(event);
	}
    }
#endif /* TK_MAC_DEBUG_CARBON_EVENTS */

    TkMacOSXProcessEvent(&macEvent,&eventStatus);
    if (eventStatus.stopProcessing) {
	err = noErr;
    }

#ifdef TK_MAC_DEBUG_CARBON_EVENTS
    if (macEvent.eKind != kEventMouseMoved &&
	    macEvent.eKind != kEventMouseDragged) {
	TkMacOSXDbgMsg("Finished handling %s: %s handled",
		TkMacOSXCarbonEventToAscii(event),
		eventStatus.stopProcessing ? "   " : "not");
    }
#endif /* TK_MAC_DEBUG_CARBON_EVENTS */
    return err;
}

/*
 *----------------------------------------------------------------------
 *
 * TkMacOSXInitCarbonEvents --
 *
 *	This procedure initializes all CarbonEvent handlers.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	Handlers for Carbon Events are registered.
 *
 *----------------------------------------------------------------------
 */

MODULE_SCOPE void
TkMacOSXInitCarbonEvents(
    Tcl_Interp *interp)
{
    const EventTypeSpec dispatcherEventTypes[] = {
	{kEventClassKeyboard,	 kEventRawKeyDown},
	{kEventClassKeyboard,	 kEventRawKeyRepeat},
	{kEventClassKeyboard,	 kEventRawKeyUp},
	{kEventClassKeyboard,	 kEventRawKeyModifiersChanged},
	{kEventClassKeyboard,	 kEventRawKeyRepeat},
    };
    const EventTypeSpec applicationEventTypes[] = {
	{kEventClassMenu,	 kEventMenuBeginTracking},
	{kEventClassMenu,	 kEventMenuEndTracking},
	{kEventClassMenu,	 kEventMenuOpening},
	{kEventClassMenu,	 kEventMenuTargetItem},
	{kEventClassCommand,	 kEventCommandProcess},
	{kEventClassCommand,	 kEventCommandUpdateStatus},
	{kEventClassApplication, kEventAppActivated},
	{kEventClassApplication, kEventAppDeactivated},
	{kEventClassApplication, kEventAppQuit},
	{kEventClassApplication, kEventAppHidden},
	{kEventClassApplication, kEventAppShown},
	{kEventClassApplication, kEventAppAvailableWindowBoundsChanged},
	{kEventClassAppearance,	 kEventAppearanceScrollBarVariantChanged},
    };

    carbonEventHandlerUPP = NewEventHandlerUPP(CarbonEventHandlerProc);
    carbonEventInterp = interp;
    ChkErr(InstallStandardApplicationEventHandler);
    ChkErr(InstallEventHandler, GetEventDispatcherTarget(),
	    carbonEventHandlerUPP, GetEventTypeCount(dispatcherEventTypes),
	    dispatcherEventTypes, (void *) carbonEventInterp, NULL);
    ChkErr(InstallEventHandler, GetApplicationEventTarget(),
	    carbonEventHandlerUPP, GetEventTypeCount(applicationEventTypes),
	    applicationEventTypes, (void *) carbonEventInterp, NULL);

#ifdef TK_MAC_DEBUG_CARBON_EVENTS
    TkMacOSXInitNamedSymbol(HIToolbox, void, DebugTraceEvent, OSType, UInt32,
	    Boolean);
    if (DebugTraceEvent) {
	unsigned int i;
	const EventTypeSpec *e;

	for (i = 0, e = dispatcherEventTypes;
		i < GetEventTypeCount(dispatcherEventTypes); i++, e++) {
	    DebugTraceEvent(e->eventClass, e->eventKind, 1);
	}
	for (i = 0, e = applicationEventTypes;
		i < GetEventTypeCount(applicationEventTypes); i++, e++) {
	    DebugTraceEvent(e->eventClass, e->eventKind, 1);
	}
	DebugTraceEvent = NULL; /* Only enable tracing once. */
    }
#endif /* TK_MAC_DEBUG_CARBON_EVENTS */
}

/*
 *----------------------------------------------------------------------
 *
 * TkMacOSXInstallWindowCarbonEventHandler --
 *
 *	This procedure installs our window CarbonEvent handler.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	Handler for Carbon Events is registered.
 *
 *----------------------------------------------------------------------
 */

MODULE_SCOPE void
TkMacOSXInstallWindowCarbonEventHandler(
	Tcl_Interp *interp, WindowRef window)
{
    const EventTypeSpec windowEventTypes[] = {
	{kEventClassMouse,	 kEventMouseDown},
	{kEventClassMouse,	 kEventMouseUp},
	{kEventClassMouse,	 kEventMouseMoved},
	{kEventClassMouse,	 kEventMouseDragged},
	{kEventClassMouse,	 kEventMouseWheelMoved},
	{kEventClassWindow,	 kEventWindowActivated},
	{kEventClassWindow,	 kEventWindowDeactivated},
	{kEventClassWindow,	 kEventWindowUpdate},
	{kEventClassWindow,	 kEventWindowExpanding},
	{kEventClassWindow,	 kEventWindowBoundsChanged},
	{kEventClassWindow,	 kEventWindowDragStarted},
	{kEventClassWindow,	 kEventWindowDragCompleted},
	{kEventClassWindow,	 kEventWindowConstrain},
	{kEventClassWindow,	 kEventWindowGetRegion},
	{kEventClassWindow,	 kEventWindowDrawContent},
    };

    ChkErr(InstallEventHandler, GetWindowEventTarget(window),
	    carbonEventHandlerUPP, GetEventTypeCount(windowEventTypes),
	    windowEventTypes, (void *) (interp ? interp : carbonEventInterp),
	    NULL);

#ifdef TK_MAC_DEBUG_CARBON_EVENTS
    TkMacOSXInitNamedSymbol(HIToolbox, void, DebugTraceEvent, OSType, UInt32,
	    Boolean);
    if (DebugTraceEvent) {
	unsigned int i;
	const EventTypeSpec *e;

	for (i = 0, e = windowEventTypes;
		i < GetEventTypeCount(windowEventTypes); i++, e++) {
	    if (!(e->eventClass == kEventClassMouse && (
		    e->eventKind == kEventMouseMoved ||
		    e->eventKind == kEventMouseDragged))) {
		DebugTraceEvent(e->eventClass, e->eventKind, 1);
	    }
	}
    }
#endif /* TK_MAC_DEBUG_CARBON_EVENTS */
}

/*
 *----------------------------------------------------------------------
 *
 * InstallStandardApplicationEventHandler --
 *
 *	This procedure installs the carbon standard application event
 *	handler.
 *
 * Results:
 *	OS status code.
 *
 * Side effects:
 *	Standard handlers for application Carbon Events are registered.
 *
 *----------------------------------------------------------------------
 */

static OSStatus
InstallStandardApplicationEventHandler(void)
{
    OSStatus err = memFullErr;

    TK_IF_HI_TOOLBOX(5,
       /*
	* The approach below does not work correctly in Leopard, it leads to
	* crashes in [NSView unlockFocus] whenever HIToolbox uses Cocoa (Help
	* menu, Nav Services, Color Picker). While it is now possible to
	* install the standard app handler with InstallStandardEventHandler(),
	* to fully replicate RAEL the standard menubar event handler also needs
	* to be installed. Unfortunately there appears to be no public API to
	* obtain the menubar event target. As a workaround, for now we resort
	* to calling the HIToolbox-internal GetMenuBarEventTarget() directly
	* (symbol acquired via TkMacOSXInitNamedSymbol() from HIToolbox
	* version 343, may not exist in later versions).
	*/
	err = ChkErr(InstallStandardEventHandler, GetApplicationEventTarget());
	TkMacOSXInitNamedSymbol(HIToolbox, EventTargetRef,
		GetMenuBarEventTarget, void);
	if (GetMenuBarEventTarget) {
	    ChkErr(InstallStandardEventHandler, GetMenuBarEventTarget());
	} else {
	    TkMacOSXDbgMsg("Unable to install standard menubar event handler");
	}
    ) TK_ELSE_HI_TOOLBOX (5,
       /*
	* This is a hack to workaround missing Carbon API to install the
	* standard application event handler (InstallStandardEventHandler()
	* does not work on the application target). The only way to install the
	* standard app handler is to call RunApplicationEventLoop(), but since
	* we are running our own event loop, we'll immediately need to break
	* out of RAEL again: we do this via longjmp out of the
	* ExitRaelEventHandlerProc event handler called first off from RAEL by
	* posting a high priority dummy event. This workaround is derived from
	* a similar approach in Technical Q&A 1061.
	*/
	enum {
	    kExitRaelEvent = 'ExiT'
	};
	const EventTypeSpec exitRaelEventType = {
	    kExitRaelEvent, kExitRaelEvent
	};
	EventHandlerUPP exitRaelEventHandler;
	EventHandlerRef exitRaelEventHandlerRef = NULL;
	EventRef exitRaelEvent = NULL;

	exitRaelEventHandler = NewEventHandlerUPP(
		(EventHandlerProcPtr) ExitRaelEventHandlerProc);
	if (exitRaelEventHandler) {
	    err = ChkErr(InstallEventHandler, GetEventDispatcherTarget(),
		    exitRaelEventHandler, 1, &exitRaelEventType, NULL,
		    &exitRaelEventHandlerRef);
	}
	if (err == noErr) {
	    err = ChkErr(CreateEvent, NULL, kExitRaelEvent, kExitRaelEvent,
		    GetCurrentEventTime(), kEventAttributeNone,
		    &exitRaelEvent);
	}
	if (err == noErr) {
	    err = ChkErr(PostEventToQueue, GetMainEventQueue(), exitRaelEvent,
		    kEventPriorityHigh);
	}
	if (err == noErr) {
	    if (!setjmp(exitRaelJmpBuf)) {
		RunApplicationEventLoop();

		/*
		 * This point should never be reached!
		 */

		Tcl_Panic("RunApplicationEventLoop exited !");
	    }
	}
	if (exitRaelEvent) {
	    ReleaseEvent(exitRaelEvent);
	}
	if (exitRaelEventHandlerRef) {
	    RemoveEventHandler(exitRaelEventHandlerRef);
	}
	if (exitRaelEventHandler) {
	    DisposeEventHandlerUPP(exitRaelEventHandler);
	}
    ) TK_ENDIF
    return err;
}

#if MAC_OS_X_VERSION_MIN_REQUIRED < 1050
/*
 *----------------------------------------------------------------------
 *
 * ExitRaelEventHandlerProc --
 *
 *	This procedure is the dummy event handler used to break out of
 *	RAEL via longjmp, it is called as the first ever event handler
 *	in RAEL by posting a high priority dummy event.
 *
 * Results:
 *	None. Never returns !
 *
 * Side effects:
 *	longjmp back to InstallStandardApplicationEventHandler().
 *
 *----------------------------------------------------------------------
 */

static void
ExitRaelEventHandlerProc(
    EventHandlerCallRef callRef,
    EventRef event,
    void *userData)
{
    longjmp(exitRaelJmpBuf, 1);
}
#endif

/*
 *----------------------------------------------------------------------
 *
 * TkMacOSXRunTclEventLoop --
 *
 *	Process a limited number of tcl events.
 *
 * Results:
 *	Returns 1 if events were handled and 0 otherwise.
 *
 * Side effects:
 *	Runs the Tcl event loop.
 *
 *----------------------------------------------------------------------
 */

MODULE_SCOPE int
TkMacOSXRunTclEventLoop(void)
{
    int i = 4, result = 0;

    /* Avoid starving main event loop: process at most 4 events. */
    while(--i && Tcl_ServiceAll()) {
	result = 1;
    }
    return result;
}

/*
 *----------------------------------------------------------------------
 *
 * CarbonTimerProc --
 *
 *	This procedure is the carbon timer handler that runs the tcl
 *	event loop periodically.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	Runs the Tcl event loop.
 *
 *----------------------------------------------------------------------
 */

static void
CarbonTimerProc(
    EventLoopTimerRef timer,
    void *userData)
{
    if(carbonTimerEnabled > 0 && TkMacOSXRunTclEventLoop()) {
#ifdef TK_MAC_DEBUG_CARBON_EVENTS
	TkMacOSXDbgMsg("Processed tcl events from carbon timer");
#endif /* TK_MAC_DEBUG_CARBON_EVENTS */
    }
}

/*
 *----------------------------------------------------------------------
 *
 * TkMacOSXStartTclEventLoopCarbonTimer --
 *
 *	This procedure installs (if necessary) and starts a carbon
 *	event timer that runs the tcl event loop periodically.
 *	It should be called whenever a nested carbon event loop might
 *	run by HIToolbox (e.g. during mouse tracking) to ensure that
 *	tcl events continue to be processed.
 *
 * Results:
 *	OS status code.
 *
 * Side effects:
 *	Carbon event timer is installed and started.
 *
 *----------------------------------------------------------------------
 */

MODULE_SCOPE OSStatus
TkMacOSXStartTclEventLoopCarbonTimer(void)
{
    OSStatus err = noErr;

    if (++carbonTimerEnabled > 0) {
	if(!carbonTimer) {
	    EventLoopTimerUPP timerUPP = NewEventLoopTimerUPP(CarbonTimerProc);

	    err = ChkErr(InstallEventLoopTimer, GetMainEventLoop(),
		    5 * kEventDurationMillisecond,
		    5 * kEventDurationMillisecond,
		    timerUPP, NULL, &carbonTimer);
	} else {
	    err = ChkErr(SetEventLoopTimerNextFireTime, carbonTimer,
		    5 * kEventDurationMillisecond);
	}
    }
    return err;
}

/*
 *----------------------------------------------------------------------
 *
 * TkMacOSXStopTclEventLoopCarbonTimer --
 *
 *	This procedure stops the carbon event timer started by
 *	TkMacOSXStartTclEventLoopCarbonTimer().
 *
 * Results:
 *	OS status code.
 *
 * Side effects:
 *	Carbon event timer is stopped.
 *
 *----------------------------------------------------------------------
 */

MODULE_SCOPE OSStatus
TkMacOSXStopTclEventLoopCarbonTimer(void)
{
    OSStatus err = noErr;

    if (--carbonTimerEnabled == 0) {
	if(carbonTimer) {
	    err = ChkErr(SetEventLoopTimerNextFireTime, carbonTimer,
		    kEventDurationForever);
	}
    }
    return err;
}

/*
 *----------------------------------------------------------------------
 *
 * TkMacOSXTrackingLoop --
 *
 *	Call with 1 before entering a mouse tracking loop (e.g. window
 *	resizing or menu tracking) to enable tcl event processing but
 *	disable  carbon event processing (except for update events)
 *	during the loop, and with 0 after exiting the loop to reset.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */

MODULE_SCOPE void
TkMacOSXTrackingLoop(int tracking)
{
    static int previousServiceMode = TCL_SERVICE_NONE;

    if (tracking) {
	inTrackingLoop++;
	previousServiceMode = Tcl_SetServiceMode(TCL_SERVICE_ALL);
	TkMacOSXStartTclEventLoopCarbonTimer();
#ifdef TK_MAC_DEBUG_CARBON_EVENTS
	TkMacOSXDbgMsg("Entering tracking loop");
#endif /* TK_MAC_DEBUG_CARBON_EVENTS */
    } else {
	TkMacOSXStopTclEventLoopCarbonTimer();
	previousServiceMode = Tcl_SetServiceMode(previousServiceMode);
	inTrackingLoop--;
#ifdef TK_MAC_DEBUG_CARBON_EVENTS
	TkMacOSXDbgMsg("Exiting tracking loop");
#endif /* TK_MAC_DEBUG_CARBON_EVENTS */
    }
}

/*
 *----------------------------------------------------------------------
 *
 * TkMacOSXReceiveAndDispatchEvent --
 *
 *	This receives a carbon event and sends it to the carbon event
 *	dispatcher.
 *
 * Results:
 *	Mac OS status
 *
 * Side effects:
 *	This receives and dispatches the next Carbon event.
 *
 *----------------------------------------------------------------------
 */
MODULE_SCOPE OSStatus
TkMacOSXReceiveAndDispatchEvent(void)
{
    static EventTargetRef targetRef = NULL;
    int numEventTypes = 0;
    const EventTypeSpec *eventTypes = NULL;
    EventRef eventRef;
    OSStatus err;
    const EventTypeSpec trackingEventTypes[] = {
	{'dniw',		 kEventWindowUpdate},
	{kEventClassWindow,	 kEventWindowUpdate},
    };

    if (inTrackingLoop > 0) {
	eventTypes = trackingEventTypes;
	numEventTypes = GetEventTypeCount(trackingEventTypes);
    }

    /*
     * This is a poll, since we have already counted the events coming
     * into this routine, and are guaranteed to have one waiting.
     */

    err = ReceiveNextEvent(numEventTypes, eventTypes,
	    kEventDurationNoWait, true, &eventRef);
    if (err == noErr) {
#ifdef TK_MAC_DEBUG_CARBON_EVENTS
	UInt32 kind = GetEventKind(eventRef);

	if (kind != kEventMouseMoved && kind != kEventMouseDragged) {
	    TkMacOSXDbgMsg("Dispatching %s", TkMacOSXCarbonEventToAscii(eventRef));
	    TkMacOSXInitNamedDebugSymbol(HIToolbox, void, _DebugPrintEvent,
		    EventRef inEvent);
	    if (_DebugPrintEvent) {
		/* Carbon-internal event debugging (c.f. Technote 2124) */
		_DebugPrintEvent(eventRef);
	    }
	}
#endif /* TK_MAC_DEBUG_CARBON_EVENTS */
	if (!targetRef) {
	    targetRef = GetEventDispatcherTarget();
	}
	TkMacOSXStartTclEventLoopCarbonTimer();
	err = SendEventToEventTarget(eventRef, targetRef);
	TkMacOSXStopTclEventLoopCarbonTimer();
	if (err != noErr && err != eventLoopTimedOutErr
		&& err != eventNotHandledErr) {
	    TkMacOSXDbgMsg("SendEventToEventTarget(%s) failed: %ld",
		    TkMacOSXCarbonEventToAscii(eventRef), err);
	}
	ReleaseEvent(eventRef);
    } else if (err != eventLoopTimedOutErr) {
	TkMacOSXDbgMsg("ReceiveNextEvent failed: %ld", err);
    }
    return err;
}

/*
 * Local Variables:
 * mode: c
 * c-basic-offset: 4
 * fill-column: 79
 * coding: utf-8
 * End:
 */
