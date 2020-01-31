/*
 * tkUnixKey.c --
 *
 *	This file contains routines for dealing with international keyboard
 *	input.
 *
 * Copyright (c) 1997 by Sun Microsystems, Inc.
 *
 * See the file "license.terms" for information on usage and redistribution of
 * this file, and for a DISCLAIMER OF ALL WARRANTIES.
 *
 * RCS: @(#) $Id: tkUnixKey.c,v 1.13.2.1 2008/06/11 00:41:25 jenglish Exp $
 */

#include "tkInt.h"

/*
 * Prototypes for local functions defined in this file:
 */

/*
 *----------------------------------------------------------------------
 *
 * Tk_SetCaretPos --
 *
 *	This enables correct placement of the XIM caret. This is called by
 *	widgets to indicate their cursor placement.  This is currently only
 *	used for over-the-spot XIM.
 *
 *----------------------------------------------------------------------
 */

void
Tk_SetCaretPos(
    Tk_Window tkwin,
    int x,
    int y,
    int height)
{
    TkWindow *winPtr = (TkWindow *) tkwin;
    TkDisplay *dispPtr = winPtr->dispPtr;

    if (   dispPtr->caret.winPtr == winPtr
	&& dispPtr->caret.x == x
	&& dispPtr->caret.y == y
	&& dispPtr->caret.height == height) 
    {
	return;
    }

    dispPtr->caret.winPtr = winPtr;
    dispPtr->caret.x = x;
    dispPtr->caret.y = y;
    dispPtr->caret.height = height;

#ifdef TK_USE_INPUT_METHODS
    /*
     * Adjust the XIM caret position.
     */
    if (   (dispPtr->flags & TK_DISPLAY_USE_IM)
	&& (dispPtr->inputStyle & XIMPreeditPosition)
	&& (winPtr->inputContext != NULL) )
    {
	XVaNestedList preedit_attr;
	XPoint spot;

	spot.x = dispPtr->caret.x;
	spot.y = dispPtr->caret.y + dispPtr->caret.height;
	preedit_attr = XVaCreateNestedList(0, XNSpotLocation, &spot, NULL);
	XSetICValues(winPtr->inputContext,
		XNPreeditAttributes, preedit_attr,
		NULL);
	XFree(preedit_attr);
    }
#endif
}

/*
 *----------------------------------------------------------------------
 *
 * TkpGetChar --
 *
 *	Convert a keyboard event to a UTF-8 string using XLookupString.
 *
 *	This is used as a fallback instead of Xutf8LookupString
 *	or XmbLookupString if input methods are turned off
 *	and for KeyRelease events.
 *
 * Notes:
 *	XLookupString() normally returns a single ISO Latin 1
 *	or ASCII control character.
 *
 *----------------------------------------------------------------------
 */
static char *
TkpGetChar(
    XEvent *eventPtr,		/* KeyPress or KeyRelease event */
    Tcl_DString *dsPtr)		/* Initialized, empty string to hold result. */
{
    int len;
    char buf[TCL_DSTRING_STATIC_SIZE];

    len = XLookupString(&eventPtr->xkey, buf, TCL_DSTRING_STATIC_SIZE, 0, 0);
    buf[len] = '\0';

    if (len == 1) {
	len = Tcl_UniCharToUtf((unsigned char)buf[0], Tcl_DStringValue(dsPtr));
	Tcl_DStringSetLength(dsPtr, len);
    } else {
	/*
	 * len > 1 should only happen if someone has called XRebindKeysym().
	 * Assume UTF-8.
	 */
	Tcl_DStringSetLength(dsPtr, len);
	strncpy(Tcl_DStringValue(dsPtr), buf, len);
    }
    return Tcl_DStringValue(dsPtr);
}

/*
 *----------------------------------------------------------------------
 *
 * TkpGetString --
 *
 *	Retrieve the UTF string associated with a keyboard event.
 *
 * Results:
 *	Returns the UTF string.
 *
 * Side effects:
 *	Stores the input string in the specified Tcl_DString. Modifies the
 *	internal input state. This routine can only be called once for a given
 *	event.
 *
 *----------------------------------------------------------------------
 */

char *
TkpGetString(
    TkWindow *winPtr,		/* Window where event occurred */
    XEvent *eventPtr,		/* X keyboard event. */
    Tcl_DString *dsPtr)		/* Initialized, empty string to hold result. */
#ifdef TK_USE_INPUT_METHODS
#if X_HAVE_UTF8_STRING
{
    if ((winPtr->dispPtr->flags & TK_DISPLAY_USE_IM)
	    && (winPtr->inputContext != NULL)
	    && (eventPtr->type == KeyPress)) 
    {
	int len;
	Status status;

	Tcl_DStringSetLength(dsPtr, TCL_DSTRING_STATIC_SIZE-1);
	len = Xutf8LookupString(winPtr->inputContext, &eventPtr->xkey,
		Tcl_DStringValue(dsPtr), Tcl_DStringLength(dsPtr),
		NULL, &status);

	if (status == XBufferOverflow) { /* Expand buffer and try again */
	    Tcl_DStringSetLength(dsPtr, len);
	    len = Xutf8LookupString(winPtr->inputContext, &eventPtr->xkey,
		    Tcl_DStringValue(dsPtr), Tcl_DStringLength(dsPtr), 
		    NULL, &status);
	}
	if ((status != XLookupChars) && (status != XLookupBoth)) {
	    Tcl_DStringSetLength(dsPtr, 0);
	    len = 0;
	}
	Tcl_DStringSetLength(dsPtr, len);

	return Tcl_DStringValue(dsPtr);
    } else {
	return TkpGetChar(eventPtr, dsPtr);
    }
}
#else /* !X_HAVE_UTF8_STRING */
{
    int len;
    Tcl_DString buf;
    Status status;

    /*
     * Overallocate the dstring to the maximum stack amount.
     */

    Tcl_DStringInit(&buf);
    Tcl_DStringSetLength(&buf, TCL_DSTRING_STATIC_SIZE-1);

    if ((winPtr->dispPtr->flags & TK_DISPLAY_USE_IM)
	    && (winPtr->inputContext != NULL)
	    && (eventPtr->type == KeyPress)) {

	len = XmbLookupString(winPtr->inputContext, &eventPtr->xkey,
		Tcl_DStringValue(&buf), Tcl_DStringLength(&buf), NULL,
		&status);

	/*
	 * If the buffer wasn't big enough, grow the buffer and try again.
	 */

	if (status == XBufferOverflow) {
	    Tcl_DStringSetLength(&buf, len);
	    len = XmbLookupString(winPtr->inputContext, &eventPtr->xkey,
		    Tcl_DStringValue(&buf), len, NULL, &status);
	}
	if ((status != XLookupChars) && (status != XLookupBoth)) {
	    len = 0;
	}
    } else {
	return TkpGetChar(eventPtr, dsPtr);
    }

    Tcl_DStringSetLength(&buf, len);
    Tcl_ExternalToUtfDString(NULL, Tcl_DStringValue(&buf), len, dsPtr);
    Tcl_DStringFree(&buf);

    return Tcl_DStringValue(dsPtr);
}

#endif /* X_HAVE_UTF8_STRING */
#else /* !TK_USE_INPUT_METHODS */
{
    return TkpGetChar(eventPtr, dsPtr);
}
#endif


/*
 * When mapping from a keysym to a keycode, need information about the
 * modifier state that should be used so that when they call XKeycodeToKeysym
 * taking into account the xkey.state, they will get back the original keysym.
 */

void
TkpSetKeycodeAndState(
    Tk_Window tkwin,
    KeySym keySym,
    XEvent *eventPtr)
{
    Display *display;
    int state;
    KeyCode keycode;

    display = Tk_Display(tkwin);

    if (keySym == NoSymbol) {
	keycode = 0;
    } else {
	keycode = XKeysymToKeycode(display, keySym);
    }
    if (keycode != 0) {
	for (state = 0; state < 4; state++) {
	    if (XKeycodeToKeysym(display, keycode, state) == keySym) {
		if (state & 1) {
		    eventPtr->xkey.state |= ShiftMask;
		}
		if (state & 2) {
		    TkDisplay *dispPtr;

		    dispPtr = ((TkWindow *) tkwin)->dispPtr;
		    eventPtr->xkey.state |= dispPtr->modeModMask;
		}
		break;
	    }
	}
    }
    eventPtr->xkey.keycode = keycode;
}

/*
 *----------------------------------------------------------------------
 *
 * TkpGetKeySym --
 *
 *	Given an X KeyPress or KeyRelease event, map the keycode in the event
 *	into a KeySym.
 *
 * Results:
 *	The return value is the KeySym corresponding to eventPtr, or NoSymbol
 *	if no matching Keysym could be found.
 *
 * Side effects:
 *	In the first call for a given display, keycode-to-KeySym maps get
 *	loaded.
 *
 *----------------------------------------------------------------------
 */

KeySym
TkpGetKeySym(
    TkDisplay *dispPtr,		/* Display in which to map keycode. */
    XEvent *eventPtr)		/* Description of X event. */
{
    KeySym sym;
    int index;

    /*
     * Refresh the mapping information if it's stale
     */

    if (dispPtr->bindInfoStale) {
	TkpInitKeymapInfo(dispPtr);
    }

    /*
     * Figure out which of the four slots in the keymap vector to use for this
     * key. Refer to Xlib documentation for more info on how this computation
     * works.
     */

    index = 0;
    if (eventPtr->xkey.state & dispPtr->modeModMask) {
	index = 2;
    }
    if ((eventPtr->xkey.state & ShiftMask)
	    || ((dispPtr->lockUsage != LU_IGNORE)
	    && (eventPtr->xkey.state & LockMask))) {
	index += 1;
    }
    sym = XKeycodeToKeysym(dispPtr->display, eventPtr->xkey.keycode, index);

    /*
     * Special handling: if the key was shifted because of Lock, but lock is
     * only caps lock, not shift lock, and the shifted keysym isn't upper-case
     * alphabetic, then switch back to the unshifted keysym.
     */

    if ((index & 1) && !(eventPtr->xkey.state & ShiftMask)
	    && (dispPtr->lockUsage == LU_CAPS)) {
	if (!(((sym >= XK_A) && (sym <= XK_Z))
		|| ((sym >= XK_Agrave) && (sym <= XK_Odiaeresis))
		|| ((sym >= XK_Ooblique) && (sym <= XK_Thorn)))) {
	    index &= ~1;
	    sym = XKeycodeToKeysym(dispPtr->display, eventPtr->xkey.keycode,
		    index);
	}
    }

    /*
     * Another bit of special handling: if this is a shifted key and there is
     * no keysym defined, then use the keysym for the unshifted key.
     */

    if ((index & 1) && (sym == NoSymbol)) {
	sym = XKeycodeToKeysym(dispPtr->display, eventPtr->xkey.keycode,
		index & ~1);
    }
    return sym;
}

/*
 *--------------------------------------------------------------
 *
 * TkpInitKeymapInfo --
 *
 *	This function is invoked to scan keymap information to recompute stuff
 *	that's important for binding, such as the modifier key (if any) that
 *	corresponds to "mode switch".
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	Keymap-related information in dispPtr is updated.
 *
 *--------------------------------------------------------------
 */

void
TkpInitKeymapInfo(
    TkDisplay *dispPtr)		/* Display for which to recompute keymap
				 * information. */
{
    XModifierKeymap *modMapPtr;
    KeyCode *codePtr;
    KeySym keysym;
    int count, i, j, max, arraySize;
#define KEYCODE_ARRAY_SIZE 20

    dispPtr->bindInfoStale = 0;
    modMapPtr = XGetModifierMapping(dispPtr->display);

    /*
     * Check the keycodes associated with the Lock modifier. If any of them is
     * associated with the XK_Shift_Lock modifier, then Lock has to be
     * interpreted as Shift Lock, not Caps Lock.
     */

    dispPtr->lockUsage = LU_IGNORE;
    codePtr = modMapPtr->modifiermap + modMapPtr->max_keypermod*LockMapIndex;
    for (count = modMapPtr->max_keypermod; count > 0; count--, codePtr++) {
	if (*codePtr == 0) {
	    continue;
	}
	keysym = XKeycodeToKeysym(dispPtr->display, *codePtr, 0);
	if (keysym == XK_Shift_Lock) {
	    dispPtr->lockUsage = LU_SHIFT;
	    break;
	}
	if (keysym == XK_Caps_Lock) {
	    dispPtr->lockUsage = LU_CAPS;
	    break;
	}
    }

    /*
     * Look through the keycodes associated with modifiers to see if the the
     * "mode switch", "meta", or "alt" keysyms are associated with any
     * modifiers. If so, remember their modifier mask bits.
     */

    dispPtr->modeModMask = 0;
    dispPtr->metaModMask = 0;
    dispPtr->altModMask = 0;
    codePtr = modMapPtr->modifiermap;
    max = 8*modMapPtr->max_keypermod;
    for (i = 0; i < max; i++, codePtr++) {
	if (*codePtr == 0) {
	    continue;
	}
	keysym = XKeycodeToKeysym(dispPtr->display, *codePtr, 0);
	if (keysym == XK_Mode_switch) {
	    dispPtr->modeModMask |= ShiftMask << (i/modMapPtr->max_keypermod);
	}
	if ((keysym == XK_Meta_L) || (keysym == XK_Meta_R)) {
	    dispPtr->metaModMask |= ShiftMask << (i/modMapPtr->max_keypermod);
	}
	if ((keysym == XK_Alt_L) || (keysym == XK_Alt_R)) {
	    dispPtr->altModMask |= ShiftMask << (i/modMapPtr->max_keypermod);
	}
    }

    /*
     * Create an array of the keycodes for all modifier keys.
     */

    if (dispPtr->modKeyCodes != NULL) {
	ckfree((char *) dispPtr->modKeyCodes);
    }
    dispPtr->numModKeyCodes = 0;
    arraySize = KEYCODE_ARRAY_SIZE;
    dispPtr->modKeyCodes = (KeyCode *)
	    ckalloc((unsigned) (KEYCODE_ARRAY_SIZE * sizeof(KeyCode)));
    for (i = 0, codePtr = modMapPtr->modifiermap; i < max; i++, codePtr++) {
	if (*codePtr == 0) {
	    continue;
	}

	/*
	 * Make sure that the keycode isn't already in the array.
	 */

	for (j = 0; j < dispPtr->numModKeyCodes; j++) {
	    if (dispPtr->modKeyCodes[j] == *codePtr) {
		goto nextModCode;
	    }
	}
	if (dispPtr->numModKeyCodes >= arraySize) {
	    KeyCode *new;

	    /*
	     * Ran out of space in the array; grow it.
	     */

	    arraySize *= 2;
	    new = (KeyCode *)
		    ckalloc((unsigned) (arraySize * sizeof(KeyCode)));
	    memcpy(new, dispPtr->modKeyCodes,
		    (dispPtr->numModKeyCodes * sizeof(KeyCode)));
	    ckfree((char *) dispPtr->modKeyCodes);
	    dispPtr->modKeyCodes = new;
	}
	dispPtr->modKeyCodes[dispPtr->numModKeyCodes] = *codePtr;
	dispPtr->numModKeyCodes++;
    nextModCode:
	continue;
    }
    XFreeModifiermap(modMapPtr);
}

/*
 * Local Variables:
 * mode: c
 * c-basic-offset: 4
 * fill-column: 78
 * End:
 */
