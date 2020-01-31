/*
 * tkUnix.c --
 *
 *	This file contains procedures that are UNIX/X-specific, and will
 *	probably have to be written differently for Windows or Macintosh
 *	platforms.
 *
 * Copyright (c) 1995 Sun Microsystems, Inc.
 *
 * See the file "license.terms" for information on usage and redistribution of
 * this file, and for a DISCLAIMER OF ALL WARRANTIES.
 *
 * RCS: @(#) $Id: tkUnix.c,v 1.15 2007/12/13 15:28:50 dgp Exp $
 */

#include "tkInt.h"
#ifdef HAVE_XSS
#include <X11/extensions/scrnsaver.h>
#endif

/*
 *----------------------------------------------------------------------
 *
 * TkGetServerInfo --
 *
 *	Given a window, this procedure returns information about the window
 *	server for that window. This procedure provides the guts of the "winfo
 *	server" command.
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
TkGetServerInfo(
    Tcl_Interp *interp,		/* The server information is returned in this
				 * interpreter's result. */
    Tk_Window tkwin)		/* Token for window; this selects a particular
				 * display and server. */
{
    char buffer[8 + TCL_INTEGER_SPACE * 2];
    char buffer2[TCL_INTEGER_SPACE];

    sprintf(buffer, "X%dR%d ", ProtocolVersion(Tk_Display(tkwin)),
	    ProtocolRevision(Tk_Display(tkwin)));
    sprintf(buffer2, " %d", VendorRelease(Tk_Display(tkwin)));
    Tcl_AppendResult(interp, buffer, ServerVendor(Tk_Display(tkwin)),
	    buffer2, (char *) NULL);
}

/*
 *----------------------------------------------------------------------
 *
 * TkGetDefaultScreenName --
 *
 *	Returns the name of the screen that Tk should use during
 *	initialization.
 *
 * Results:
 *	Returns the argument or a string that should not be freed by the
 *	caller.
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */

CONST char *
TkGetDefaultScreenName(
    Tcl_Interp *interp,		/* Interp used to find environment
				 * variables. */
    CONST char *screenName)	/* Screen name from command line, or NULL. */
{
    if ((screenName == NULL) || (screenName[0] == '\0')) {
	screenName = Tcl_GetVar2(interp, "env", "DISPLAY", TCL_GLOBAL_ONLY);
    }
    return screenName;
}

/*
 *----------------------------------------------------------------------
 *
 * Tk_UpdatePointer --
 *
 *	Unused function in UNIX
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
Tk_UpdatePointer(
    Tk_Window tkwin,		/* Window to which pointer event is reported.
				 * May be NULL. */
    int x, int y,		/* Pointer location in root coords. */
    int state)			/* Modifier state mask. */
{
  /*
   * This function intentionally left blank
   */
}

/*
 *----------------------------------------------------------------------
 *
 * TkpBuildRegionFromAlphaData --
 *
 *	Set up a rectangle of the given region based on the supplied alpha
 *	data.
 *
 * Results:
 *	None
 *
 * Side effects:
 *	The region is updated, with extra pixels added to it.
 *
 *----------------------------------------------------------------------
 */

void
TkpBuildRegionFromAlphaData(
    TkRegion region,		/* Region to be updated. */
    unsigned x, unsigned y,	/* Where in region to update. */
    unsigned width, unsigned height,
				/* Size of rectangle to update. */
    unsigned char *dataPtr,	/* Data to read from. */
    unsigned pixelStride,	/* Num bytes from one piece of alpha data to
				 * the next in the line. */
    unsigned lineStride)	/* Num bytes from one line of alpha data to
				 * the next line. */
{
    unsigned char *lineDataPtr;
    unsigned int x1, y1, end;
    XRectangle rect;

    for (y1 = 0; y1 < height; y1++) {
	lineDataPtr = dataPtr;
	for (x1 = 0; x1 < width; x1 = end) {
	    /*
	     * Search for first non-transparent pixel.
	     */

	    while ((x1 < width) && !*lineDataPtr) {
		x1++;
		lineDataPtr += pixelStride;
	    }
	    end = x1;

	    /*
	     * Search for first transparent pixel.
	     */

	    while ((end < width) && *lineDataPtr) {
		end++;
		lineDataPtr += pixelStride;
	    }
	    if (end > x1) {
		rect.x = x + x1;
		rect.y = y + y1;
		rect.width = end - x1;
		rect.height = 1;
		TkUnionRectWithRegion(&rect, region, region);
	    }
	}
	dataPtr += lineStride;
    }
}

/*
 *----------------------------------------------------------------------
 *
 * Tk_GetUserInactiveTime --
 *
 *	Return the number of milliseconds the user was inactive.
 *
 * Results:
 *	The number of milliseconds since the user's latest interaction with
 *	the system on the given display, or -1 if the XScreenSaver extension
 *	is not supported by the client libraries or the X server
 *	implementation.
 *
 * Side effects:
 *	None.
 *----------------------------------------------------------------------
 */

long
Tk_GetUserInactiveTime(
    Display *dpy)		/* The display for which to query the inactive
				 * time. */
{
    long inactiveTime = -1;
#ifdef HAVE_XSS
    int eventBase, errorBase, major, minor;

    /*
     * Calling XScreenSaverQueryVersion seems to be needed to prevent a crash
     * on some buggy versions of XFree86.
     */

    if (
#ifdef __APPLE__
 	XScreenSaverQueryInfo != NULL && /* Support for weak-linked libXss. */
#endif
	XScreenSaverQueryExtension(dpy, &eventBase, &errorBase) &&
	XScreenSaverQueryVersion(dpy, &major, &minor)) {

	XScreenSaverInfo *info = XScreenSaverAllocInfo();

	if (info == NULL) {
	    /*
	     * We are out of memory.
	     */

	    Tcl_Panic("Out of memory: XScreenSaverAllocInfo failed in Tk_GetUserInactiveTime");
	}
	if (XScreenSaverQueryInfo(dpy, DefaultRootWindow(dpy), info)) {
	    inactiveTime = info->idle;
	}
	XFree(info);
    }
#endif /* HAVE_XSS */
    return inactiveTime;
}

/*
 *----------------------------------------------------------------------
 *
 * Tk_ResetUserInactiveTime --
 *
 *	Reset the user inactivity timer
 *
 * Results:
 *	none
 *
 * Side effects:
 *	The user inactivity timer of the underlaying windowing system is reset
 *	to zero.
 *
 *----------------------------------------------------------------------
 */

void
Tk_ResetUserInactiveTime(
    Display *dpy)
{
    XResetScreenSaver(dpy);
}

/*
 * Local Variables:
 * mode: c
 * c-basic-offset: 4
 * fill-column: 78
 * End:
 */
