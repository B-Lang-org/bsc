/*
 * xdraw.c --
 *
 *	This file contains generic procedures related to X drawing primitives.
 *
 * Copyright (c) 1995 Sun Microsystems, Inc.
 *
 * See the file "license.terms" for information on usage and redistribution of
 * this file, and for a DISCLAIMER OF ALL WARRANTIES.
 *
 * RCS: @(#) $Id: xdraw.c,v 1.5 2007/01/02 23:39:40 dkf Exp $
 */

#include "tk.h"

/*
 *----------------------------------------------------------------------
 *
 * XDrawLine --
 *
 *	Draw a single line between two points in a given drawable.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	Draws a single line segment.
 *
 *----------------------------------------------------------------------
 */

void
XDrawLine(
    Display *display,
    Drawable d,
    GC gc,
    int x1, int y1,
    int x2, int y2)		/* Coordinates of line segment. */
{
    XPoint points[2];

    points[0].x = x1;
    points[0].y = y1;
    points[1].x = x2;
    points[1].y = y2;
    XDrawLines(display, d, gc, points, 2, CoordModeOrigin);
}

/*
 *----------------------------------------------------------------------
 *
 * XFillRectangle --
 *
 *	Fills a rectangular area in the given drawable. This procedure is
 *	implemented as a call to XFillRectangles.
 *
 * Results:
 *	None
 *
 * Side effects:
 *	Fills the specified rectangle.
 *
 *----------------------------------------------------------------------
 */

void
XFillRectangle(
    Display *display,
    Drawable d,
    GC gc,
    int x,
    int y,
    unsigned int width,
    unsigned int height)
{
    XRectangle rectangle;
    rectangle.x = x;
    rectangle.y = y;
    rectangle.width = width;
    rectangle.height = height;
    XFillRectangles(display, d, gc, &rectangle, 1);
}

/*
 * Local Variables:
 * mode: c
 * c-basic-offset: 4
 * fill-column: 78
 * End:
 */
