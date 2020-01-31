/*
 * xgc.c --
 *
 *	This file contains generic routines for manipulating X graphics
 *	contexts.
 *
 * Copyright (c) 1995-1996 Sun Microsystems, Inc.
 * Copyright (c) 2002-2007 Daniel A. Steffen <das@users.sourceforge.net>
 *
 * See the file "license.terms" for information on usage and redistribution of
 * this file, and for a DISCLAIMER OF ALL WARRANTIES.
 *
 * RCS: @(#) $Id: xgc.c,v 1.16 2007/12/13 15:29:45 dgp Exp $
 */

#include <tkInt.h>

#if !defined(MAC_OSX_TK)
#   include <X11/Xlib.h>
#endif
#ifdef MAC_OSX_TK
#   include <tkMacOSXInt.h>
#   include <X11/Xlib.h>
#   include <X11/X.h>
#   define Cursor XCursor
#   define Region XRegion
#endif


/*
 *----------------------------------------------------------------------
 *
 * AllocClipMask --
 *
 *	Static helper proc to allocate new or clear existing TkpClipMask.
 *
 * Results:
 *	Returns ptr to the new/cleared TkpClipMask.
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */

static TkpClipMask *AllocClipMask(GC gc) {
    TkpClipMask *clip_mask = (TkpClipMask*) gc->clip_mask;
    
    if (clip_mask == None) {
	clip_mask = (TkpClipMask*) ckalloc(sizeof(TkpClipMask));
	gc->clip_mask = (Pixmap) clip_mask;
#ifdef MAC_OSX_TK
    } else if (clip_mask->type == TKP_CLIP_REGION) {
	TkpReleaseRegion(clip_mask->value.region);
#endif
    }
    return clip_mask;
}

/*
 *----------------------------------------------------------------------
 *
 * FreeClipMask --
 *
 *	Static helper proc to free TkpClipMask.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */

static void FreeClipMask(GC gc) {
    if (gc->clip_mask != None) {
#ifdef MAC_OSX_TK
	if (((TkpClipMask*) gc->clip_mask)->type == TKP_CLIP_REGION) {
	    TkpReleaseRegion(((TkpClipMask*) gc->clip_mask)->value.region);
	}
#endif
	ckfree((char*) gc->clip_mask);
	gc->clip_mask = None;
    }
}

/*
 *----------------------------------------------------------------------
 *
 * XCreateGC --
 *
 *	Allocate a new GC, and initialize the specified fields.
 *
 * Results:
 *	Returns a newly allocated GC.
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */

GC
XCreateGC(
    Display *display,
    Drawable d,
    unsigned long mask,
    XGCValues *values)
{
    GC gp;

    /*
     * In order to have room for a dash list, MAX_DASH_LIST_SIZE extra chars
     * are defined, which is invisible from the outside. The list is assumed
     * to end with a 0-char, so this must be set explicitely during
     * initialization.
     */

#define MAX_DASH_LIST_SIZE 10

    gp = (XGCValues *) ckalloc(sizeof(XGCValues) + MAX_DASH_LIST_SIZE);
    if (!gp) {
	return None;
    }

#define InitField(name,maskbit,default) \
	(gp->name = (mask & (maskbit)) ? values->name : (default))

    InitField(function,		  GCFunction,		GXcopy);
    InitField(plane_mask,	  GCPlaneMask,		(unsigned long)(~0));
    InitField(foreground,	  GCForeground,		
	    BlackPixelOfScreen(DefaultScreenOfDisplay(display)));
    InitField(background,	  GCBackground,		
	    WhitePixelOfScreen(DefaultScreenOfDisplay(display)));
    InitField(line_width,	  GCLineWidth,		1);
    InitField(line_style,	  GCLineStyle,		LineSolid);
    InitField(cap_style,	  GCCapStyle,		0);
    InitField(join_style,	  GCJoinStyle,		0);
    InitField(fill_style,	  GCFillStyle,		FillSolid);
    InitField(fill_rule,	  GCFillRule,		WindingRule);
    InitField(arc_mode,		  GCArcMode,		ArcPieSlice);
    InitField(tile,		  GCTile,		None);
    InitField(stipple,		  GCStipple,		None);
    InitField(ts_x_origin,	  GCTileStipXOrigin,	0);
    InitField(ts_y_origin,	  GCTileStipYOrigin,	0);
    InitField(font,		  GCFont,		None);
    InitField(subwindow_mode,	  GCSubwindowMode,	ClipByChildren);
    InitField(graphics_exposures, GCGraphicsExposures,	True);
    InitField(clip_x_origin,	  GCClipXOrigin,	0);
    InitField(clip_y_origin,	  GCClipYOrigin,	0);
    InitField(dash_offset,	  GCDashOffset,		0);
    InitField(dashes,		  GCDashList,		4);
    (&(gp->dashes))[1] = 0;

    gp->clip_mask = None;
    if (mask & GCClipMask) {
	TkpClipMask *clip_mask = AllocClipMask(gp);
	
	clip_mask->type = TKP_CLIP_PIXMAP;
	clip_mask->value.pixmap = values->clip_mask;
    }

    return gp;
}

/*
 *----------------------------------------------------------------------
 *
 * XChangeGC --
 *
 *	Changes the GC components specified by valuemask for the specified GC.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	Updates the specified GC.
 *
 *----------------------------------------------------------------------
 */

void
XChangeGC(
    Display *d,
    GC gc,
    unsigned long mask,
    XGCValues *values)
{
#define ModifyField(name,maskbit) \
	if (mask & (maskbit)) { gc->name = values->name; }

    ModifyField(function, GCFunction);
    ModifyField(plane_mask, GCPlaneMask);
    ModifyField(foreground, GCForeground);
    ModifyField(background, GCBackground);
    ModifyField(line_width, GCLineWidth);
    ModifyField(line_style, GCLineStyle);
    ModifyField(cap_style, GCCapStyle);
    ModifyField(join_style, GCJoinStyle);
    ModifyField(fill_style, GCFillStyle);
    ModifyField(fill_rule, GCFillRule);
    ModifyField(arc_mode, GCArcMode);
    ModifyField(tile, GCTile);
    ModifyField(stipple, GCStipple);
    ModifyField(ts_x_origin, GCTileStipXOrigin);
    ModifyField(ts_y_origin, GCTileStipYOrigin);
    ModifyField(font, GCFont);
    ModifyField(subwindow_mode, GCSubwindowMode);
    ModifyField(graphics_exposures, GCGraphicsExposures);
    ModifyField(clip_x_origin, GCClipXOrigin);
    ModifyField(clip_y_origin, GCClipYOrigin);
    ModifyField(dash_offset, GCDashOffset);
    if (mask & GCClipMask) {
	XSetClipMask(d, gc, values->clip_mask);
    }
    if (mask & GCDashList) {
	gc->dashes = values->dashes;
	(&(gc->dashes))[1] = 0;
    }
}

/*
 *----------------------------------------------------------------------
 *
 * XFreeGC --
 *
 *	Deallocates the specified graphics context.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */

void XFreeGC(
    Display *d,
    GC gc)
{
    if (gc != None) {
	FreeClipMask(gc);
	ckfree((char *) gc);
    }
}

/*
 *----------------------------------------------------------------------
 *
 * XSetForeground, etc. --
 *
 *	The following functions are simply accessor functions for the GC
 *	slots.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	Each function sets some slot in the GC.
 *
 *----------------------------------------------------------------------
 */

void
XSetForeground(
    Display *display,
    GC gc,
    unsigned long foreground)
{
    gc->foreground = foreground;
}

void
XSetBackground(
    Display *display,
    GC gc,
    unsigned long background)
{
    gc->background = background;
}

void
XSetDashes(
    Display *display,
    GC gc,
    int dash_offset,
    _Xconst char *dash_list,
    int n)
{
    char *p = &(gc->dashes);

#ifdef TkWinDeleteBrush
    TkWinDeleteBrush(gc->fgBrush);
    TkWinDeletePen(gc->fgPen);
    TkWinDeleteBrush(gc->bgBrush);
    TkWinDeletePen(gc->fgExtPen);
#endif
    gc->dash_offset = dash_offset;
    if (n > MAX_DASH_LIST_SIZE) n = MAX_DASH_LIST_SIZE;
    while (n-- > 0) {
	*p++ = *dash_list++;
    }
    *p = 0;
}

void
XSetFunction(
    Display *display,
    GC gc,
    int function)
{
    gc->function = function;
}

void
XSetFillRule(
    Display *display,
    GC gc,
    int fill_rule)
{
    gc->fill_rule = fill_rule;
}

void
XSetFillStyle(
    Display *display,
    GC gc,
    int fill_style)
{
    gc->fill_style = fill_style;
}

void
XSetTSOrigin(
    Display *display,
    GC gc,
    int x, int y)
{
    gc->ts_x_origin = x;
    gc->ts_y_origin = y;
}

void
XSetFont(
    Display *display,
    GC gc,
    Font font)
{
    gc->font = font;
}

void
XSetArcMode(
    Display *display,
    GC gc,
    int arc_mode)
{
    gc->arc_mode = arc_mode;
}

void
XSetStipple(
    Display *display,
    GC gc,
    Pixmap stipple)
{
    gc->stipple = stipple;
}

void
XSetLineAttributes(
    Display *display,
    GC gc,
    unsigned int line_width,
    int line_style,
    int cap_style,
    int join_style)
{
    gc->line_width = line_width;
    gc->line_style = line_style;
    gc->cap_style = cap_style;
    gc->join_style = join_style;
}

void
XSetClipOrigin(
    Display *display,
    GC gc,
    int clip_x_origin,
    int clip_y_origin)
{
    gc->clip_x_origin = clip_x_origin;
    gc->clip_y_origin = clip_y_origin;
}

/*
 *----------------------------------------------------------------------
 *
 * TkSetRegion, XSetClipMask --
 *
 *	Sets the clipping region/pixmap for a GC.
 *
 *	Note that unlike the Xlib equivalent, it is not safe to delete the
 *	region after setting it into the GC (except on Mac OS X). The only
 *	uses of TkSetRegion are currently in DisplayFrame and in
 *	ImgPhotoDisplay, which use the GC immediately.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	Allocates or dealloates a TkpClipMask.
 *
 *----------------------------------------------------------------------
 */

void
TkSetRegion(
    Display *display,
    GC gc,
    TkRegion r)
{
    if (r == None) {
	FreeClipMask(gc);
    } else {
	TkpClipMask *clip_mask = AllocClipMask(gc);

	clip_mask->type = TKP_CLIP_REGION;
	clip_mask->value.region = r;
#ifdef MAC_OSX_TK
	TkpRetainRegion(r);
#endif
    }
}

void
XSetClipMask(
    Display *display,
    GC gc,
    Pixmap pixmap)
{
    if (pixmap == None) {
	FreeClipMask(gc);
    } else {
	TkpClipMask *clip_mask = AllocClipMask(gc);

	clip_mask->type = TKP_CLIP_PIXMAP;
	clip_mask->value.pixmap = pixmap;
    }
}

/*
 * Some additional dummy functions (hopefully implemented soon).
 */

#if 0
Cursor
XCreateFontCursor(
    Display *display,
    unsigned int shape)
{
    return (Cursor) 0;
}

void
XDrawImageString(
    Display *display,
    Drawable d,
    GC gc,
    int x,
    int y,
    _Xconst char *string,
    int length)
{
}
#endif

void
XDrawPoint(
    Display *display,
    Drawable d,
    GC gc,
    int x,
    int y)
{
    XDrawLine(display, d, gc, x, y, x, y);
}

void
XDrawPoints(
    Display *display,
    Drawable d,
    GC gc,
    XPoint *points,
    int npoints,
    int mode)
{
    int i;

    for (i=0; i<npoints; i++) {
	XDrawLine(display, d, gc,
		points[i].x, points[i].y, points[i].x, points[i].y);
    }
}

#if !defined(MAC_OSX_TK)
void
XDrawSegments(
    Display *display,
    Drawable d,
    GC gc,
    XSegment *segments,
    int nsegments)
{
}
#endif

#if 0
char *
XFetchBuffer(
    Display *display,
    int *nbytes_return,
    int buffer)
{
    return (char *) 0;
}

Status
XFetchName(
    Display *display,
    Window w,
    char **window_name_return)
{
    return (Status) 0;
}

Atom *
XListProperties(
    Display* display,
    Window w,
    int *num_prop_return)
{
    return (Atom *) 0;
}

void
XMapRaised(
    Display *display,
    Window w)
{
}

void
XPutImage(
    Display *display,
    Drawable d,
    GC gc,
    XImage *image,
    int src_x,
    int src_y,
    int dest_x,
    int dest_y,
    unsigned int width,
    unsigned int height)
{
}

void
XQueryTextExtents(
    Display *display,
    XID font_ID,
    _Xconst char *string,
    int nchars,
    int *direction_return,
    int *font_ascent_return,
    int *font_descent_return,
    XCharStruct *overall_return)
{
}

void
XReparentWindow(
    Display *display,
    Window w,
    Window parent,
    int x,
    int y)
{
}

void
XRotateBuffers(
    Display *display,
    int rotate)
{
}

void
XStoreBuffer(
    Display *display,
    _Xconst char *bytes,
    int nbytes,
    int buffer)
{
}

void
XUndefineCursor(
    Display *display,
    Window w)
{
}
#endif

/*
 * Local Variables:
 * mode: c
 * c-basic-offset: 4
 * fill-column: 78
 * End:
 */
