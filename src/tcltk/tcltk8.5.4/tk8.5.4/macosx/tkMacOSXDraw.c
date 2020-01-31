/*
 * tkMacOSXDraw.c --
 *
 *	This file contains functions that perform drawing to
 *	Xlib windows. Most of the functions simple emulate
 *	Xlib functions.
 *
 * Copyright (c) 1995-1997 Sun Microsystems, Inc.
 * Copyright 2001, Apple Computer, Inc.
 * Copyright (c) 2006-2007 Daniel A. Steffen <das@users.sourceforge.net>
 *
 * See the file "license.terms" for information on usage and redistribution
 * of this file, and for a DISCLAIMER OF ALL WARRANTIES.
 *
 * RCS: @(#) $Id: tkMacOSXDraw.c,v 1.33 2008/02/27 00:12:33 das Exp $
 */

#include "tkMacOSXPrivate.h"
#include "tkMacOSXDebug.h"
#include "xbytes.h"

/*
#ifdef TK_MAC_DEBUG
#define TK_MAC_DEBUG_DRAWING
#endif
*/

#define radians(d) ((d) * (M_PI/180.0))

/*
 * Non-antialiased CG drawing looks better and more like X11 drawing when using
 * very fine lines, so decrease all linewidths by the following constant.
 */
#define NON_AA_CG_OFFSET .999

/*
 * Temporary region that can be reused.
 */

RgnHandle tkMacOSXtmpQdRgn = NULL;

int tkMacOSXUseCGDrawing = 1;

int tkPictureIsOpen;

static PixPatHandle penPat = NULL, tmpPixPat = NULL;

static int cgAntiAliasLimit = 0;
#define notAA(w) ((w) < cgAntiAliasLimit)

static int useThemedToplevel = 0;
static int useThemedFrame = 0;

/*
 * Prototypes for functions used only in this file.
 */

static void ClipToGC(Drawable d, GC gc, HIShapeRef *clipRgnPtr);
static void NoQDClip(CGrafPtr port);


/*
 *----------------------------------------------------------------------
 *
 * TkMacOSXInitCGDrawing --
 *
 *	Initializes link vars that control CG drawing.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */

MODULE_SCOPE int
TkMacOSXInitCGDrawing(
    Tcl_Interp *interp,
    int enable,
    int limit)
{
    static Boolean initialized = FALSE;

    if (!initialized) {
	initialized = TRUE;

	if (Tcl_CreateNamespace(interp, "::tk::mac", NULL, NULL) == NULL) {
	    Tcl_ResetResult(interp);
	}
	if (Tcl_LinkVar(interp, "::tk::mac::useCGDrawing",
		(char *) &tkMacOSXUseCGDrawing, TCL_LINK_BOOLEAN) != TCL_OK) {
	    Tcl_ResetResult(interp);
	}
	tkMacOSXUseCGDrawing = enable;

	if (Tcl_LinkVar(interp, "::tk::mac::CGAntialiasLimit",
		(char *) &cgAntiAliasLimit, TCL_LINK_INT) != TCL_OK) {
	    Tcl_ResetResult(interp);
	}
	cgAntiAliasLimit = limit;

	/*
	 * Piggy-back the themed drawing var init here.
	 */

	if (Tcl_LinkVar(interp, "::tk::mac::useThemedToplevel",
		(char *) &useThemedToplevel, TCL_LINK_BOOLEAN) != TCL_OK) {
	    Tcl_ResetResult(interp);
	}
	if (Tcl_LinkVar(interp, "::tk::mac::useThemedFrame",
		(char *) &useThemedFrame, TCL_LINK_BOOLEAN) != TCL_OK) {
	    Tcl_ResetResult(interp);
	}

	if (tkMacOSXtmpQdRgn == NULL) {
	    tkMacOSXtmpQdRgn = NewRgn();
	}
    }
#ifdef TK_MAC_DEBUG_DRAWING
    TkMacOSXInitNamedDebugSymbol(QD, void, QD_DebugPrint, char*);
    if (QD_DebugPrint) {
	; /* gdb: b *QD_DebugPrint */
    }
#endif /* TK_MAC_DEBUG_WINDOWS */
    return TCL_OK;
}

/*
 *----------------------------------------------------------------------
 *
 * XCopyArea --
 *
 *	Copies data from one drawable to another using block transfer
 *	routines.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	Data is moved from a window or bitmap to a second window or
 *	bitmap.
 *
 *----------------------------------------------------------------------
 */

void
XCopyArea(
    Display *display,		/* Display. */
    Drawable src,		/* Source drawable. */
    Drawable dst,		/* Destination drawable. */
    GC gc,			/* GC to use. */
    int src_x,			/* X & Y, width & height */
    int src_y,			/* define the source rectangle */
    unsigned int width,		/* that will be copied. */
    unsigned int height,
    int dest_x,			/* Dest X & Y on dest rect. */
    int dest_y)
{
    TkMacOSXDrawingContext dc;
    MacDrawable *srcDraw = (MacDrawable *) src, *dstDraw = (MacDrawable *) dst;

    display->request++;
    if (!width || !height) {
	/* TkMacOSXDbgMsg("Drawing of emtpy area requested"); */
	return;
    }
    {
	CGrafPtr srcPort;

	srcPort = TkMacOSXGetDrawablePort(src);
	if (srcPort) {
	    Rect srcRect, dstRect, *srcPtr = &srcRect, *dstPtr = &dstRect;
	    const BitMap *srcBit, *dstBit;
	    RGBColor black = {0, 0, 0}, white = {0xffff, 0xffff, 0xffff};

	    if (!TkMacOSXSetupDrawingContext(dst, gc, 0, &dc)) {
		return;
	    }
	    if (dc.context) {
		TkMacOSXDbgMsg("Ignored CG drawing of QD drawable");
		goto end;
	    }
	    if (!dc.port) {
		TkMacOSXDbgMsg("Invalid destination drawable");
		goto end;
	    }
	    srcBit = GetPortBitMapForCopyBits(srcPort);
	    dstBit = GetPortBitMapForCopyBits(dc.port);
	    SetRect(srcPtr, srcDraw->xOff + src_x, srcDraw->yOff + src_y,
		    srcDraw->xOff + src_x + width,
		    srcDraw->yOff + src_y + height);
	    if (tkPictureIsOpen) {
		dstPtr = srcPtr;
	    } else {
		SetRect(dstPtr, dstDraw->xOff + dest_x, dstDraw->yOff + dest_y,
			dstDraw->xOff + dest_x + width,
			dstDraw->yOff + dest_y + height);
	    }
	    RGBForeColor(&black);
	    RGBBackColor(&white);
	    CopyBits(srcBit, dstBit, srcPtr, dstPtr, srcCopy, NULL);
end:
	    TkMacOSXRestoreDrawingContext(&dc);
	} else {
	    TkMacOSXDbgMsg("Invalid source drawable");
	}
    }
}

/*
 *----------------------------------------------------------------------
 *
 * XCopyPlane --
 *
 *	Copies a bitmap from a source drawable to a destination
 *	drawable. The plane argument specifies which bit plane of
 *	the source contains the bitmap. Note that this implementation
 *	ignores the gc->function.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	Changes the destination drawable.
 *
 *----------------------------------------------------------------------
 */

void
XCopyPlane(
    Display *display,		/* Display. */
    Drawable src,		/* Source drawable. */
    Drawable dst,		/* Destination drawable. */
    GC gc,			/* GC to use. */
    int src_x,			/* X & Y, width & height */
    int src_y,			/* define the source rectangle */
    unsigned int width,		/* that will be copied. */
    unsigned int height,
    int dest_x,			/* Dest X & Y on dest rect. */
    int dest_y,
    unsigned long plane)	/* Which plane to copy. */
{
    TkMacOSXDrawingContext dc;
    MacDrawable *srcDraw = (MacDrawable *) src, *dstDraw = (MacDrawable *) dst;

    display->request++;
    if (!width || !height) {
	/* TkMacOSXDbgMsg("Drawing of emtpy area requested"); */
	return;
    }
    if (plane != 1) {
	Tcl_Panic("Unexpected plane specified for XCopyPlane");
    }
    {
	CGrafPtr srcPort;

	srcPort = TkMacOSXGetDrawablePort(src);
	if (srcPort) {
	    Rect srcRect, dstRect, *srcPtr = &srcRect, *dstPtr = &dstRect;
	    const BitMap *srcBit, *dstBit;
	    TkpClipMask *clipPtr = (TkpClipMask *) gc->clip_mask;

	    if (!TkMacOSXSetupDrawingContext(dst, gc, 0, &dc)) {
		return;
	    }
	    if (dc.context) {
		TkMacOSXDbgMsg("Ignored CG drawing of QD drawable");
		goto end;
	    }
	    if (!dc.port) {
		TkMacOSXDbgMsg("Invalid destination drawable");
		goto end;
	    }
	    srcBit = GetPortBitMapForCopyBits(srcPort);
	    dstBit = GetPortBitMapForCopyBits(dc.port);
	    SetRect(srcPtr, srcDraw->xOff + src_x, srcDraw->yOff + src_y,
		    srcDraw->xOff + src_x + width,
		    srcDraw->yOff + src_y + height);
	    if (tkPictureIsOpen) {
		dstPtr = srcPtr;
	    } else {
		SetRect(dstPtr, dstDraw->xOff + dest_x, dstDraw->yOff + dest_y,
			dstDraw->xOff + dest_x + width,
			dstDraw->yOff + dest_y + height);
	    }
	    TkMacOSXSetColorInPort(gc->foreground, 1, NULL, dc.port);
	    if (!clipPtr || clipPtr->type == TKP_CLIP_REGION) {
		/*
		 * Opaque bitmaps.
		 */

		TkMacOSXSetColorInPort(gc->background, 0, NULL, dc.port);
		CopyBits(srcBit, dstBit, srcPtr, dstPtr, srcCopy, NULL);
	    } else if (clipPtr->type == TKP_CLIP_PIXMAP) {
		if (clipPtr->value.pixmap == src) {
		    /*
		     * Transparent bitmaps. If it's color ignore the forecolor.
		     */
		    short tmode = GetPixDepth(GetPortPixMap(srcPort)) == 1 ?
			    srcOr : transparent;

		    CopyBits(srcBit, dstBit, srcPtr, dstPtr, tmode, NULL);
		} else {
		    /*
		     * Two arbitrary bitmaps.
		     */

		    CGrafPtr mskPort = TkMacOSXGetDrawablePort(
			    clipPtr->value.pixmap);
		    const BitMap *mskBit = GetPortBitMapForCopyBits(mskPort);

		    CopyDeepMask(srcBit, mskBit, dstBit, srcPtr, srcPtr,
			    dstPtr, srcCopy, NULL);
		}
	    }
end:
	    TkMacOSXRestoreDrawingContext(&dc);
	} else {
	    TkMacOSXDbgMsg("Invalid source drawable");
	}
    }
}

/*
 *----------------------------------------------------------------------
 *
 * TkPutImage --
 *
 *	Copies a subimage from an in-memory image to a rectangle of
 *	of the specified drawable.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	Draws the image on the specified drawable.
 *
 *----------------------------------------------------------------------
 */

void
TkPutImage(
    unsigned long *colors,	/* Unused on Macintosh. */
    int ncolors,		/* Unused on Macintosh. */
    Display* display,		/* Display. */
    Drawable d,			/* Drawable to place image on. */
    GC gc,			/* GC to use. */
    XImage* image,		/* Image to place. */
    int src_x,			/* Source X & Y. */
    int src_y,
    int dest_x,			/* Destination X & Y. */
    int dest_y,
    unsigned int width,		/* Same width & height for both */
    unsigned int height)	/* distination and source. */
{
    TkMacOSXDrawingContext dc;
    MacDrawable *dstDraw = (MacDrawable *) d;

    display->request++;
    if (!TkMacOSXSetupDrawingContext(d, gc, 0, &dc)) {
	return;
    }
    if (dc.context) {
	TkMacOSXDbgMsg("Ignored CG drawing of XImage");
    } else {
	Rect srcRect, dstRect, *srcPtr = &srcRect, *dstPtr = &dstRect;
	const BitMap *dstBit;
	RGBColor black = {0, 0, 0}, white = {0xffff, 0xffff, 0xffff};
	int i, j;
	char *newData = NULL;
	char *dataPtr, *newPtr, *oldPtr;
	int rowBytes = image->bytes_per_line, sliceRowBytes, lastSliceRowBytes;
	int slices, sliceWidth, lastSliceWidth;

	dstBit = GetPortBitMapForCopyBits(dc.port);
	SetRect(srcPtr, src_x, src_y, src_x + width, src_y + height);
	if (tkPictureIsOpen) {
	    dstPtr = srcPtr;
	} else {
	    SetRect(dstPtr, dstDraw->xOff + dest_x, dstDraw->yOff + dest_y,
		    dstDraw->xOff + dest_x + width,
		    dstDraw->yOff + dest_y + height);
	}
	RGBForeColor(&black);
	RGBBackColor(&white);
	if (image->obdata) {
	    /*
	     * Image from XGetImage, copy from containing GWorld directly.
	     */

	    CopyBits(GetPortBitMapForCopyBits(TkMacOSXGetDrawablePort(
		    (Drawable)image->obdata)), dstBit,
		    srcPtr, dstPtr, srcCopy, NULL);
	} else if (image->depth == 1) {
	    /*
	     * BW image
	     */

	    const int maxRowBytes = 0x3ffe;
	    BitMap bitmap;
	    int odd;

	    if (rowBytes > maxRowBytes) {
		slices = rowBytes / maxRowBytes;
		sliceRowBytes = maxRowBytes;
		lastSliceRowBytes = rowBytes - (slices * maxRowBytes);
		if (!lastSliceRowBytes) {
		    slices--;
		    lastSliceRowBytes = maxRowBytes;
		}
		sliceWidth = (long) image->width * maxRowBytes / rowBytes;
		lastSliceWidth = image->width - (sliceWidth * slices);
	    } else {
		slices = 0;
		sliceRowBytes = lastSliceRowBytes = rowBytes;
		sliceWidth = lastSliceWidth = image->width;
	    }
	    bitmap.bounds.top = bitmap.bounds.left = 0;
	    bitmap.bounds.bottom = (short) image->height;
	    dataPtr = image->data + image->xoffset;
	    do {
		if (slices) {
		    bitmap.bounds.right = bitmap.bounds.left + sliceWidth;
		} else {
		    sliceRowBytes = lastSliceRowBytes;
		    bitmap.bounds.right = bitmap.bounds.left + lastSliceWidth;
		}
		oldPtr = dataPtr;
		odd = sliceRowBytes % 2;
		if (!newData) {
		    newData = ckalloc(image->height * (sliceRowBytes+odd));
		}
		newPtr = newData;
		if (image->bitmap_bit_order != MSBFirst) {
		    for (i = 0; i < image->height; i++) {
			for (j = 0; j < sliceRowBytes; j++) {
			    *newPtr = xBitReverseTable[(unsigned char)*oldPtr];
			    newPtr++; oldPtr++;
			}
			if (odd) {
			    *newPtr++ = 0;
			}
			oldPtr += rowBytes - sliceRowBytes;
		    }
		} else {
		    for (i = 0; i < image->height; i++) {
			memcpy(newPtr, oldPtr, sliceRowBytes);
			newPtr += sliceRowBytes;
			if (odd) {
			    *newPtr++ = 0;
			}
			oldPtr += rowBytes;
		    }
		}
		bitmap.baseAddr = newData;
		bitmap.rowBytes = sliceRowBytes + odd;
		CopyBits(&bitmap, dstBit, srcPtr, dstPtr, srcCopy, NULL);
		if (slices) {
		    bitmap.bounds.left = bitmap.bounds.right;
		    dataPtr += sliceRowBytes;
		}
	    } while (slices--);
	    ckfree(newData);
	} else {
	    /*
	     * Color image
	     */

	    const int maxRowBytes = 0x3ffc;
	    PixMap pixmap;

	    pixmap.bounds.left = 0;
	    pixmap.bounds.top = 0;
	    pixmap.bounds.bottom = (short) image->height;
	    pixmap.pixelType = RGBDirect;
	    pixmap.pmVersion = baseAddr32;	/* 32bit clean */
	    pixmap.packType = 0;
	    pixmap.packSize = 0;
	    pixmap.hRes = 0x00480000;
	    pixmap.vRes = 0x00480000;
	    pixmap.pixelSize = 32;
	    pixmap.cmpCount = 3;
	    pixmap.cmpSize = 8;
	    pixmap.pixelFormat = image->byte_order == MSBFirst ?
		    k32ARGBPixelFormat : k32BGRAPixelFormat;
	    pixmap.pmTable = NULL;
	    pixmap.pmExt = 0;
	    if (rowBytes > maxRowBytes) {
		slices = rowBytes / maxRowBytes;
		sliceRowBytes = maxRowBytes;
		lastSliceRowBytes = rowBytes - (slices * maxRowBytes);
		if (!lastSliceRowBytes) {
		    slices--;
		    lastSliceRowBytes = maxRowBytes;
		}
		sliceWidth = (long) image->width * maxRowBytes / rowBytes;
		lastSliceWidth = image->width - (sliceWidth * slices);
		dataPtr = image->data + image->xoffset;
		newData = (char *) ckalloc(image->height * sliceRowBytes);
		do {
		    if (slices) {
			pixmap.bounds.right = pixmap.bounds.left + sliceWidth;
		    } else {
			sliceRowBytes = lastSliceRowBytes;
			pixmap.bounds.right = pixmap.bounds.left + lastSliceWidth;
		    }
		    oldPtr = dataPtr;
		    newPtr = newData;
		    for (i = 0; i < image->height; i++) {
			memcpy(newPtr, oldPtr, sliceRowBytes);
			oldPtr += rowBytes;
			newPtr += sliceRowBytes;
		    }
		    pixmap.baseAddr = newData;
		    pixmap.rowBytes = sliceRowBytes | 0x8000;
		    CopyBits((BitMap*) &pixmap, dstBit, srcPtr, dstPtr, srcCopy,
			    NULL);
		    if (slices) {
			pixmap.bounds.left = pixmap.bounds.right;
			dataPtr += sliceRowBytes;
		    }
		} while (slices--);
		ckfree(newData);
	    } else {
		pixmap.bounds.right = (short) image->width;
		pixmap.baseAddr = image->data + image->xoffset;
		pixmap.rowBytes = rowBytes | 0x8000;
		CopyBits((BitMap*) &pixmap, dstBit, srcPtr, dstPtr, srcCopy, NULL);
	    }
	}
    }
    TkMacOSXRestoreDrawingContext(&dc);
}

/*
 *----------------------------------------------------------------------
 *
 * XDrawLines --
 *
 *	Draw connected lines.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	Renders a series of connected lines.
 *
 *----------------------------------------------------------------------
 */

void
XDrawLines(
    Display *display,		/* Display. */
    Drawable d,			/* Draw on this. */
    GC gc,			/* Use this GC. */
    XPoint *points,		/* Array of points. */
    int npoints,		/* Number of points. */
    int mode)			/* Line drawing mode. */
{
    MacDrawable *macWin = (MacDrawable *) d;
    TkMacOSXDrawingContext dc;
    int i, lw = gc->line_width;

    if (npoints < 2) {
	/*
	 * TODO: generate BadValue error.
	 */

	return;
    }

    display->request++;
    if (!TkMacOSXSetupDrawingContext(d, gc, tkMacOSXUseCGDrawing, &dc)) {
	return;
    }
    if (dc.context) {
	double prevx, prevy;
	double o = (lw % 2) ? .5 : 0;

	CGContextBeginPath(dc.context);
	prevx = macWin->xOff + points[0].x + o;
	prevy = macWin->yOff + points[0].y + o;
	CGContextMoveToPoint(dc.context, prevx, prevy);
	for (i = 1; i < npoints; i++) {
	    if (mode == CoordModeOrigin) {
		CGContextAddLineToPoint(dc.context,
			macWin->xOff + points[i].x + o,
			macWin->yOff + points[i].y + o);
	    } else {
		prevx += points[i].x;
		prevy += points[i].y;
		CGContextAddLineToPoint(dc.context, prevx, prevy);
	    }
	}
	CGContextStrokePath(dc.context);
    } else {
	int o = -lw/2;

	/* This is broken for fat lines, it is not possible to correctly
	 * imitate X11 drawing of oblique fat lines with QD line drawing,
	 * we should draw a filled polygon instead. */

	MoveTo((short) (macWin->xOff + points[0].x + o),
	       (short) (macWin->yOff + points[0].y + o));
	for (i = 1; i < npoints; i++) {
	    if (mode == CoordModeOrigin) {
		LineTo((short) (macWin->xOff + points[i].x + o),
		       (short) (macWin->yOff + points[i].y + o));
	    } else {
		Line((short) points[i].x, (short) points[i].y);
	    }
	}
    }
    TkMacOSXRestoreDrawingContext(&dc);
}

/*
 *----------------------------------------------------------------------
 *
 * XDrawSegments --
 *
 *	Draw unconnected lines.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	Renders a series of unconnected lines.
 *
 *----------------------------------------------------------------------
 */

void
XDrawSegments(
    Display *display,
    Drawable d,
    GC gc,
    XSegment *segments,
    int nsegments)
{
    MacDrawable *macWin = (MacDrawable *) d;
    TkMacOSXDrawingContext dc;
    int i, lw = gc->line_width;

    display->request++;
    if (!TkMacOSXSetupDrawingContext(d, gc, tkMacOSXUseCGDrawing, &dc)) {
	return;
    }
    if (dc.context) {
	double o = (lw % 2) ? .5 : 0;

	for (i = 0; i < nsegments; i++) {
	    CGContextBeginPath(dc.context);
	    CGContextMoveToPoint(dc.context,
		    macWin->xOff + segments[i].x1 + o,
		    macWin->yOff + segments[i].y1 + o);
	    CGContextAddLineToPoint(dc.context,
		    macWin->xOff + segments[i].x2 + o,
		    macWin->yOff + segments[i].y2 + o);
	    CGContextStrokePath(dc.context);
	}
    } else {
	int o = -lw/2;

	/* This is broken for fat lines, it is not possible to correctly
	 * imitate X11 drawing of oblique fat lines with QD line drawing,
	 * we should draw a filled polygon instead. */

	for (i = 0; i < nsegments; i++) {
	    MoveTo((short) (macWin->xOff + segments[i].x1 + o),
		   (short) (macWin->yOff + segments[i].y1 + o));
	    LineTo((short) (macWin->xOff + segments[i].x2 + o),
		   (short) (macWin->yOff + segments[i].y2 + o));
	}
    }
    TkMacOSXRestoreDrawingContext(&dc);
}

/*
 *----------------------------------------------------------------------
 *
 * XFillPolygon --
 *
 *	Draws a filled polygon.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	Draws a filled polygon on the specified drawable.
 *
 *----------------------------------------------------------------------
 */

void
XFillPolygon(
    Display* display,		/* Display. */
    Drawable d,			/* Draw on this. */
    GC gc,			/* Use this GC. */
    XPoint* points,		/* Array of points. */
    int npoints,		/* Number of points. */
    int shape,			/* Shape to draw. */
    int mode)			/* Drawing mode. */
{
    MacDrawable *macWin = (MacDrawable *) d;
    TkMacOSXDrawingContext dc;
    int i;

    display->request++;
    if (!TkMacOSXSetupDrawingContext(d, gc, tkMacOSXUseCGDrawing, &dc)) {
	return;
    }
    if (dc.context) {
	double prevx, prevy;
	double o = (gc->line_width % 2) ? .5 : 0;

	CGContextBeginPath(dc.context);
	prevx = macWin->xOff + points[0].x + o;
	prevy = macWin->yOff + points[0].y + o;
	CGContextMoveToPoint(dc.context, prevx, prevy);
	for (i = 1; i < npoints; i++) {
	    if (mode == CoordModeOrigin) {
		CGContextAddLineToPoint(dc.context,
			macWin->xOff + points[i].x + o,
			macWin->yOff + points[i].y + o);
	    } else {
		prevx += points[i].x;
		prevy += points[i].y;
		CGContextAddLineToPoint(dc.context, prevx, prevy);
	    }
	}
	CGContextEOFillPath(dc.context);
    } else {
	PolyHandle polygon;

	polygon = OpenPoly();
	MoveTo((short) (macWin->xOff + points[0].x),
	       (short) (macWin->yOff + points[0].y));
	for (i = 1; i < npoints; i++) {
	    if (mode == CoordModeOrigin) {
		LineTo((short) (macWin->xOff + points[i].x),
		       (short) (macWin->yOff + points[i].y));
	    } else {
		Line((short) points[i].x, (short) points[i].y);
	    }
	}
	ClosePoly();
	FillCPoly(polygon, dc.penPat);
	KillPoly(polygon);
    }
    TkMacOSXRestoreDrawingContext(&dc);
}

/*
 *----------------------------------------------------------------------
 *
 * XDrawRectangle --
 *
 *	Draws a rectangle.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	Draws a rectangle on the specified drawable.
 *
 *----------------------------------------------------------------------
 */

void
XDrawRectangle(
    Display *display,		/* Display. */
    Drawable d,			/* Draw on this. */
    GC gc,			/* Use this GC. */
    int x, int y,		/* Upper left corner. */
    unsigned int width,		/* Width & height of rect. */
    unsigned int height)
{
    MacDrawable *macWin = (MacDrawable *) d;
    TkMacOSXDrawingContext dc;
    int lw = gc->line_width;

    if (width == 0 || height == 0) {
	return;
    }

    display->request++;
    if (!TkMacOSXSetupDrawingContext(d, gc, tkMacOSXUseCGDrawing, &dc)) {
	return;
    }
    if (dc.context) {
	CGRect rect;
	double o = (lw % 2) ? .5 : 0;

	rect = CGRectMake(
		macWin->xOff + x + o,
		macWin->yOff + y + o,
		width, height);
	CGContextStrokeRect(dc.context, rect);
    } else {
	Rect theRect;
	int o = -lw/2;

	theRect.left =	 (short) (macWin->xOff + x + o);
	theRect.top =	 (short) (macWin->yOff + y + o);
	theRect.right =	 (short) (theRect.left + width	+ lw);
	theRect.bottom = (short) (theRect.top  + height + lw);
	FrameRect(&theRect);
    }
    TkMacOSXRestoreDrawingContext(&dc);
}

#ifdef TK_MACOSXDRAW_UNUSED
/*
 *----------------------------------------------------------------------
 *
 * XDrawRectangles --
 *
 *	Draws the outlines of the specified rectangles as if a
 *	five-point PolyLine protocol request were specified for each
 *	rectangle:
 *
 *	    [x,y] [x+width,y] [x+width,y+height] [x,y+height] [x,y]
 *
 *	For the specified rectangles, these functions do not draw a
 *	pixel more than once. XDrawRectangles draws the rectangles in
 *	the order listed in the array. If rectangles intersect, the
 *	intersecting pixels are drawn multiple times. Draws a
 *	rectangle.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	Draws rectangles on the specified drawable.
 *
 *----------------------------------------------------------------------
 */

void
XDrawRectangles(
    Display *display,
    Drawable drawable,
    GC gc,
    XRectangle *rectArr,
    int nRects)
{
    MacDrawable *macWin = (MacDrawable *) drawable;
    TkMacOSXDrawingContext dc;
    XRectangle * rectPtr;
    int i, lw = gc->line_width;

    display->request++;
    if (!TkMacOSXSetupDrawingContext(d, gc, tkMacOSXUseCGDrawing, &dc)) {
	return;
    }
    if (dc.context) {
	CGRect rect;
	double o = (lw % 2) ? .5 : 0;

	for (i = 0, rectPtr = rectArr; i < nRects; i++, rectPtr++) {
	    if (rectPtr->width == 0 || rectPtr->height == 0) {
		continue;
	    }
	    rect = CGRectMake(
		    macWin->xOff + rectPtr->x + o,
		    macWin->yOff + rectPtr->y + o,
		    rectPtr->width, rectPtr->height);
	    CGContextStrokeRect(dc.context, rect);
	}
    } else {
	Rect theRect;
	int o = -lw/2;

	for (i = 0, rectPtr = rectArr; i < nRects;i++, rectPtr++) {
	    theRect.left =   (short) (macWin->xOff + rectPtr->x + o);
	    theRect.top =    (short) (macWin->yOff + rectPtr->y + o);
	    theRect.right =  (short) (theRect.left + rectPtr->width  + lw);
	    theRect.bottom = (short) (theRect.top  + rectPtr->height + lw);
	    FrameRect(&theRect);
	}
    }
    TkMacOSXRestoreDrawingContext(&dc);
}
#endif

/*
 *----------------------------------------------------------------------
 *
 * XFillRectangles --
 *
 *	Fill multiple rectangular areas in the given drawable.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	Draws onto the specified drawable.
 *
 *----------------------------------------------------------------------
 */

void
XFillRectangles(
    Display* display,		/* Display. */
    Drawable d,			/* Draw on this. */
    GC gc,			/* Use this GC. */
    XRectangle *rectangles,	/* Rectangle array. */
    int n_rectangles)		/* Number of rectangles. */
{
    MacDrawable *macWin = (MacDrawable *) d;
    TkMacOSXDrawingContext dc;
    XRectangle * rectPtr;
    int i;

    display->request++;
    if (!TkMacOSXSetupDrawingContext(d, gc, tkMacOSXUseCGDrawing, &dc)) {
	return;
    }
    if (dc.context) {
	CGRect rect;

	for (i = 0, rectPtr = rectangles; i < n_rectangles; i++, rectPtr++) {
	    if (rectPtr->width == 0 || rectPtr->height == 0) {
		continue;
	    }
	    rect = CGRectMake(
		    macWin->xOff + rectPtr->x,
		    macWin->yOff + rectPtr->y,
		    rectPtr->width, rectPtr->height);
	    CGContextFillRect(dc.context, rect);
	}
    } else {
	Rect theRect;

	for (i = 0, rectPtr = rectangles; i < n_rectangles; i++, rectPtr++) {
	    theRect.left =   (short) (macWin->xOff + rectPtr->x);
	    theRect.top =    (short) (macWin->yOff + rectPtr->y);
	    theRect.right =  (short) (theRect.left + rectPtr->width);
	    theRect.bottom = (short) (theRect.top  + rectPtr->height);
	    FillCRect(&theRect, dc.penPat);
	}
    }
    TkMacOSXRestoreDrawingContext(&dc);
}

/*
 *----------------------------------------------------------------------
 *
 * XDrawArc --
 *
 *	Draw an arc.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	Draws an arc on the specified drawable.
 *
 *----------------------------------------------------------------------
 */

void
XDrawArc(
    Display* display,		/* Display. */
    Drawable d,			/* Draw on this. */
    GC gc,			/* Use this GC. */
    int x, int y,		/* Upper left of bounding rect. */
    unsigned int width,		/* Width & height. */
    unsigned int height,
    int angle1,			/* Staring angle of arc. */
    int angle2)			/* Extent of arc. */
{
    MacDrawable *macWin = (MacDrawable *) d;
    TkMacOSXDrawingContext dc;
    int lw = gc->line_width;

    if (width == 0 || height == 0 || angle2 == 0) {
	return;
    }

    display->request++;
    if (!TkMacOSXSetupDrawingContext(d, gc, tkMacOSXUseCGDrawing, &dc)) {
	return;
    }
    if (dc.context) {
	CGRect rect;
	double o = (lw % 2) ? .5 : 0;

	rect = CGRectMake(
		macWin->xOff + x + o,
		macWin->yOff + y + o,
		width, height);
	TK_IF_MAC_OS_X_API_COND (4, CGContextStrokeEllipseInRect,
		angle1 == 0 && angle2 == 23040,
	    CGContextStrokeEllipseInRect(dc.context, rect);
	) TK_ELSE (
	    CGMutablePathRef p = CGPathCreateMutable();
	    CGAffineTransform t = CGAffineTransformIdentity;
	    CGPoint c = CGPointMake(CGRectGetMidX(rect), CGRectGetMidY(rect));
	    double w = CGRectGetWidth(rect);

	    if (width != height) {
		t = CGAffineTransformMakeScale(1.0, CGRectGetHeight(rect)/w);
		c = CGPointApplyAffineTransform(c, CGAffineTransformInvert(t));
	    }
	    CGPathAddArc(p, &t, c.x, c.y, w/2, radians(-angle1/64.0),
		    radians(-(angle1 + angle2)/64.0), angle2 > 0);
	    CGContextAddPath(dc.context, p);
	    CGPathRelease(p);
	    CGContextStrokePath(dc.context);
	) TK_ENDIF
    } else {
	Rect theRect;
	short start, extent;
	int o = -lw/2;

	theRect.left   = (short) (macWin->xOff + x + o);
	theRect.top    = (short) (macWin->yOff + y + o);
	theRect.right  = (short) (theRect.left + width + lw);
	theRect.bottom = (short) (theRect.top + height + lw);
	start  = (short) (90 - (angle1/64));
	extent = (short) (-(angle2/64));
	FrameArc(&theRect, start, extent);
    }
    TkMacOSXRestoreDrawingContext(&dc);
}

#ifdef TK_MACOSXDRAW_UNUSED
/*
 *----------------------------------------------------------------------
 *
 * XDrawArcs --
 *
 *	Draws multiple circular or elliptical arcs. Each arc is
 *	specified by a rectangle and two angles. The center of the
 *	circle or ellipse is the center of the rect- angle, and the
 *	major and minor axes are specified by the width and height.
 *	Positive angles indicate counterclock- wise motion, and
 *	negative angles indicate clockwise motion. If the magnitude
 *	of angle2 is greater than 360 degrees, XDrawArcs truncates it
 *	to 360 degrees.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	Draws an arc for each array element on the specified drawable.
 *
 *----------------------------------------------------------------------
 */

void
XDrawArcs(
    Display *display,
    Drawable d,
    GC gc,
    XArc *arcArr,
    int nArcs)
{

    MacDrawable *macWin = (MacDrawable *) d;
    TkMacOSXDrawingContext dc;
    XArc *arcPtr;
    int i, lw = gc->line_width;

    display->request++;
    if (!TkMacOSXSetupDrawingContext(d, gc, tkMacOSXUseCGDrawing, &dc)) {
	return;
    }
    if (dc.context) {
	CGRect rect;
	double o = (lw % 2) ? .5 : 0;

	for (i=0, arcPtr = arcArr; i < nArcs; i++, arcPtr++) {
	    if (arcPtr->width == 0 || arcPtr->height == 0
		    || arcPtr->angle2 == 0) {
		continue;
	    }
	    rect = CGRectMake(
		    macWin->xOff + arcPtr->x + o,
		    macWin->yOff + arcPtr->y + o,
		    arcPtr->width, arcPtr->height);

	    TK_IF_MAC_OS_X_API_COND (4, CGContextStrokeEllipseInRect,
		    arcPtr->angle1 == 0 && arcPtr->angle2 == 23040,
		CGContextStrokeEllipseInRect(dc.context, rect);
	    ) TK_ELSE (
		CGMutablePathRef p = CGPathCreateMutable();
		CGAffineTransform t = CGAffineTransformIdentity;
		CGPoint c = CGPointMake(CGRectGetMidX(rect),
			CGRectGetMidY(rect));
		double w = CGRectGetWidth(rect);

		if (arcPtr->width != arcPtr->height) {
		    t = CGAffineTransformMakeScale(1, CGRectGetHeight(rect)/w);
		    c = CGPointApplyAffineTransform(c,
			    CGAffineTransformInvert(t));
		}
		CGPathAddArc(p, &t, c.x, c.y, w/2,
			radians(-arcPtr->angle1/64.0),
			radians(-(arcPtr->angle1 + arcPtr->angle2)/64.0),
			arcPtr->angle2 > 0);
		CGContextAddPath(dc.context, p);
		CGPathRelease(p);
		CGContextStrokePath(dc.context);
	    ) TK_ENDIF
	}
    } else {
	Rect theRect;
	short start, extent;
	int o = -lw/2;

	for (i = 0, arcPtr = arcArr;i < nArcs;i++, arcPtr++) {
	    theRect.left =   (short) (macWin->xOff + arcPtr->x + o);
	    theRect.top =    (short) (macWin->yOff + arcPtr->y + o);
	    theRect.right =  (short) (theRect.left + arcPtr->width + lw);
	    theRect.bottom = (short) (theRect.top + arcPtr->height + lw);
	    start =  (short) (90 - (arcPtr->angle1/64));
	    extent = (short) (-(arcPtr->angle2/64));
	    FrameArc(&theRect, start, extent);
	}
    }
    TkMacOSXRestoreDrawingContext(&dc);
}
#endif

/*
 *----------------------------------------------------------------------
 *
 * XFillArc --
 *
 *	Draw a filled arc.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	Draws a filled arc on the specified drawable.
 *
 *----------------------------------------------------------------------
 */

void
XFillArc(
    Display* display,		/* Display. */
    Drawable d,			/* Draw on this. */
    GC gc,			/* Use this GC. */
    int x, int y,		/* Upper left of bounding rect. */
    unsigned int width,		/* Width & height. */
    unsigned int height,
    int angle1,			/* Staring angle of arc. */
    int angle2)			/* Extent of arc. */
{
    MacDrawable *macWin = (MacDrawable *) d;
    TkMacOSXDrawingContext dc;
    int lw = gc->line_width;

    if (width == 0 || height == 0 || angle2 == 0) {
	return;
    }

    display->request++;
    if (!TkMacOSXSetupDrawingContext(d, gc, tkMacOSXUseCGDrawing, &dc)) {
	return;
    }
    if (dc.context) {
	CGRect rect;
	double o = (lw % 2) ? .5 : 0, u = 0;

	if (notAA(lw)) {
	    o += NON_AA_CG_OFFSET/2;
	    u += NON_AA_CG_OFFSET;
	}
	rect = CGRectMake(
		macWin->xOff + x + o,
		macWin->yOff + y + o,
		width - u, height - u);

	TK_IF_MAC_OS_X_API_COND (4, CGContextFillEllipseInRect,
		angle1 == 0 && angle2 == 23040,
	    CGContextFillEllipseInRect(dc.context, rect);
	) TK_ELSE (
	    CGMutablePathRef p = CGPathCreateMutable();
	    CGAffineTransform t = CGAffineTransformIdentity;
	    CGPoint c = CGPointMake(CGRectGetMidX(rect), CGRectGetMidY(rect));
	    double w = CGRectGetWidth(rect);

	    if (width != height) {
		t = CGAffineTransformMakeScale(1, CGRectGetHeight(rect)/w);
		c = CGPointApplyAffineTransform(c, CGAffineTransformInvert(t));
	    }
	    if (gc->arc_mode == ArcPieSlice) {
		CGPathMoveToPoint(p, &t, c.x, c.y);
	    }
	    CGPathAddArc(p, &t, c.x, c.y, w/2, radians(-angle1/64.0),
		    radians(-(angle1 + angle2)/64.0), angle2 > 0);
	    CGPathCloseSubpath(p);
	    CGContextAddPath(dc.context, p);
	    CGPathRelease(p);
	    CGContextFillPath(dc.context);
	) TK_ENDIF
    } else {
	Rect theRect;
	short start, extent;
	int o = -lw/2;
	PolyHandle polygon;
	double sin1, cos1, sin2, cos2, angle;
	double boxWidth, boxHeight;
	double vertex[2], center1[2], center2[2];

	theRect.left =	 (short) (macWin->xOff + x + o);
	theRect.top =	 (short) (macWin->yOff + y + o);
	theRect.right =	 (short) (theRect.left + width + lw);
	theRect.bottom = (short) (theRect.top + height + lw);
	start = (short) (90 - (angle1/64));
	extent = (short) (-(angle2/64));
	if (gc->arc_mode == ArcChord) {
	    boxWidth = theRect.right - theRect.left;
	    boxHeight = theRect.bottom - theRect.top;
	    angle = radians(-angle1/64.0);
	    sin1 = sin(angle);
	    cos1 = cos(angle);
	    angle -= radians(angle2/64.0);
	    sin2 = sin(angle);
	    cos2 = cos(angle);
	    vertex[0] = (theRect.left + theRect.right)/2.0;
	    vertex[1] = (theRect.top + theRect.bottom)/2.0;
	    center1[0] = vertex[0] + cos1*boxWidth/2.0;
	    center1[1] = vertex[1] + sin1*boxHeight/2.0;
	    center2[0] = vertex[0] + cos2*boxWidth/2.0;
	    center2[1] = vertex[1] + sin2*boxHeight/2.0;

	    polygon = OpenPoly();
	    MoveTo((short) ((theRect.left + theRect.right)/2),
		   (short) ((theRect.top + theRect.bottom)/2));
	    LineTo((short) (center1[0] + .5), (short) (center1[1] + .5));
	    LineTo((short) (center2[0] + .5), (short) (center2[1] + .5));
	    ClosePoly();
	    FillCArc(&theRect, start, extent, dc.penPat);
	    FillCPoly(polygon, dc.penPat);
	    KillPoly(polygon);
	} else {
	    FillCArc(&theRect, start, extent, dc.penPat);
	}
    }
    TkMacOSXRestoreDrawingContext(&dc);
}

#ifdef TK_MACOSXDRAW_UNUSED
/*
 *----------------------------------------------------------------------
 *
 * XFillArcs --
 *
 *	Draw a filled arc.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	Draws a filled arc for each array element on the specified drawable.
 *
 *----------------------------------------------------------------------
 */

void
XFillArcs(
    Display *display,
    Drawable d,
    GC gc,
    XArc *arcArr,
    int nArcs)
{
    MacDrawable *macWin = (MacDrawable *) d;
    TkMacOSXDrawingContext dc;
    XArc * arcPtr;
    int i, lw = gc->line_width;

    display->request++;
    if (!TkMacOSXSetupDrawingContext(d, gc, tkMacOSXUseCGDrawing, &dc)) {
	return;
    }
    if (dc.context) {
	CGRect rect;
	double o = (lw % 2) ? .5 : 0, u = 0;

	if (notAA(lw)) {
	    o += NON_AA_CG_OFFSET/2;
	    u += NON_AA_CG_OFFSET;
	}
	for (i = 0, arcPtr = arcArr; i < nArcs; i++, arcPtr++) {
	    if (arcPtr->width == 0 || arcPtr->height == 0
		    || arcPtr->angle2 == 0) {
		continue;
	    }
	    rect = CGRectMake(
		    macWin->xOff + arcPtr->x + o,
		    macWin->yOff + arcPtr->y + o,
		    arcPtr->width - u, arcPtr->height - u);
	    TK_IF_MAC_OS_X_API_COND (4, CGContextFillEllipseInRect,
		    arcPtr->angle1 == 0 && arcPtr->angle2 == 23040,
		CGContextFillEllipseInRect(dc.context, rect);
	    ) TK_ELSE (
		CGMutablePathRef p = CGPathCreateMutable();
		CGAffineTransform t = CGAffineTransformIdentity;
		CGPoint c = CGPointMake(CGRectGetMidX(rect),
			CGRectGetMidY(rect));
		double w = CGRectGetWidth(rect);

		if (arcPtr->width != arcPtr->height) {
		    t = CGAffineTransformMakeScale(1, CGRectGetHeight(rect)/w);
		    c = CGPointApplyAffineTransform(c,
			    CGAffineTransformInvert(t));
		}
		if (gc->arc_mode == ArcPieSlice) {
		    CGPathMoveToPoint(p, &t, c.x, c.y);
		}
		CGPathAddArc(p, &t, c.x, c.y, w/2,
			radians(-arcPtr->angle1/64.0),
			radians(-(arcPtr->angle1 + arcPtr->angle2)/64.0),
			arcPtr->angle2 > 0);
		CGPathCloseSubpath(p);
		CGContextAddPath(dc.context, p);
		CGPathRelease(p);
		CGContextFillPath(dc.context);
	    ) TK_ENDIF
	}
    } else {
	Rect theRect;
	short start, extent;
	int o = -lw/2;
	PolyHandle polygon;
	double sin1, cos1, sin2, cos2, angle;
	double boxWidth, boxHeight;
	double vertex[2], center1[2], center2[2];

	for (i = 0, arcPtr = arcArr;i<nArcs;i++, arcPtr++) {
	    theRect.left =   (short) (macWin->xOff + arcPtr->x + o);
	    theRect.top =    (short) (macWin->yOff + arcPtr->y + o);
	    theRect.right =  (short) (theRect.left + arcPtr->width + lw);
	    theRect.bottom = (short) (theRect.top + arcPtr->height + lw);
	    start = (short) (90 - (arcPtr->angle1/64));
	    extent = (short) (- (arcPtr->angle2/64));

	    if (gc->arc_mode == ArcChord) {
		boxWidth = theRect.right - theRect.left;
		boxHeight = theRect.bottom - theRect.top;
		angle = radians(-arcPtr->angle1/64.0);
		sin1 = sin(angle);
		cos1 = cos(angle);
		angle -= radians(arcPtr->angle2/64.0);
		sin2 = sin(angle);
		cos2 = cos(angle);
		vertex[0] = (theRect.left + theRect.right)/2.0;
		vertex[1] = (theRect.top + theRect.bottom)/2.0;
		center1[0] = vertex[0] + cos1*boxWidth/2.0;
		center1[1] = vertex[1] + sin1*boxHeight/2.0;
		center2[0] = vertex[0] + cos2*boxWidth/2.0;
		center2[1] = vertex[1] + sin2*boxHeight/2.0;

		polygon = OpenPoly();
		MoveTo((short) ((theRect.left + theRect.right)/2),
		       (short) ((theRect.top + theRect.bottom)/2));
		LineTo((short) (center1[0] + .5), (short) (center1[1] + .5));
		LineTo((short) (center2[0] + .5), (short) (center2[1] + .5));
		ClosePoly();
		FillCArc(&theRect, start, extent, dc.penPat);
		FillCPoly(polygon, dc.penPat);
		KillPoly(polygon);
	    } else {
		FillCArc(&theRect, start, extent, dc.penPat);
	    }
	}
    }
    TkMacOSXRestoreDrawingContext(&dc);
}
#endif

#ifdef TK_MACOSXDRAW_UNUSED
/*
 *----------------------------------------------------------------------
 *
 * XMaxRequestSize --
 *
 *----------------------------------------------------------------------
 */

long
XMaxRequestSize(
    Display *display)
{
    return (SHRT_MAX / 4);
}
#endif

/*
 *----------------------------------------------------------------------
 *
 * TkScrollWindow --
 *
 *	Scroll a rectangle of the specified window and accumulate
 *	a damage region.
 *
 * Results:
 *	Returns 0 if the scroll genereated no additional damage.
 *	Otherwise, sets the region that needs to be repainted after
 *	scrolling and returns 1.
 *
 * Side effects:
 *	Scrolls the bits in the window.
 *
 *----------------------------------------------------------------------
 */

int
TkScrollWindow(
    Tk_Window tkwin,		/* The window to be scrolled. */
    GC gc,			/* GC for window to be scrolled. */
    int x, int y,		/* Position rectangle to be scrolled. */
    int width, int height,
    int dx, int dy,		/* Distance rectangle should be moved. */
    TkRegion damageRgn)		/* Region to accumulate damage in. */
{
    MacDrawable *destDraw = (MacDrawable *) Tk_WindowId(tkwin);
    CGrafPtr destPort, savePort;
    Boolean portChanged;
    Rect scrollRect;
    int result;
    HIShapeRef dmgRgn;

    /*
     * Due to the implementation below the behavior may be differnt
     * than X in certain cases that should never occur in Tk. The
     * scrollRect is the source rect extended by the offset (the union
     * of the source rect and the offset rect). Everything
     * in the extended scrollRect is scrolled. On X, it's possible
     * to "skip" over an area if the offset makes the source and
     * destination rects disjoint and non-aligned.
     */

    scrollRect.left	= destDraw->xOff + x;
    scrollRect.top	= destDraw->yOff + y;
    scrollRect.right	= scrollRect.left + width;
    scrollRect.bottom	= scrollRect.top + height;
    if (dx < 0) {
	scrollRect.left += dx;
    } else {
	scrollRect.right += dx;
    }
    if (dy < 0) {
	scrollRect.top += dy;
    } else {
	scrollRect.bottom += dy;
    }

    destPort = TkMacOSXGetDrawablePort(Tk_WindowId(tkwin));
    TkMacOSXSetUpClippingRgn(Tk_WindowId(tkwin));
    TkMacOSXCheckTmpQdRgnEmpty();
    portChanged = QDSwapPort(destPort, &savePort);
    ScrollRect(&scrollRect, dx, dy, tkMacOSXtmpQdRgn);
    if (portChanged) {
	QDSwapPort(savePort, NULL);
    }

    /*
     * Fortunately, the region returned by ScrollRect is semantically
     * the same as what we need to return in this function. If the
     * region is empty we return zero to denote that no damage was
     * created.
     */

    dmgRgn = HIShapeCreateWithQDRgn(tkMacOSXtmpQdRgn);
    SetEmptyRgn(tkMacOSXtmpQdRgn);
    TkMacOSXSetWithNativeRegion(damageRgn, dmgRgn);
    result = HIShapeIsEmpty(dmgRgn) ? 0 : 1;
    CFRelease(dmgRgn);

    return result;
}

/*
 *----------------------------------------------------------------------
 *
 * TkMacOSXSetUpGraphicsPort --
 *
 *	Set up the graphics port from the given GC.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	The current port is adjusted.
 *
 *----------------------------------------------------------------------
 */

void
TkMacOSXSetUpGraphicsPort(
    GC gc,			/* GC to apply to current port. */
    GWorldPtr destPort)
{
    CGrafPtr savePort;
    Boolean portChanged;

    portChanged = QDSwapPort(destPort, &savePort);
    PenNormal();
    if (gc) {
	if (!penPat) {
	    if (!tmpPixPat) {
		penPat = NewPixPat();
	    } else {
		penPat = tmpPixPat;
		tmpPixPat = NULL;
	    }
	}
	TkMacOSXSetColorInPort(gc->foreground, 1, penPat, destPort);
	PenPixPat(penPat);
	if(gc->function == GXxor) {
	    PenMode(patXor);
	}
	if (gc->line_width > 1) {
	    PenSize(gc->line_width, gc->line_width);
	}
	if (gc->line_style != LineSolid) {
	    /*
	     * FIXME: Here the dash pattern should be set in the drawing
	     * environment. This is not possible with QuickDraw line drawing.
	     */
	}
    }
    if (portChanged) {
	QDSwapPort(savePort, NULL);
    }
}

/*
 *----------------------------------------------------------------------
 *
 * TkMacOSXSetUpDrawingContext --
 *
 *	Set up a drawing context for the given drawable and GC.
 *
 * Results:
 *	Boolean indicating whether it is ok to draw; if false, drawing
 *	context was not setup, so do not attempt to draw and do not call
 *	TkMacOSXRestoreDrawingContext().
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */

int
TkMacOSXSetupDrawingContext(
    Drawable d,
    GC gc,
    int useCG, /* advisory only ! */
    TkMacOSXDrawingContext *dcPtr)
{
    MacDrawable *macDraw = ((MacDrawable*)d);
    int dontDraw = 0;
    TkMacOSXDrawingContext dc = {NULL, NULL, NULL, NULL, NULL, NULL, NULL,
	    {SHRT_MIN, SHRT_MIN, SHRT_MAX, SHRT_MAX}, false};

    if (tkPictureIsOpen) {
	if (useCG) {
	    TkMacOSXDbgMsg("Ignored CG Drawing with QD Picture open");
	    dontDraw = 1;
	}
    } else {
	dc.clipRgn = TkMacOSXGetClipRgn(d);
    }
    if (!dontDraw) {
	ClipToGC(d, gc, &dc.clipRgn);
	dontDraw = dc.clipRgn ? HIShapeIsEmpty(dc.clipRgn) : 0;
    }
    if (dontDraw) {
	if (dc.clipRgn) {
	    CFRelease(dc.clipRgn);
	    dc.clipRgn = NULL;
	}
	goto end;
    }
    if (useCG) {
	dc.context = macDraw->context;
    }
    if (!dc.context || !(macDraw->flags & TK_IS_PIXMAP)) {
	dc.port = TkMacOSXGetDrawablePort(d);
	if (dc.port) {
	    GetPortBounds(dc.port, &dc.portBounds);
	}
    }
    if (dc.context) {
	if (!dc.port) {
	    CGRect r;

	    TK_IF_MAC_OS_X_API (3, CGContextGetClipBoundingBox,
		r = CGContextGetClipBoundingBox(dc.context);
	    ) TK_ELSE_MAC_OS_X (3,
		r.origin = CGPointZero;
		r.size = macDraw->size;
	    ) TK_ENDIF
	    SetRect(&dc.portBounds, r.origin.x + macDraw->xOff,
		    r.origin.y + macDraw->yOff,
		    r.origin.x + r.size.width + macDraw->xOff,
		    r.origin.y + r.size.height + macDraw->yOff);
	}
	CGContextSaveGState(dc.context);
	dc.saveState = (void*)1;
	dc.port = NULL;
    } else if (dc.port) {
	dc.portChanged = QDSwapPort(dc.port, &dc.savePort);
	if (useCG && ChkErr(QDBeginCGContext, dc.port, &dc.context) == noErr) {
	    SyncCGContextOriginWithPort(dc.context, dc.port);
	} else {
	    dc.context = NULL;
	}
    } else {
	Tcl_Panic("TkMacOSXSetupDrawingContext(): "
		"no port or context to draw into !");
    }
    if (dc.context) {
	CGContextConcatCTM(dc.context, CGAffineTransformMake(1.0, 0.0, 0.0,
		-1.0, 0.0, dc.portBounds.bottom - dc.portBounds.top));
	if (dc.clipRgn) {
#ifdef TK_MAC_DEBUG_DRAWING
	    CGContextSaveGState(dc.context);
	    ChkErr(HIShapeReplacePathInCGContext, dc.clipRgn, dc.context);
	    CGContextSetRGBFillColor(dc.context, 1.0, 0.0, 0.0, 0.2);
	    CGContextEOFillPath(dc.context);
	    CGContextRestoreGState(dc.context);
#endif /* TK_MAC_DEBUG_DRAWING */
	    ChkErr(HIShapeReplacePathInCGContext, dc.clipRgn, dc.context);
	    CGContextEOClip(dc.context);
	}
	if (gc) {
	    static const CGLineCap cgCap[] = {
		[CapNotLast] = kCGLineCapButt, 
		[CapButt] = kCGLineCapButt, 
		[CapRound] = kCGLineCapRound, 
		[CapProjecting] = kCGLineCapSquare, 
	    };
	    static const CGLineJoin cgJoin[] = {
		[JoinMiter] = kCGLineJoinMiter, 
		[JoinRound] = kCGLineJoinRound, 
		[JoinBevel] = kCGLineJoinBevel, 
	    };
	    bool shouldAntialias;
	    double w = gc->line_width;

	    TkMacOSXSetColorInContext(gc->foreground, dc.context);
	    if (dc.port) {
		CGContextSetPatternPhase(dc.context, CGSizeMake(
			dc.portBounds.right - dc.portBounds.left,
			dc.portBounds.bottom - dc.portBounds.top));
	    }
	    if(gc->function != GXcopy) {
		TkMacOSXDbgMsg("Logical functions other than GXcopy are "
			"not supported for CG drawing!");
	    }
	    /* When should we antialias? */
	    shouldAntialias = !notAA(gc->line_width);
	    if (!shouldAntialias) {
		/* Make non-antialiased CG drawing look more like X11 */
		w -= (gc->line_width ? NON_AA_CG_OFFSET : 0);
	    }
	    CGContextSetShouldAntialias(dc.context, shouldAntialias);
	    CGContextSetLineWidth(dc.context, w);
	    if (gc->line_style != LineSolid) {
		int num = 0;
		char *p = &(gc->dashes);
		double dashOffset = gc->dash_offset;
		float lengths[10];

		while (p[num] != '\0' && num < 10) {
		    lengths[num] = p[num];
		    num++;
		}
		CGContextSetLineDash(dc.context, dashOffset, lengths, num);
	    }
	    if ((unsigned)gc->cap_style < sizeof(cgCap)/sizeof(CGLineCap)) {
		CGContextSetLineCap(dc.context,
			cgCap[(unsigned)gc->cap_style]);
	    }
	    if ((unsigned)gc->join_style < sizeof(cgJoin)/sizeof(CGLineJoin)) {
		CGContextSetLineJoin(dc.context,
			cgJoin[(unsigned)gc->join_style]);
	    }
	}
    } else if (dc.port) {
	PixPatHandle savePat = penPat;

	ChkErr(GetThemeDrawingState, &dc.saveState);
	penPat = NULL;
	TkMacOSXSetUpGraphicsPort(gc, dc.port);
	dc.penPat = penPat;
	penPat = savePat;
	dc.saveClip = NewRgn();
	GetPortClipRegion(dc.port, dc.saveClip);
	if (dc.clipRgn) {
	    ChkErr(HIShapeSetQDClip, dc.clipRgn, dc.port);
	} else {
	    NoQDClip(dc.port);
	}
	if (!tkPictureIsOpen) {
	    ShowPen();
	}
    }
end:
    *dcPtr = dc;
    return !dontDraw;
}

/*
 *----------------------------------------------------------------------
 *
 * TkMacOSXRestoreDrawingContext --
 *
 *	Restore drawing context.
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
TkMacOSXRestoreDrawingContext(
    TkMacOSXDrawingContext *dcPtr)
{
    if (dcPtr->context) {
	CGContextSynchronize(dcPtr->context);
	if (dcPtr->saveState) {
	    CGContextRestoreGState(dcPtr->context);
	}
	if (dcPtr->port) {
	    ChkErr(QDEndCGContext, dcPtr->port, &(dcPtr->context));
	}
    } else if (dcPtr->port) {
	if (!tkPictureIsOpen) {
	    HidePen();
	}
	PenNormal();
	if (dcPtr->saveClip) {
	    SetPortClipRegion(dcPtr->port, dcPtr->saveClip);
	    DisposeRgn(dcPtr->saveClip);
	}
	if (dcPtr->penPat) {
	    if (!tmpPixPat) {
		tmpPixPat = dcPtr->penPat;
	    } else {
		DisposePixPat(dcPtr->penPat);
	    }
	}
	if (dcPtr->saveState) {
	    ChkErr(SetThemeDrawingState, dcPtr->saveState, true);
	}
    }
    if (dcPtr->clipRgn) {
	CFRelease(dcPtr->clipRgn);
    }
    if (dcPtr->portChanged) {
	QDSwapPort(dcPtr->savePort, NULL);
    }
#ifdef TK_MAC_DEBUG
    bzero(dcPtr, sizeof(TkMacOSXDrawingContext));
#endif /* TK_MAC_DEBUG */
}

/*
 *----------------------------------------------------------------------
 *
 * TkMacOSXGetClipRgn --
 *
 *	Get the clipping region needed to restrict drawing to the given
 *	drawable.
 *
 * Results:
 *	Clipping region. If non-NULL, CFRelease it when done.
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */

HIShapeRef
TkMacOSXGetClipRgn(
    Drawable drawable)		/* Drawable. */
{
    MacDrawable *macDraw = (MacDrawable *) drawable;
    HIShapeRef clipRgn = NULL;
    CGRect r;

    if (macDraw->winPtr && macDraw->flags & TK_CLIP_INVALID) {
	TkMacOSXUpdateClipRgn(macDraw->winPtr);
#ifdef TK_MAC_DEBUG_DRAWING
	TkMacOSXDbgMsg("%s visRgn  ", macDraw->winPtr->pathName);
	TkMacOSXDebugFlashRegion(drawable, macDraw->visRgn);
#endif /* TK_MAC_DEBUG_DRAWING */
    }

    if (macDraw->flags & TK_CLIPPED_DRAW) {
	r = CGRectOffset(macDraw->drawRect, macDraw->xOff, macDraw->yOff);
    }
    if (macDraw->visRgn) {
	if (macDraw->flags & TK_CLIPPED_DRAW) {
	    HIShapeRef rgn = HIShapeCreateWithRect(&r);

	    clipRgn = HIShapeCreateIntersection(macDraw->visRgn, rgn);
	    CFRelease(rgn);
	} else {
	    clipRgn = HIShapeCreateCopy(macDraw->visRgn);
	}
    } else if (macDraw->flags & TK_CLIPPED_DRAW) {
	clipRgn = HIShapeCreateWithRect(&r);
    }
#ifdef TK_MAC_DEBUG_DRAWING
    TkMacOSXDbgMsg("%s clipRgn ", macDraw->winPtr->pathName);
    TkMacOSXDebugFlashRegion(drawable, clipRgn);
#endif /* TK_MAC_DEBUG_DRAWING */

    return clipRgn;
}

/*
 *----------------------------------------------------------------------
 *
 * TkMacOSXSetUpClippingRgn --
 *
 *	Set up the clipping region so that drawing only occurs on the
 *	specified X subwindow.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	The clipping region in the current port is changed.
 *
 *----------------------------------------------------------------------
 */

void
TkMacOSXSetUpClippingRgn(
    Drawable drawable)		/* Drawable to update. */
{
    CGrafPtr port = TkMacOSXGetDrawablePort(drawable);

    if (port) {
	HIShapeRef clipRgn = TkMacOSXGetClipRgn(drawable);

	if (clipRgn) {
	    ChkErr(HIShapeSetQDClip, clipRgn, port);
	    CFRelease(clipRgn);
	}
    }
}

/*
 *----------------------------------------------------------------------
 *
 * TkpClipDrawableToRect --
 *
 *	Clip all drawing into the drawable d to the given rectangle.
 *	If width and height are negative, reset to no clipping.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	Subsequent drawing into d is offset and clipped as specified.
 *
 *----------------------------------------------------------------------
 */

void
TkpClipDrawableToRect(
    Display *display,
    Drawable d,
    int x, int y,
    int width, int height)
{
    MacDrawable *macDraw = (MacDrawable *) d;

    if (width < 0 && height < 0) {
	macDraw->drawRect = CGRectNull;
	macDraw->flags &= ~TK_CLIPPED_DRAW;
    } else {
	macDraw->drawRect = CGRectMake(x, y, width, height);
	macDraw->flags |= TK_CLIPPED_DRAW;
    }
}

/*
 *----------------------------------------------------------------------
 *
 * ClipToGC --
 *
 *	Helper function to intersect given region with gc clip region.
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
ClipToGC(
    Drawable d,
    GC gc,
    HIShapeRef *clipRgnPtr) /* must point to initialized variable */
{
    if (gc && gc->clip_mask &&
	    ((TkpClipMask*)gc->clip_mask)->type == TKP_CLIP_REGION) {
	TkRegion gcClip = ((TkpClipMask*)gc->clip_mask)->value.region;
	int xOffset = ((MacDrawable *) d)->xOff + gc->clip_x_origin;
	int yOffset = ((MacDrawable *) d)->yOff + gc->clip_y_origin;
	HIShapeRef clipRgn = *clipRgnPtr, gcClipRgn;

	if (!tkPictureIsOpen) {
	    TkMacOSXOffsetRegion(gcClip, xOffset, yOffset);
	}
	gcClipRgn = TkMacOSXGetNativeRegion(gcClip);
	if (clipRgn) {
	    *clipRgnPtr = HIShapeCreateIntersection(gcClipRgn, clipRgn);
	    CFRelease(clipRgn);
	} else {
	    *clipRgnPtr = HIShapeCreateCopy(gcClipRgn);
	}
	CFRelease(gcClipRgn);
	if (!tkPictureIsOpen) {
	    TkMacOSXOffsetRegion(gcClip, -xOffset, -yOffset);
	}
    }
}

/*
 *----------------------------------------------------------------------
 *
 * NoQDClip --
 *
 *	Helper function to setup a QD port to not clip anything.
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
NoQDClip(
    CGrafPtr port)
{
    static RgnHandle noClipRgn = NULL;

    if (!noClipRgn) {
	noClipRgn = NewRgn();
	SetRectRgn(noClipRgn, SHRT_MIN, SHRT_MIN, SHRT_MAX, SHRT_MAX);
    }
    SetPortClipRegion(port, noClipRgn);
}

/*
 *----------------------------------------------------------------------
 *
 * TkMacOSXMakeStippleMap --
 *
 *	Given a drawable and a stipple pattern this function draws the
 *	pattern repeatedly over the drawable. The drawable can then
 *	be used as a mask for bit-bliting a stipple pattern over an
 *	object.
 *
 * Results:
 *	A BitMap data structure.
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */

BitMapPtr
TkMacOSXMakeStippleMap(
    Drawable drawable,		/* Window to apply stipple. */
    Drawable stipple)		/* The stipple pattern. */
{
    CGrafPtr stipplePort;
    BitMapPtr bitmapPtr;
    const BitMap *stippleBitmap;
    Rect portRect;
    int width, height, stippleHeight, stippleWidth, i, j;
    Rect bounds;

    GetPortBounds(TkMacOSXGetDrawablePort(drawable), &portRect);
    width = portRect.right - portRect.left;
    height = portRect.bottom - portRect.top;
    bitmapPtr = (BitMap *) ckalloc(sizeof(BitMap));
    bitmapPtr->bounds.top = bitmapPtr->bounds.left = 0;
    bitmapPtr->bounds.right = (short) width;
    bitmapPtr->bounds.bottom = (short) height;
    bitmapPtr->rowBytes = (width / 8) + 1;
    bitmapPtr->baseAddr = ckalloc(height * bitmapPtr->rowBytes);

    stipplePort = TkMacOSXGetDrawablePort(stipple);
    stippleBitmap = GetPortBitMapForCopyBits(stipplePort);
    GetPortBounds(stipplePort, &portRect);
    stippleWidth = portRect.right - portRect.left;
    stippleHeight = portRect.bottom - portRect.top;

    for (i = 0; i < height; i += stippleHeight) {
	for (j = 0; j < width; j += stippleWidth) {
	    bounds.left = j;
	    bounds.top = i;
	    bounds.right = j + stippleWidth;
	    bounds.bottom = i + stippleHeight;
	    CopyBits(stippleBitmap, bitmapPtr, &portRect, &bounds, srcCopy,
		    NULL);
	}
    }
    return bitmapPtr;
}

/*
 *----------------------------------------------------------------------
 *
 * TkpDrawHighlightBorder --
 *
 *	This procedure draws a rectangular ring around the outside of
 *	a widget to indicate that it has received the input focus.
 *
 *	On the Macintosh, this puts a 1 pixel border in the bgGC color
 *	between the widget and the focus ring, except in the case where
 *	highlightWidth is 1, in which case the border is left out.
 *
 *	For proper Mac L&F, use highlightWidth of 3.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	A rectangle "width" pixels wide is drawn in "drawable",
 *	corresponding to the outer area of "tkwin".
 *
 *----------------------------------------------------------------------
 */

void
TkpDrawHighlightBorder (
    Tk_Window tkwin,
    GC fgGC,
    GC bgGC,
    int highlightWidth,
    Drawable drawable)
{
    if (highlightWidth == 1) {
	TkDrawInsetFocusHighlight (tkwin, fgGC, highlightWidth, drawable, 0);
    } else {
	TkDrawInsetFocusHighlight (tkwin, bgGC, highlightWidth, drawable, 0);
	if (fgGC != bgGC) {
	    TkDrawInsetFocusHighlight (tkwin, fgGC, highlightWidth - 1,
		    drawable, 0);
	}
    }
}

/*
 *----------------------------------------------------------------------
 *
 * TkpDrawFrame --
 *
 *	This procedure draws the rectangular frame area. If the user
 *	has request themeing, it draws with a the background theme.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	Draws inside the tkwin area.
 *
 *----------------------------------------------------------------------
 */

void
TkpDrawFrame(
    Tk_Window tkwin,
    Tk_3DBorder border,
    int highlightWidth,
    int borderWidth,
    int relief)
{
    if (useThemedToplevel && Tk_IsTopLevel(tkwin)) {
	static Tk_3DBorder themedBorder = NULL;

	if (!themedBorder) {
	    themedBorder = Tk_Get3DBorder(NULL, tkwin,
		    "systemWindowHeaderBackground");
	}
	if (themedBorder) {
	    border = themedBorder;
	}
    }
    Tk_Fill3DRectangle(tkwin, Tk_WindowId(tkwin),
	    border, highlightWidth, highlightWidth,
	    Tk_Width(tkwin) - 2 * highlightWidth,
	    Tk_Height(tkwin) - 2 * highlightWidth,
	    borderWidth, relief);
}
