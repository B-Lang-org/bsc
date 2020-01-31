/*
 * tkUtil.c --
 *
 *	This file contains miscellaneous utility functions that are used by
 *	the rest of Tk, such as a function for drawing a focus highlight.
 *
 * Copyright (c) 1994 The Regents of the University of California.
 * Copyright (c) 1994-1997 Sun Microsystems, Inc.
 *
 * See the file "license.terms" for information on usage and redistribution of
 * this file, and for a DISCLAIMER OF ALL WARRANTIES.
 *
 * RCS: @(#) $Id: tkUtil.c,v 1.21 2007/12/13 15:24:21 dgp Exp $
 */

#include "tkInt.h"

/*
 * The structure below defines the implementation of the "statekey" Tcl
 * object, used for quickly finding a mapping in a TkStateMap.
 */

Tcl_ObjType tkStateKeyObjType = {
    "statekey",			/* name */
    NULL,			/* freeIntRepProc */
    NULL,			/* dupIntRepProc */
    NULL,			/* updateStringProc */
    NULL			/* setFromAnyProc */
};

/*
 *--------------------------------------------------------------
 *
 * TkStateParseProc --
 *
 *	This function is invoked during option processing to handle the
 *	"-state" and "-default" options.
 *
 * Results:
 *	A standard Tcl return value.
 *
 * Side effects:
 *	The state for a given item gets replaced by the state indicated in the
 *	value argument.
 *
 *--------------------------------------------------------------
 */

int
TkStateParseProc(
    ClientData clientData,	/* some flags.*/
    Tcl_Interp *interp,		/* Used for reporting errors. */
    Tk_Window tkwin,		/* Window containing canvas widget. */
    const char *value,		/* Value of option. */
    char *widgRec,		/* Pointer to record for item. */
    int offset)			/* Offset into item. */
{
    int c;
    int flags = PTR2INT(clientData);
    size_t length;

    register Tk_State *statePtr = (Tk_State *) (widgRec + offset);

    if(value == NULL || *value == 0) {
	*statePtr = TK_STATE_NULL;
	return TCL_OK;
    }

    c = value[0];
    length = strlen(value);

    if ((c == 'n') && (strncmp(value, "normal", length) == 0)) {
	*statePtr = TK_STATE_NORMAL;
	return TCL_OK;
    }
    if ((c == 'd') && (strncmp(value, "disabled", length) == 0)) {
	*statePtr = TK_STATE_DISABLED;
	return TCL_OK;
    }
    if ((c == 'a') && (flags&1) && (strncmp(value, "active", length) == 0)) {
	*statePtr = TK_STATE_ACTIVE;
	return TCL_OK;
    }
    if ((c == 'h') && (flags&2) && (strncmp(value, "hidden", length) == 0)) {
	*statePtr = TK_STATE_HIDDEN;
	return TCL_OK;
    }

    Tcl_AppendResult(interp, "bad ", (flags&4)?"-default" : "state",
	    " value \"", value, "\": must be normal", NULL);
    if (flags&1) {
	Tcl_AppendResult(interp, ", active", NULL);
    }
    if (flags&2) {
	Tcl_AppendResult(interp, ", hidden", NULL);
    }
    if (flags&3) {
	Tcl_AppendResult(interp, ",", NULL);
    }
    Tcl_AppendResult(interp, " or disabled", NULL);
    *statePtr = TK_STATE_NORMAL;
    return TCL_ERROR;
}

/*
 *--------------------------------------------------------------
 *
 * TkStatePrintProc --
 *
 *	This function is invoked by the Tk configuration code to produce a
 *	printable string for the "-state" configuration option.
 *
 * Results:
 *	The return value is a string describing the state for the item
 *	referred to by "widgRec". In addition, *freeProcPtr is filled in with
 *	the address of a function to call to free the result string when it's
 *	no longer needed (or NULL to indicate that the string doesn't need to
 *	be freed).
 *
 * Side effects:
 *	None.
 *
 *--------------------------------------------------------------
 */

char *
TkStatePrintProc(
    ClientData clientData,	/* Ignored. */
    Tk_Window tkwin,		/* Window containing canvas widget. */
    char *widgRec,		/* Pointer to record for item. */
    int offset,			/* Offset into item. */
    Tcl_FreeProc **freeProcPtr)	/* Pointer to variable to fill in with
				 * information about how to reclaim storage
				 * for return string. */
{
    register Tk_State *statePtr = (Tk_State *) (widgRec + offset);

    switch (*statePtr) {
    case TK_STATE_NORMAL:
	return "normal";
    case TK_STATE_DISABLED:
	return "disabled";
    case TK_STATE_HIDDEN:
	return "hidden";
    case TK_STATE_ACTIVE:
	return "active";
    default:
	return "";
    }
}

/*
 *--------------------------------------------------------------
 *
 * TkOrientParseProc --
 *
 *	This function is invoked during option processing to handle the
 *	"-orient" option.
 *
 * Results:
 *	A standard Tcl return value.
 *
 * Side effects:
 *	The orientation for a given item gets replaced by the orientation
 *	indicated in the value argument.
 *
 *--------------------------------------------------------------
 */

int
TkOrientParseProc(
    ClientData clientData,	/* some flags.*/
    Tcl_Interp *interp,		/* Used for reporting errors. */
    Tk_Window tkwin,		/* Window containing canvas widget. */
    const char *value,		/* Value of option. */
    char *widgRec,		/* Pointer to record for item. */
    int offset)			/* Offset into item. */
{
    int c;
    size_t length;

    register int *orientPtr = (int *) (widgRec + offset);

    if(value == NULL || *value == 0) {
	*orientPtr = 0;
	return TCL_OK;
    }

    c = value[0];
    length = strlen(value);

    if ((c == 'h') && (strncmp(value, "horizontal", length) == 0)) {
	*orientPtr = 0;
	return TCL_OK;
    }
    if ((c == 'v') && (strncmp(value, "vertical", length) == 0)) {
	*orientPtr = 1;
	return TCL_OK;
    }
    Tcl_AppendResult(interp, "bad orientation \"", value,
	    "\": must be vertical or horizontal", NULL);
    *orientPtr = 0;
    return TCL_ERROR;
}

/*
 *--------------------------------------------------------------
 *
 * TkOrientPrintProc --
 *
 *	This function is invoked by the Tk configuration code to produce a
 *	printable string for the "-orient" configuration option.
 *
 * Results:
 *	The return value is a string describing the orientation for the item
 *	referred to by "widgRec". In addition, *freeProcPtr is filled in with
 *	the address of a function to call to free the result string when it's
 *	no longer needed (or NULL to indicate that the string doesn't need to
 *	be freed).
 *
 * Side effects:
 *	None.
 *
 *--------------------------------------------------------------
 */

char *
TkOrientPrintProc(
    ClientData clientData,	/* Ignored. */
    Tk_Window tkwin,		/* Window containing canvas widget. */
    char *widgRec,		/* Pointer to record for item. */
    int offset,			/* Offset into item. */
    Tcl_FreeProc **freeProcPtr)	/* Pointer to variable to fill in with
				 * information about how to reclaim storage
				 * for return string. */
{
    register int *statePtr = (int *) (widgRec + offset);

    if (*statePtr) {
	return "vertical";
    } else {
	return "horizontal";
    }
}

/*
 *----------------------------------------------------------------------
 *
 * TkOffsetParseProc --
 *
 *	Converts the offset of a stipple or tile into the Tk_TSOffset
 *	structure.
 *
 *----------------------------------------------------------------------
 */

int
TkOffsetParseProc(
    ClientData clientData,	/* not used */
    Tcl_Interp *interp,		/* Interpreter to send results back to */
    Tk_Window tkwin,		/* Window on same display as tile */
    const char *value,		/* Name of image */
    char *widgRec,		/* Widget structure record */
    int offset)			/* Offset of tile in record */
{
    Tk_TSOffset *offsetPtr = (Tk_TSOffset *) (widgRec + offset);
    Tk_TSOffset tsoffset;
    const char *q, *p;
    int result;

    if ((value == NULL) || (*value == 0)) {
	tsoffset.flags = TK_OFFSET_CENTER|TK_OFFSET_MIDDLE;
	goto goodTSOffset;
    }
    tsoffset.flags = 0;
    p = value;

    switch(value[0]) {
    case '#':
	if (PTR2INT(clientData) & TK_OFFSET_RELATIVE) {
	    tsoffset.flags = TK_OFFSET_RELATIVE;
	    p++;
	    break;
	}
	goto badTSOffset;
    case 'e':
	switch(value[1]) {
	case '\0':
	    tsoffset.flags = TK_OFFSET_RIGHT|TK_OFFSET_MIDDLE;
	    goto goodTSOffset;
	case 'n':
	    if (value[2]!='d' || value[3]!='\0') {
		goto badTSOffset;
	    }
	    tsoffset.flags = INT_MAX;
	    goto goodTSOffset;
	}
    case 'w':
	if (value[1] != '\0') {goto badTSOffset;}
	tsoffset.flags = TK_OFFSET_LEFT|TK_OFFSET_MIDDLE;
	goto goodTSOffset;
    case 'n':
	if ((value[1] != '\0') && (value[2] != '\0')) {
	    goto badTSOffset;
	}
	switch(value[1]) {
	case '\0':
	    tsoffset.flags = TK_OFFSET_CENTER|TK_OFFSET_TOP;
	    goto goodTSOffset;
	case 'w':
	    tsoffset.flags = TK_OFFSET_LEFT|TK_OFFSET_TOP;
	    goto goodTSOffset;
	case 'e':
	    tsoffset.flags = TK_OFFSET_RIGHT|TK_OFFSET_TOP;
	    goto goodTSOffset;
	}
	goto badTSOffset;
    case 's':
	if ((value[1] != '\0') && (value[2] != '\0')) {
	    goto badTSOffset;
	}
	switch(value[1]) {
	case '\0':
	    tsoffset.flags = TK_OFFSET_CENTER|TK_OFFSET_BOTTOM;
	    goto goodTSOffset;
	case 'w':
	    tsoffset.flags = TK_OFFSET_LEFT|TK_OFFSET_BOTTOM;
	    goto goodTSOffset;
	case 'e':
	    tsoffset.flags = TK_OFFSET_RIGHT|TK_OFFSET_BOTTOM;
	    goto goodTSOffset;
	}
	goto badTSOffset;
    case 'c':
	if (strncmp(value, "center", strlen(value)) != 0) {
	    goto badTSOffset;
	}
	tsoffset.flags = TK_OFFSET_CENTER|TK_OFFSET_MIDDLE;
	goto goodTSOffset;
    }
    if ((q = strchr(p,',')) == NULL) {
	if (PTR2INT(clientData) & TK_OFFSET_INDEX) {
	    if (Tcl_GetInt(interp, (char *) p, &tsoffset.flags) != TCL_OK) {
		Tcl_ResetResult(interp);
		goto badTSOffset;
	    }
	    tsoffset.flags |= TK_OFFSET_INDEX;
	    goto goodTSOffset;
	}
	goto badTSOffset;
    }
    *((char *) q) = 0;
    result = Tk_GetPixels(interp, tkwin, (char *) p, &tsoffset.xoffset);
    *((char *) q) = ',';
    if (result != TCL_OK) {
	return TCL_ERROR;
    }
    if (Tk_GetPixels(interp, tkwin, (char*)q+1, &tsoffset.yoffset) != TCL_OK) {
	return TCL_ERROR;
    }

  goodTSOffset:
    /*
     * Below is a hack to allow the stipple/tile offset to be stored in the
     * internal tile structure. Most of the times, offsetPtr is a pointer to
     * an already existing tile structure. However if this structure is not
     * already created, we must do it with Tk_GetTile()!!!!;
     */

    memcpy(offsetPtr, &tsoffset, sizeof(Tk_TSOffset));
    return TCL_OK;

  badTSOffset:
    Tcl_AppendResult(interp, "bad offset \"", value,
	    "\": expected \"x,y\"", NULL);
    if (PTR2INT(clientData) & TK_OFFSET_RELATIVE) {
	Tcl_AppendResult(interp, ", \"#x,y\"", NULL);
    }
    if (PTR2INT(clientData) & TK_OFFSET_INDEX) {
	Tcl_AppendResult(interp, ", <index>", NULL);
    }
    Tcl_AppendResult(interp, ", n, ne, e, se, s, sw, w, nw, or center", NULL);
    return TCL_ERROR;
}

/*
 *----------------------------------------------------------------------
 *
 * TkOffsetPrintProc --
 *
 *	Returns the offset of the tile.
 *
 * Results:
 *	The offset of the tile is returned.
 *
 *----------------------------------------------------------------------
 */

char *
TkOffsetPrintProc(
    ClientData clientData,	/* not used */
    Tk_Window tkwin,		/* not used */
    char *widgRec,		/* Widget structure record */
    int offset,			/* Offset of tile in record */
    Tcl_FreeProc **freeProcPtr)	/* not used */
{
    Tk_TSOffset *offsetPtr = (Tk_TSOffset *) (widgRec + offset);
    char *p, *q;

    if (offsetPtr->flags & TK_OFFSET_INDEX) {
	if (offsetPtr->flags >= INT_MAX) {
	    return "end";
	}
	p = (char *) ckalloc(32);
	sprintf(p, "%d", offsetPtr->flags & ~TK_OFFSET_INDEX);
	*freeProcPtr = TCL_DYNAMIC;
	return p;
    }
    if (offsetPtr->flags & TK_OFFSET_TOP) {
	if (offsetPtr->flags & TK_OFFSET_LEFT) {
	    return "nw";
	} else if (offsetPtr->flags & TK_OFFSET_CENTER) {
	    return "n";
	} else if (offsetPtr->flags & TK_OFFSET_RIGHT) {
	    return "ne";
	}
    } else if (offsetPtr->flags & TK_OFFSET_MIDDLE) {
	if (offsetPtr->flags & TK_OFFSET_LEFT) {
	    return "w";
	} else if (offsetPtr->flags & TK_OFFSET_CENTER) {
	    return "center";
	} else if (offsetPtr->flags & TK_OFFSET_RIGHT) {
	    return "e";
	}
    } else if (offsetPtr->flags & TK_OFFSET_BOTTOM) {
	if (offsetPtr->flags & TK_OFFSET_LEFT) {
	    return "sw";
	} else if (offsetPtr->flags & TK_OFFSET_CENTER) {
	    return "s";
	} else if (offsetPtr->flags & TK_OFFSET_RIGHT) {
	    return "se";
	}
    }
    q = p = (char *) ckalloc(32);
    if (offsetPtr->flags & TK_OFFSET_RELATIVE) {
	*q++ = '#';
    }
    sprintf(q, "%d,%d", offsetPtr->xoffset, offsetPtr->yoffset);
    *freeProcPtr = TCL_DYNAMIC;
    return p;
}

/*
 *----------------------------------------------------------------------
 *
 * TkPixelParseProc --
 *
 *	Converts the name of an image into a tile.
 *
 *----------------------------------------------------------------------
 */

int
TkPixelParseProc(
    ClientData clientData,	/* If non-NULL, negative values are allowed as
				 * well */
    Tcl_Interp *interp,		/* Interpreter to send results back to */
    Tk_Window tkwin,		/* Window on same display as tile */
    const char *value,		/* Name of image */
    char *widgRec,		/* Widget structure record */
    int offset)			/* Offset of tile in record */
{
    double *doublePtr = (double *) (widgRec + offset);
    int result;

    result = TkGetDoublePixels(interp, tkwin, value, doublePtr);

    if ((result == TCL_OK) && (clientData == NULL) && (*doublePtr < 0.0)) {
	Tcl_AppendResult(interp, "bad screen distance \"", value, "\"", NULL);
	return TCL_ERROR;
    }
    return result;
}

/*
 *----------------------------------------------------------------------
 *
 * TkPixelPrintProc --
 *
 *	Returns the name of the tile.
 *
 * Results:
 *	The name of the tile is returned.
 *
 *----------------------------------------------------------------------
 */

char *
TkPixelPrintProc(
    ClientData clientData,	/* not used */
    Tk_Window tkwin,		/* not used */
    char *widgRec,		/* Widget structure record */
    int offset,			/* Offset of tile in record */
    Tcl_FreeProc **freeProcPtr)	/* not used */
{
    double *doublePtr = (double *) (widgRec + offset);
    char *p = (char *) ckalloc(24);

    Tcl_PrintDouble(NULL, *doublePtr, p);
    *freeProcPtr = TCL_DYNAMIC;
    return p;
}

/*
 *----------------------------------------------------------------------
 *
 * TkDrawInsetFocusHighlight --
 *
 *	This function draws a rectangular ring around the outside of a widget
 *	to indicate that it has received the input focus. It takes an
 *	additional padding argument that specifies how much padding is present
 *	outside the widget.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	A rectangle "width" pixels wide is drawn in "drawable", corresponding
 *	to the outer area of "tkwin".
 *
 *----------------------------------------------------------------------
 */

void
TkDrawInsetFocusHighlight(
    Tk_Window tkwin,		/* Window whose focus highlight ring is to be
				 * drawn. */
    GC gc,			/* Graphics context to use for drawing the
				 * highlight ring. */
    int width,			/* Width of the highlight ring, in pixels. */
    Drawable drawable,		/* Where to draw the ring (typically a pixmap
				 * for double buffering). */
    int padding)		/* Width of padding outside of widget. */
{
    XRectangle rects[4];

    rects[0].x = padding;
    rects[0].y = padding;
    rects[0].width = Tk_Width(tkwin) - (2 * padding);
    rects[0].height = width;
    rects[1].x = padding;
    rects[1].y = Tk_Height(tkwin) - width - padding;
    rects[1].width = Tk_Width(tkwin) - (2 * padding);
    rects[1].height = width;
    rects[2].x = padding;
    rects[2].y = width + padding;
    rects[2].width = width;
    rects[2].height = Tk_Height(tkwin) - 2*width - 2*padding;
    rects[3].x = Tk_Width(tkwin) - width - padding;
    rects[3].y = rects[2].y;
    rects[3].width = width;
    rects[3].height = rects[2].height;
    XFillRectangles(Tk_Display(tkwin), drawable, gc, rects, 4);
}

/*
 *----------------------------------------------------------------------
 *
 * Tk_DrawFocusHighlight --
 *
 *	This function draws a rectangular ring around the outside of a widget
 *	to indicate that it has received the input focus.
 *
 *	This function is now deprecated. Use TkpDrawHighlightBorder instead,
 *	since this function does not handle drawing the Focus ring properly on
 *	the Macintosh - you need to know the background GC as well as the
 *	foreground since the Mac focus ring separated from the widget by a 1
 *	pixel border.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	A rectangle "width" pixels wide is drawn in "drawable", corresponding
 *	to the outer area of "tkwin".
 *
 *----------------------------------------------------------------------
 */

void
Tk_DrawFocusHighlight(
    Tk_Window tkwin,		/* Window whose focus highlight ring is to be
				 * drawn. */
    GC gc,			/* Graphics context to use for drawing the
				 * highlight ring. */
    int width,			/* Width of the highlight ring, in pixels. */
    Drawable drawable)		/* Where to draw the ring (typically a pixmap
				 * for double buffering). */
{
    TkDrawInsetFocusHighlight(tkwin, gc, width, drawable, 0);
}

/*
 *----------------------------------------------------------------------
 *
 * Tk_GetScrollInfo --
 *
 *	This function is invoked to parse "xview" and "yview" scrolling
 *	commands for widgets using the new scrolling command syntax ("moveto"
 *	or "scroll" options).
 *
 * Results:
 *	The return value is either TK_SCROLL_MOVETO, TK_SCROLL_PAGES,
 *	TK_SCROLL_UNITS, or TK_SCROLL_ERROR. This indicates whether the
 *	command was successfully parsed and what form the command took. If
 *	TK_SCROLL_MOVETO, *dblPtr is filled in with the desired position; if
 *	TK_SCROLL_PAGES or TK_SCROLL_UNITS, *intPtr is filled in with the
 *	number of lines to move (may be negative); if TK_SCROLL_ERROR, the
 *	interp's result contains an error message.
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */

int
Tk_GetScrollInfo(
    Tcl_Interp *interp,		/* Used for error reporting. */
    int argc,			/* # arguments for command. */
    const char **argv,		/* Arguments for command. */
    double *dblPtr,		/* Filled in with argument "moveto" option, if
				 * any. */
    int *intPtr)		/* Filled in with number of pages or lines to
				 * scroll, if any. */
{
    int c = argv[2][0];
    size_t length = strlen(argv[2]);

    if ((c == 'm') && (strncmp(argv[2], "moveto", length) == 0)) {
	if (argc != 4) {
	    Tcl_AppendResult(interp, "wrong # args: should be \"", argv[0],
		    " ", argv[1], " moveto fraction\"", NULL);
	    return TK_SCROLL_ERROR;
	}
	if (Tcl_GetDouble(interp, argv[3], dblPtr) != TCL_OK) {
	    return TK_SCROLL_ERROR;
	}
	return TK_SCROLL_MOVETO;
    } else if ((c == 's')
	    && (strncmp(argv[2], "scroll", length) == 0)) {
	if (argc != 5) {
	    Tcl_AppendResult(interp, "wrong # args: should be \"", argv[0],
		    " ", argv[1], " scroll number units|pages\"", NULL);
	    return TK_SCROLL_ERROR;
	}
	if (Tcl_GetInt(interp, argv[3], intPtr) != TCL_OK) {
	    return TK_SCROLL_ERROR;
	}
	length = strlen(argv[4]);
	c = argv[4][0];
	if ((c == 'p') && (strncmp(argv[4], "pages", length) == 0)) {
	    return TK_SCROLL_PAGES;
	} else if ((c == 'u') && (strncmp(argv[4], "units", length) == 0)) {
	    return TK_SCROLL_UNITS;
	}

	Tcl_AppendResult(interp, "bad argument \"", argv[4],
		"\": must be units or pages", NULL);
	return TK_SCROLL_ERROR;
    }
    Tcl_AppendResult(interp, "unknown option \"", argv[2],
	    "\": must be moveto or scroll", NULL);
    return TK_SCROLL_ERROR;
}

/*
 *----------------------------------------------------------------------
 *
 * Tk_GetScrollInfoObj --
 *
 *	This function is invoked to parse "xview" and "yview" scrolling
 *	commands for widgets using the new scrolling command syntax ("moveto"
 *	or "scroll" options).
 *
 * Results:
 *	The return value is either TK_SCROLL_MOVETO, TK_SCROLL_PAGES,
 *	TK_SCROLL_UNITS, or TK_SCROLL_ERROR. This indicates whether the
 *	command was successfully parsed and what form the command took. If
 *	TK_SCROLL_MOVETO, *dblPtr is filled in with the desired position; if
 *	TK_SCROLL_PAGES or TK_SCROLL_UNITS, *intPtr is filled in with the
 *	number of lines to move (may be negative); if TK_SCROLL_ERROR, the
 *	interp's result contains an error message.
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */

int
Tk_GetScrollInfoObj(
    Tcl_Interp *interp,		/* Used for error reporting. */
    int objc,			/* # arguments for command. */
    Tcl_Obj *const objv[],	/* Arguments for command. */
    double *dblPtr,		/* Filled in with argument "moveto" option, if
				 * any. */
    int *intPtr)		/* Filled in with number of pages or lines to
				 * scroll, if any. */
{
    int length;
    const char *arg;

    arg = Tcl_GetStringFromObj(objv[2], &length);

#define ArgPfxEq(str) ((arg[0]==str[0])&&!strncmp(arg,str,(unsigned)length))

    if (ArgPfxEq("moveto")) {
	if (objc != 4) {
	    Tcl_WrongNumArgs(interp, 2, objv, "moveto fraction");
	    return TK_SCROLL_ERROR;
	}
	if (Tcl_GetDoubleFromObj(interp, objv[3], dblPtr) != TCL_OK) {
	    return TK_SCROLL_ERROR;
	}
	return TK_SCROLL_MOVETO;
    } else if (ArgPfxEq("scroll")) {
	if (objc != 5) {
	    Tcl_WrongNumArgs(interp, 2, objv, "scroll number units|pages");
	    return TK_SCROLL_ERROR;
	}
	if (Tcl_GetIntFromObj(interp, objv[3], intPtr) != TCL_OK) {
	    return TK_SCROLL_ERROR;
	}

	arg = Tcl_GetStringFromObj(objv[4], &length);
	if (ArgPfxEq("pages")) {
	    return TK_SCROLL_PAGES;
	} else if (ArgPfxEq("units")) {
	    return TK_SCROLL_UNITS;
	}

	Tcl_AppendResult(interp, "bad argument \"", arg,
		"\": must be units or pages", NULL);
	return TK_SCROLL_ERROR;
    }
    Tcl_AppendResult(interp, "unknown option \"", arg,
	    "\": must be moveto or scroll", NULL);
    return TK_SCROLL_ERROR;
}

/*
 *---------------------------------------------------------------------------
 *
 * TkComputeAnchor --
 *
 *	Determine where to place a rectangle so that it will be properly
 *	anchored with respect to the given window. Used by widgets to align a
 *	box of text inside a window. When anchoring with respect to one of the
 *	sides, the rectangle be placed inside of the internal border of the
 *	window.
 *
 * Results:
 *	*xPtr and *yPtr set to the upper-left corner of the rectangle anchored
 *	in the window.
 *
 * Side effects:
 *	None.
 *
 *---------------------------------------------------------------------------
 */

void
TkComputeAnchor(
    Tk_Anchor anchor,		/* Desired anchor. */
    Tk_Window tkwin,		/* Anchored with respect to this window. */
    int padX, int padY,		/* Use this extra padding inside window, in
				 * addition to the internal border. */
    int innerWidth, int innerHeight,
				/* Size of rectangle to anchor in window. */
    int *xPtr, int *yPtr)	/* Returns upper-left corner of anchored
				 * rectangle. */
{
    /*
     * Handle the horizontal parts.
     */

    switch (anchor) {
    case TK_ANCHOR_NW:
    case TK_ANCHOR_W:
    case TK_ANCHOR_SW:
	*xPtr = Tk_InternalBorderLeft(tkwin) + padX;
	break;

    case TK_ANCHOR_N:
    case TK_ANCHOR_CENTER:
    case TK_ANCHOR_S:
	*xPtr = (Tk_Width(tkwin) - innerWidth - Tk_InternalBorderLeft(tkwin) -
		Tk_InternalBorderRight(tkwin)) / 2 +
		Tk_InternalBorderLeft(tkwin);
	break;

    default:
	*xPtr = Tk_Width(tkwin) - Tk_InternalBorderRight(tkwin) - padX
		- innerWidth;
	break;
    }

    /*
     * Handle the vertical parts.
     */

    switch (anchor) {
    case TK_ANCHOR_NW:
    case TK_ANCHOR_N:
    case TK_ANCHOR_NE:
	*yPtr = Tk_InternalBorderTop(tkwin) + padY;
	break;

    case TK_ANCHOR_W:
    case TK_ANCHOR_CENTER:
    case TK_ANCHOR_E:
	*yPtr = (Tk_Height(tkwin) - innerHeight- Tk_InternalBorderTop(tkwin) -
		Tk_InternalBorderBottom(tkwin)) / 2 +
		Tk_InternalBorderTop(tkwin);
	break;

    default:
	*yPtr = Tk_Height(tkwin) - Tk_InternalBorderBottom(tkwin) - padY
		- innerHeight;
	break;
    }
}

/*
 *---------------------------------------------------------------------------
 *
 * TkFindStateString --
 *
 *	Given a lookup table, map a number to a string in the table.
 *
 * Results:
 *	If numKey was equal to the numeric key of one of the elements in the
 *	table, returns the string key of that element. Returns NULL if numKey
 *	was not equal to any of the numeric keys in the table.
 *
 * Side effects.
 *	None.
 *
 *---------------------------------------------------------------------------
 */

char *
TkFindStateString(
    const TkStateMap *mapPtr,	/* The state table. */
    int numKey)			/* The key to try to find in the table. */
{
    for (; mapPtr->strKey!=NULL ; mapPtr++) {
	if (numKey == mapPtr->numKey) {
	    return (char *) mapPtr->strKey;
	}
    }
    return NULL;
}

/*
 *---------------------------------------------------------------------------
 *
 * TkFindStateNum, TkFindStateNumObj --
 *
 *	Given a lookup table, map a string to a number in the table.
 *
 * Results:
 *	If strKey was equal to the string keys of one of the elements in the
 *	table, returns the numeric key of that element. Returns the numKey
 *	associated with the last element (the NULL string one) in the table if
 *	strKey was not equal to any of the string keys in the table. In that
 *	case, an error message is also left in the interp's result (if interp
 *	is not NULL).
 *
 * Side effects.
 *	None.
 *
 *---------------------------------------------------------------------------
 */

int
TkFindStateNum(
    Tcl_Interp *interp,		/* Interp for error reporting. */
    const char *option,		/* String to use when constructing error. */
    const TkStateMap *mapPtr,	/* Lookup table. */
    const char *strKey)		/* String to try to find in lookup table. */
{
    const TkStateMap *mPtr;

    /*
     * See if the value is in the state map.
     */

    for (mPtr = mapPtr; mPtr->strKey != NULL; mPtr++) {
	if (strcmp(strKey, mPtr->strKey) == 0) {
	    return mPtr->numKey;
	}
    }

    /*
     * Not there. Generate an error message (if we can) and return the
     * default.
     */

    if (interp != NULL) {
	mPtr = mapPtr;
	Tcl_AppendResult(interp, "bad ", option, " value \"", strKey,
		"\": must be ", mPtr->strKey, NULL);
	for (mPtr++; mPtr->strKey != NULL; mPtr++) {
	    Tcl_AppendResult(interp,
		    ((mPtr[1].strKey != NULL) ? ", " : ", or "),
		    mPtr->strKey, NULL);
	}
    }
    return mPtr->numKey;
}

int
TkFindStateNumObj(
    Tcl_Interp *interp,		/* Interp for error reporting. */
    Tcl_Obj *optionPtr,		/* String to use when constructing error. */
    const TkStateMap *mapPtr,	/* Lookup table. */
    Tcl_Obj *keyPtr)		/* String key to find in lookup table. */
{
    const TkStateMap *mPtr;
    const char *key;
    const Tcl_ObjType *typePtr;

    /*
     * See if the value is in the object cache.
     */

    if ((keyPtr->typePtr == &tkStateKeyObjType)
	    && (keyPtr->internalRep.twoPtrValue.ptr1 == mapPtr)) {
	return PTR2INT(keyPtr->internalRep.twoPtrValue.ptr2);
    }

    /*
     * Not there. Look in the state map.
     */

    key = Tcl_GetStringFromObj(keyPtr, NULL);
    for (mPtr = mapPtr; mPtr->strKey != NULL; mPtr++) {
	if (strcmp(key, mPtr->strKey) == 0) {
	    typePtr = keyPtr->typePtr;
	    if ((typePtr != NULL) && (typePtr->freeIntRepProc != NULL)) {
		(*typePtr->freeIntRepProc)(keyPtr);
	    }
	    keyPtr->internalRep.twoPtrValue.ptr1 = (void *) mapPtr;
	    keyPtr->internalRep.twoPtrValue.ptr2 = INT2PTR(mPtr->numKey);
	    keyPtr->typePtr = &tkStateKeyObjType;
	    return mPtr->numKey;
	}
    }

    /*
     * Not there either. Generate an error message (if we can) and return the
     * default.
     */

    if (interp != NULL) {
	mPtr = mapPtr;
	Tcl_AppendResult(interp, "bad ", Tcl_GetString(optionPtr),
		" value \"", key, "\": must be ", mPtr->strKey, NULL);
	for (mPtr++; mPtr->strKey != NULL; mPtr++) {
	    Tcl_AppendResult(interp,
		((mPtr[1].strKey != NULL) ? ", " : ", or "),
		mPtr->strKey, NULL);
	}
    }
    return mPtr->numKey;
}

/*
 * Local Variables:
 * mode: c
 * c-basic-offset: 4
 * fill-column: 78
 * End:
 */
