/*
 * tkUnixRFont.c --
 *
 *	Alternate implementation of tkUnixFont.c using Xft.
 *
 * Copyright (c) 2002-2003 Keith Packard
 *
 * See the file "license.terms" for information on usage and redistribution of
 * this file, and for a DISCLAIMER OF ALL WARRANTIES.
 *
 * RCS: @(#) $Id: tkUnixRFont.c,v 1.24 2008/03/12 16:35:27 jenglish Exp $
 */

#include "tkUnixInt.h"
#include "tkFont.h"
#include <X11/Xft/Xft.h>
#include <ctype.h>

typedef struct {
    XftFont *ftFont;
    FcPattern *source;
    FcCharSet *charset;
} UnixFtFace;

typedef struct {
    TkFont font;	    	/* Stuff used by generic font package. Must be
				 * first in structure. */
    UnixFtFace *faces;
    int nfaces;
    FcFontSet *fontset;
    FcPattern *pattern;

    Display *display;
    int screen;
    XftDraw *ftDraw;
    XftColor color;
} UnixFtFont;


/*
 * Package initialization:
 * 	Nothing to do here except register the fact that we're using Xft in
 * 	the TIP 59 configuration database.
 */

#ifndef TCL_CFGVAL_ENCODING
#define TCL_CFGVAL_ENCODING "ascii"
#endif

void
TkpFontPkgInit(
    TkMainInfo *mainPtr)	/* The application being created. */
{
    static Tcl_Config cfg[] = {
	{ "fontsystem", "xft" },
	{ 0,0 }
    };

    Tcl_RegisterConfig(mainPtr->interp, "tk", cfg, TCL_CFGVAL_ENCODING);
}

static XftFont *
GetFont(
    UnixFtFont *fontPtr,
    FcChar32 ucs4)
{
    int i;

    if (ucs4) {
	for (i = 0; i < fontPtr->nfaces; i++) {
	    FcCharSet *charset = fontPtr->faces[i].charset;
	    if (charset && FcCharSetHasChar(charset, ucs4)) {
		break;
	    }
	}
	if (i == fontPtr->nfaces) {
	    i = 0;
	}
    } else {
	i = 0;
    }
    if (!fontPtr->faces[i].ftFont) {
	FcPattern *pat = FcFontRenderPrepare(0,
	    fontPtr->pattern, fontPtr->faces[i].source);
	XftFont *ftFont = XftFontOpenPattern(fontPtr->display, pat);

	if (!ftFont) {
	    /*
	     * The previous call to XftFontOpenPattern() should not fail,
	     * but sometimes does anyway.  Usual cause appears to be
	     * a misconfigured fontconfig installation; see [Bug 1090382].
	     * Try a fallback:
	     */
	    ftFont = XftFontOpen(fontPtr->display, fontPtr->screen,
			FC_FAMILY, FcTypeString, "sans",
			FC_SIZE, FcTypeDouble, 12.0,
			NULL);
	}
	if (!ftFont) {
	    /*
	     * The previous call should definitely not fail.
	     * Impossible to proceed at this point.
	     */
	    Tcl_Panic("Cannot find a usable font.");
	}

	fontPtr->faces[i].ftFont = ftFont;
    }
    return fontPtr->faces[i].ftFont;
}

/*
 *---------------------------------------------------------------------------
 *
 * GetTkFontAttributes --
 * 	Fill in TkFontAttributes from an XftFont.
 */

static void
GetTkFontAttributes(
    XftFont *ftFont,
    TkFontAttributes *faPtr)
{
    char *family = "Unknown", **familyPtr = &family;
    int weight, slant, size, pxsize;
    double ptsize;

    (void)XftPatternGetString(ftFont->pattern, XFT_FAMILY, 0, familyPtr);
    if (XftPatternGetDouble(ftFont->pattern, XFT_SIZE, 0,
	    &ptsize) == XftResultMatch) {
	size = (int)ptsize;
    } else if (XftPatternGetInteger(ftFont->pattern, XFT_PIXEL_SIZE, 0,
	    &pxsize) == XftResultMatch) {
	size = -pxsize;
    } else {
	size = 12;
    }
    if (XftPatternGetInteger(ftFont->pattern, XFT_WEIGHT, 0,
	    &weight) != XftResultMatch) {
	weight = XFT_WEIGHT_MEDIUM;
    }
    if (XftPatternGetInteger(ftFont->pattern, XFT_SLANT, 0,
	    &slant) != XftResultMatch) {
	slant = XFT_SLANT_ROMAN;
    }

#if DEBUG_FONTSEL
    printf("family %s size %d weight %d slant %d\n",
	    family, size, weight, slant);
#endif /* DEBUG_FONTSEL */

    faPtr->family = Tk_GetUid(family);
    faPtr->size = size;
    faPtr->weight = (weight > XFT_WEIGHT_MEDIUM) ? TK_FW_BOLD : TK_FW_NORMAL;
    faPtr->slant = (slant > XFT_SLANT_ROMAN) ? TK_FS_ITALIC : TK_FS_ROMAN;
    faPtr->underline = 0;
    faPtr->overstrike = 0;
}

/*
 *---------------------------------------------------------------------------
 *
 * GetTkFontMetrics --
 * 	Fill in TkFontMetrics from an XftFont.
 */

static void GetTkFontMetrics(
    XftFont *ftFont,
    TkFontMetrics *fmPtr)
{
    int spacing;

    if (XftPatternGetInteger(ftFont->pattern, XFT_SPACING, 0,
	    &spacing) != XftResultMatch) {
	spacing = XFT_PROPORTIONAL;
    }

    fmPtr->ascent = ftFont->ascent;
    fmPtr->descent = ftFont->descent;
    fmPtr->maxWidth = ftFont->max_advance_width;
    fmPtr->fixed = spacing != XFT_PROPORTIONAL;
}

/*
 *---------------------------------------------------------------------------
 *
 * InitFont --
 *
 *	Initializes the fields of a UnixFtFont structure. If fontPtr is NULL,
 *	also allocates a new UnixFtFont.
 *
 * Results:
 * 	On error, frees fontPtr and returns NULL, otherwise returns fontPtr.
 *
 *---------------------------------------------------------------------------
 */

static UnixFtFont *
InitFont(
    Tk_Window tkwin,
    FcPattern *pattern,
    UnixFtFont *fontPtr)
{
    FcFontSet *set;
    FcCharSet *charset;
    FcResult result;
    XftFont *ftFont;
    int i;

    if (!fontPtr) {
	fontPtr = (UnixFtFont *) ckalloc(sizeof(UnixFtFont));
    }

    FcConfigSubstitute(0, pattern, FcMatchPattern);
    XftDefaultSubstitute(Tk_Display(tkwin), Tk_ScreenNumber(tkwin), pattern);

    /*
     * Generate the list of fonts
     */

    set = FcFontSort(0, pattern, FcTrue, NULL, &result);
    if (!set) {
	FcPatternDestroy(pattern);
	ckfree((char *)fontPtr);
	return NULL;
    }

    fontPtr->fontset = set;
    fontPtr->pattern = pattern;
    fontPtr->faces = (UnixFtFace *) ckalloc(set->nfont * sizeof(UnixFtFace));
    fontPtr->nfaces = set->nfont;

    /*
     * Fill in information about each returned font
     */

    for (i = 0; i < set->nfont; i++) {
	fontPtr->faces[i].ftFont = 0;
	fontPtr->faces[i].source = set->fonts[i];
	if (FcPatternGetCharSet(set->fonts[i], FC_CHARSET, 0,
		&charset) == FcResultMatch) {
	    fontPtr->faces[i].charset = FcCharSetCopy(charset);
	} else {
	    fontPtr->faces[i].charset = 0;
	}
    }

    fontPtr->display = Tk_Display(tkwin);
    fontPtr->screen = Tk_ScreenNumber(tkwin);
    fontPtr->ftDraw = 0;
    fontPtr->color.color.red = 0;
    fontPtr->color.color.green = 0;
    fontPtr->color.color.blue = 0;
    fontPtr->color.color.alpha = 0xffff;
    fontPtr->color.pixel = 0xffffffff;

    /*
     * Fill in platform-specific fields of TkFont.
     */
    ftFont = GetFont(fontPtr, 0);
    fontPtr->font.fid = XLoadFont(Tk_Display(tkwin), "fixed");
    GetTkFontAttributes(ftFont, &fontPtr->font.fa);
    GetTkFontMetrics(ftFont, &fontPtr->font.fm);

    return fontPtr;
}

static void
FinishedWithFont(
    UnixFtFont *fontPtr)
{
    Display *display = fontPtr->display;
    int i;
    Tk_ErrorHandler handler = Tk_CreateErrorHandler(display, -1, -1, -1, NULL,
	    (ClientData) NULL);

    for (i = 0; i < fontPtr->nfaces; i++) {
	if (fontPtr->faces[i].ftFont) {
	    XftFontClose(fontPtr->display, fontPtr->faces[i].ftFont);
	}
	if (fontPtr->faces[i].charset) {
	    FcCharSetDestroy(fontPtr->faces[i].charset);
	}
    }
    if (fontPtr->faces) {
	ckfree((char *)fontPtr->faces);
    }
    if (fontPtr->pattern) {
	FcPatternDestroy(fontPtr->pattern);
    }
    if (fontPtr->ftDraw) {
	XftDrawDestroy(fontPtr->ftDraw);
    }
    if (fontPtr->font.fid) {
	XUnloadFont(fontPtr->display, fontPtr->font.fid);
    }
    if (fontPtr->fontset) {
	FcFontSetDestroy(fontPtr->fontset);
    }
    Tk_DeleteErrorHandler(handler);
}

TkFont *
TkpGetNativeFont(
    Tk_Window tkwin,		/* For display where font will be used. */
    CONST char *name)		/* Platform-specific font name. */
{
    UnixFtFont *fontPtr;
    FcPattern *pattern;
#if DEBUG_FONTSEL
    printf("TkpGetNativeFont %s\n", name);
#endif /* DEBUG_FONTSEL */

    pattern = XftXlfdParse(name, FcFalse, FcFalse);
    if (!pattern) {
	return NULL;
    }

    /*
     * Should also try: pattern = FcNameParse(name); but generic/tkFont.c
     * expects TkpGetNativeFont() to only work on XLFD names under Unix.
     */

    fontPtr = InitFont(tkwin, pattern, NULL);
    if (!fontPtr) {
	return NULL;
    }
    return &fontPtr->font;
}

TkFont *
TkpGetFontFromAttributes(
    TkFont *tkFontPtr,		/* If non-NULL, store the information in this
				 * existing TkFont structure, rather than
				 * allocating a new structure to hold the
				 * font; the existing contents of the font
				 * will be released. If NULL, a new TkFont
				 * structure is allocated. */
    Tk_Window tkwin,		/* For display where font will be used. */
    CONST TkFontAttributes *faPtr)
				/* Set of attributes to match. */
{
    XftPattern *pattern;
    int weight, slant;
    UnixFtFont *fontPtr;

#if DEBUG_FONTSEL
    printf("TkpGetFontFromAttributes %s-%d %d %d\n", faPtr->family,
	    faPtr->size, faPtr->weight, faPtr->slant);
#endif /* DEBUG_FONTSEL */
    pattern = XftPatternCreate();
    if (faPtr->family) {
	XftPatternAddString(pattern, XFT_FAMILY, faPtr->family);
    }
    if (faPtr->size > 0) {
	XftPatternAddDouble(pattern, XFT_SIZE, (double)faPtr->size);
    } else if (faPtr->size < 0) {
	XftPatternAddInteger(pattern, XFT_PIXEL_SIZE, -faPtr->size);
    } else {
	XftPatternAddDouble(pattern, XFT_SIZE, 12.0);
    }
    switch (faPtr->weight) {
    case TK_FW_NORMAL:
    default:
	weight = XFT_WEIGHT_MEDIUM;
	break;
    case TK_FW_BOLD:
	weight = XFT_WEIGHT_BOLD;
	break;
    }
    XftPatternAddInteger(pattern, XFT_WEIGHT, weight);
    switch (faPtr->slant) {
    case TK_FS_ROMAN:
    default:
	slant = XFT_SLANT_ROMAN;
	break;
    case TK_FS_ITALIC:
	slant = XFT_SLANT_ITALIC;
	break;
    case TK_FS_OBLIQUE:
	slant = XFT_SLANT_OBLIQUE;
	break;
    }
    XftPatternAddInteger(pattern, XFT_SLANT, slant);

    fontPtr = (UnixFtFont *) tkFontPtr;
    if (fontPtr != NULL) {
	FinishedWithFont(fontPtr);
    }
    fontPtr = InitFont(tkwin, pattern, fontPtr);
    if (!fontPtr) {
	return NULL;
    }
    return &fontPtr->font;
}

void
TkpDeleteFont(
    TkFont *tkFontPtr)		/* Token of font to be deleted. */
{
    UnixFtFont *fontPtr = (UnixFtFont *) tkFontPtr;

    FinishedWithFont(fontPtr);
    /* XXX tkUnixFont.c doesn't free tkFontPtr... */
}

/*
 *---------------------------------------------------------------------------
 *
 * TkpGetFontFamilies --
 *
 *	Return information about the font families that are available on the
 *	display of the given window.
 *
 * Results:
 *	Modifies interp's result object to hold a list of all the available
 *	font families.
 *
 *---------------------------------------------------------------------------
 */

void
TkpGetFontFamilies(
    Tcl_Interp *interp,		/* Interp to hold result. */
    Tk_Window tkwin)		/* For display to query. */
{
    Tcl_Obj *resultPtr;
    XftFontSet *list;
    int i;

    resultPtr = Tcl_NewListObj(0, NULL);

    list = XftListFonts(Tk_Display(tkwin), Tk_ScreenNumber(tkwin),
		(char*)0,		/* pattern elements */
		XFT_FAMILY, (char*)0);	/* fields */
    for (i = 0; i < list->nfont; i++) {
	char *family, **familyPtr = &family;
	if (XftPatternGetString(list->fonts[i], XFT_FAMILY, 0, familyPtr)
		== XftResultMatch)
	{
	    Tcl_Obj *strPtr = Tcl_NewStringObj(family, -1);
	    Tcl_ListObjAppendElement(NULL, resultPtr, strPtr);
	}
    }
    XftFontSetDestroy(list);

    Tcl_SetObjResult(interp, resultPtr);
}

/*
 *-------------------------------------------------------------------------
 *
 * TkpGetSubFonts --
 *
 *	Called by [testfont subfonts] in the Tk testing package.
 *
 * Results:
 *	Sets interp's result to a list of the faces used by tkfont
 *
 *-------------------------------------------------------------------------
 */

void
TkpGetSubFonts(
    Tcl_Interp *interp,
    Tk_Font tkfont)
{
    Tcl_Obj *objv[3], *listPtr, *resultPtr;
    UnixFtFont *fontPtr = (UnixFtFont *) tkfont;
    FcPattern *pattern;
    char *family = "Unknown", **familyPtr = &family;
    char *foundry = "Unknown", **foundryPtr = &foundry;
    char *encoding = "Unknown", **encodingPtr = &encoding;
    int i;

    resultPtr = Tcl_NewListObj(0, NULL);

    for (i = 0; i < fontPtr->nfaces ; ++i) {
 	pattern = FcFontRenderPrepare(0, fontPtr->pattern,
		fontPtr->faces[i].source);

	XftPatternGetString(pattern, XFT_FAMILY, 0, familyPtr);
	XftPatternGetString(pattern, XFT_FOUNDRY, 0, foundryPtr);
	XftPatternGetString(pattern, XFT_ENCODING, 0, encodingPtr);
	objv[0] = Tcl_NewStringObj(family, -1);
	objv[1] = Tcl_NewStringObj(foundry, -1);
	objv[2] = Tcl_NewStringObj(encoding, -1);
	listPtr = Tcl_NewListObj(3, objv);
	Tcl_ListObjAppendElement(NULL, resultPtr, listPtr);
    }
    Tcl_SetObjResult(interp, resultPtr);
}

/*
 *----------------------------------------------------------------------
 *
 * TkpGetFontAttrsForChar --
 *
 *	Retrieve the font attributes of the actual font used to render a given
 *	character.
 *
 *----------------------------------------------------------------------
 */

void
TkpGetFontAttrsForChar(
    Tk_Window tkwin,		/* Window on the font's display */
    Tk_Font tkfont,		/* Font to query */
    Tcl_UniChar c,		/* Character of interest */
    TkFontAttributes *faPtr)	/* Output: Font attributes */
{
    UnixFtFont *fontPtr = (UnixFtFont *) tkfont;
				/* Structure describing the logical font */
    FcChar32 ucs4 = (FcChar32) c;
				/* UCS-4 character to map */
    XftFont *ftFont = GetFont(fontPtr, ucs4);
				/* Actual font used to render the character */

    GetTkFontAttributes(ftFont, faPtr);
    faPtr->underline = fontPtr->font.fa.underline;
    faPtr->overstrike = fontPtr->font.fa.overstrike;
}

int
Tk_MeasureChars(
    Tk_Font tkfont,		/* Font in which characters will be drawn. */
    CONST char *source,		/* UTF-8 string to be displayed. Need not be
				 * '\0' terminated. */
    int numBytes,		/* Maximum number of bytes to consider from
				 * source string. */
    int maxLength,		/* If >= 0, maxLength specifies the longest
				 * permissible line length in pixels; don't
				 * consider any character that would cross
				 * this x-position. If < 0, then line length
				 * is unbounded and the flags argument is
				 * ignored. */
    int flags,			/* Various flag bits OR-ed together:
				 * TK_PARTIAL_OK means include the last char
				 * which only partially fit on this line.
				 * TK_WHOLE_WORDS means stop on a word
				 * boundary, if possible. TK_AT_LEAST_ONE
				 * means return at least one character even if
				 * no characters fit. */
    int *lengthPtr)		/* Filled with x-location just after the
				 * terminating character. */
{
    UnixFtFont *fontPtr = (UnixFtFont *) tkfont;
    XftFont *ftFont;
    FcChar32 c;
    XGlyphInfo extents;
    int clen, curX, newX, curByte, newByte, sawNonSpace;
    int termByte = 0, termX = 0;
#if DEBUG_FONTSEL
    char string[256];
    int len = 0;
#endif /* DEBUG_FONTSEL */

    curX = 0;
    curByte = 0;
    sawNonSpace = 0;
    while (numBytes > 0) {
	Tcl_UniChar unichar;

	clen = Tcl_UtfToUniChar(source, &unichar);
	c = (FcChar32)unichar;

	if (clen <= 0) {
	    /*
	     * This can't happen (but see #1185640)
	     */

	    *lengthPtr = curX;
	    return curByte;
	}

	source += clen;
	numBytes -= clen;
	if (c < 256 && isspace(c)) {		/* I18N: ??? */
	    if (sawNonSpace) {
		termByte = curByte;
		termX = curX;
		sawNonSpace = 0;
	    }
	} else {
	    sawNonSpace = 1;
	}

#if DEBUG_FONTSEL
	string[len++] = (char) c;
#endif /* DEBUG_FONTSEL */
	ftFont = GetFont(fontPtr, c);

	XftTextExtents32(fontPtr->display, ftFont, &c, 1, &extents);

	newX = curX + extents.xOff;
	newByte = curByte + clen;
	if (maxLength >= 0 && newX > maxLength) {
	    if (flags & TK_PARTIAL_OK ||
		    (flags & TK_AT_LEAST_ONE && curByte == 0)) {
		curX = newX;
		curByte = newByte;
	    } else if (flags & TK_WHOLE_WORDS && termX != 0) {
		curX = termX;
		curByte = termByte;
	    }
	    break;
	}

	curX = newX;
	curByte = newByte;
    }
#if DEBUG_FONTSEL
    string[len] = '\0';
    printf("MeasureChars %s length %d bytes %d\n", string, curX, curByte);
#endif /* DEBUG_FONTSEL */
    *lengthPtr = curX;
    return curByte;
}

int
TkpMeasureCharsInContext(
    Tk_Font tkfont,
    CONST char *source,
    int numBytes,
    int rangeStart,
    int rangeLength,
    int maxLength,
    int flags,
    int *lengthPtr)
{
    (void) numBytes; /*unused*/

    return Tk_MeasureChars(tkfont, source + rangeStart, rangeLength,
	    maxLength, flags, lengthPtr);
}

#define NUM_SPEC    1024

void
Tk_DrawChars(
    Display *display,		/* Display on which to draw. */
    Drawable drawable,		/* Window or pixmap in which to draw. */
    GC gc,			/* Graphics context for drawing characters. */
    Tk_Font tkfont,		/* Font in which characters will be drawn;
				 * must be the same as font used in GC. */
    CONST char *source,		/* UTF-8 string to be displayed. Need not be
				 * '\0' terminated. All Tk meta-characters
				 * (tabs, control characters, and newlines)
				 * should be stripped out of the string that
				 * is passed to this function. If they are not
				 * stripped out, they will be displayed as
				 * regular printing characters. */
    int numBytes,		/* Number of bytes in string. */
    int x, int y)		/* Coordinates at which to place origin of
				 * string when drawing. */
{
    const int maxCoord = 0x7FFF;/* Xft coordinates are 16 bit values */
    UnixFtFont *fontPtr = (UnixFtFont *) tkfont;
    XGCValues values;
    XColor xcolor;
    int clen, nspec;
    XftGlyphFontSpec specs[NUM_SPEC];
    XGlyphInfo metrics;

    if (fontPtr->ftDraw == 0) {
#if DEBUG_FONTSEL
	printf("Switch to drawable 0x%x\n", drawable);
#endif /* DEBUG_FONTSEL */
	fontPtr->ftDraw = XftDrawCreate(display, drawable,
		DefaultVisual(display, fontPtr->screen),
		DefaultColormap(display, fontPtr->screen));
    } else {
	Tk_ErrorHandler handler = Tk_CreateErrorHandler(display, -1, -1, -1,
		NULL, (ClientData) NULL);

	XftDrawChange(fontPtr->ftDraw, drawable);
	Tk_DeleteErrorHandler(handler);
    }
    XGetGCValues(display, gc, GCForeground, &values);
    if (values.foreground != fontPtr->color.pixel) {
	xcolor.pixel = values.foreground;
	XQueryColor(display, DefaultColormap(display, fontPtr->screen),
		&xcolor);
	fontPtr->color.color.red = xcolor.red;
	fontPtr->color.color.green = xcolor.green;
	fontPtr->color.color.blue = xcolor.blue;
	fontPtr->color.color.alpha = 0xffff;
	fontPtr->color.pixel = values.foreground;
    }
    nspec = 0;
    while (numBytes > 0 && x <= maxCoord && y <= maxCoord) {
	XftFont *ftFont;
	FcChar32 c;

	clen = FcUtf8ToUcs4((FcChar8 *) source, &c, numBytes);
	if (clen <= 0) {
	    /*
	     * This should not happen, but it can.
	     */

	    return;
	}
	source += clen;
	numBytes -= clen;

	ftFont = GetFont(fontPtr, c);
	if (ftFont) {
	    specs[nspec].font = ftFont;
	    specs[nspec].glyph = XftCharIndex(fontPtr->display, ftFont, c);
	    specs[nspec].x = x;
	    specs[nspec].y = y;
	    XftGlyphExtents(fontPtr->display, ftFont, &specs[nspec].glyph, 1,
		    &metrics);
	    x += metrics.xOff;
	    y += metrics.yOff;
	    nspec++;
	    if (nspec == NUM_SPEC) {
		XftDrawGlyphFontSpec(fontPtr->ftDraw, &fontPtr->color,
			specs, nspec);
		nspec = 0;
	    }
	}
    }
    if (nspec) {
	XftDrawGlyphFontSpec(fontPtr->ftDraw, &fontPtr->color, specs, nspec);
    }
}
