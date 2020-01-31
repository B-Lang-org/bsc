/*
 * tkMacOSXFont.c --
 *
 *	Contains the Macintosh implementation of the platform-independant
 *	font package interface. This version uses ATSU instead of Quickdraw.
 *
 * Copyright 2002-2004 Benjamin Riefenstahl, Benjamin.Riefenstahl@epost.de
 * Copyright (c) 2006-2008 Daniel A. Steffen <das@users.sourceforge.net>
 *
 * Some functions were originally copied verbatim from the QuickDraw version
 * of tkMacOSXFont.c, which had these copyright notices:
 *
 * Copyright (c) 1990-1994 The Regents of the University of California.
 * Copyright (c) 1994-1997 Sun Microsystems, Inc.
 * Copyright 2001, Apple Computer, Inc.
 *
 * See the file "license.terms" for information on usage and redistribution
 * of this file, and for a DISCLAIMER OF ALL WARRANTIES.
 *
 * Todos:
 *
 * - Get away from Font Manager and Quickdraw functions as much as possible,
 *   replace with ATS functions instead.
 *
 * - Use Font Manager functions to translate ids from ATS to Font Manager
 *   instead of just assuming that they are the same.
 *
 * - Get a second font register going for fonts that are not assigned to a
 *   font family by the OS. On my system I have 27 fonts of that type,
 *   Hebrew, Arabic and Hindi fonts that actually come with the system.
 *   FMGetFontFamilyInstanceFromFont() returns -981 (kFMInvalidFontFamilyErr)
 *   for these and they are not listed when enumerating families, but they
 *   are when enumerating fonts directly. The problem that the OS sees may
 *   be that at least some of them do not contain any Latin characters. Note
 *   that such fonts can not be used for controls, because controls
 *   definitely require a family id (this assertion needs testing).
 *
 * RCS: @(#) $Id: tkMacOSXFont.c,v 1.37.2.1 2008/06/19 00:10:54 das Exp $
 */

#include "tkMacOSXPrivate.h"
#include "tkMacOSXFont.h"

/*
#ifdef TK_MAC_DEBUG
#define TK_MAC_DEBUG_FONTS
#endif
*/

/*
 * Problem: The sum of two parts is not the same as the whole. In particular
 * the width of two separately measured strings will usually be larger than
 * the width of them pasted together. Tk has a design bug here, because it
 * generally assumes that this kind of arithmetic works.
 * To workaround this, #define TK_MAC_COALESCE_LINE to 1 below, we then avoid
 * lines that tremble and shiver while the cursor passes through them by
 * undercutting the system and behind the scenes pasting strings together that
 * look like they are on the same line and adjacent and that are drawn with
 * the same font. To do this we need some global data.
 */
#define TK_MAC_COALESCE_LINE 0

/*
 * The following structure represents our Macintosh-specific implementation
 * of a font object.
 */

typedef struct {
    TkFont font;		/* Stuff used by generic font package. Must
				 * be first in structure. */

    /*
     * The ATSU view of the font and other text properties. Used for drawing
     * and measuring.
     */

    ATSUFontID atsuFontId;	/* == FMFont. */
    ATSUTextLayout atsuLayout;	/* ATSU layout object, representing the whole
				 * text that ATSU sees with some option
				 * bits. */
    ATSUStyle atsuStyle;	/* ATSU style object, representing a run of
				 * text with the same properties. */

    /*
     * The QuickDraw view of the font. Used to configure controls.
     */

    FMFontFamily qdFont;	/* == FMFontFamilyId, Carbon replacement for
				 * QD face numbers. */
    short qdSize;		/* Font size in points. */
    short qdStyle;		/* QuickDraw style bits. */
} MacFont;

/*
 * Information about font families, initialized at startup time. Font
 * families are described by a mapping from UTF-8 names to MacOS font family
 * IDs. The whole list is kept as the sorted array "familyList", allocated
 * with ckrealloc().
 *
 * Note: This would have been easier, if we could just have used Tcl hash
 * arrays. Unfortunately there seems to be no pre-packaged
 * non-case-sensitive version of that available.
 */

typedef struct {
    const char * name;
    FMFontFamily familyId;
} MacFontFamily;

static MacFontFamily * familyList = NULL;
static int
    familyListNextFree = 0,	/* The next free slot in familyList. */
    familyListMaxValid = 0,	/* The top of the sorted area. */
    familyListSize = 0;		/* The size of the whole array. */

/*
 * A simple one-shot sub-allocator for fast and efficient allocation of
 * strings. Used by the familyList array for the names. These strings are
 * only allocated once at startup and never freed. If you ever need to
 * re-initialize this, you can just ckfree() all the StringBlocks in the list
 * and start over.
 */

#define STRING_BLOCK_MAX (1024-8)	/* Make sizeof(StringBlock) ==
					 * 1024. */
typedef struct StringBlock {
    struct StringBlock *next;		/* Starting from "stringMemory" these
					 * blocks form a linked list. */
    int nextFree;			/* Top of the used area in the
					 * "strings" member. */
    char strings[STRING_BLOCK_MAX];	/* The actual memory managed here. */
} StringBlock;

static StringBlock *stringMemory = NULL;

#if TK_MAC_COALESCE_LINE
static Tcl_DString currentLine;	/* The current line as seen so far. This
				 * contains a Tcl_UniChar DString. */
static int
    currentY = -1,		/* The Y position (row in pixels) of the
				 * current line. */
    currentLeft = -1,		/* The left edge (pixels) of the current
				 * line. */
    currentRight = -1;		/* The right edge (pixels) of the current
				 * line. */
static const MacFont *currentFontPtr = NULL;
				/* The font of the current line. */
#endif /* TK_MAC_COALESCE_LINE */

static int antialiasedTextEnabled;

/*
 * The names for our "native" fonts.
 */

#define SYSTEMFONT_NAME		"system"
#define APPLFONT_NAME		"application"
#define MENUITEMFONT_NAME	"menu"

struct SystemFontMapEntry {
    const ThemeFontID id;
    const char *systemName;
    const char *tkName;
    const char *tkName1;
};

#define ThemeFont(n, ...) { kTheme##n##Font, "system" #n "Font", ##__VA_ARGS__ }
static const struct SystemFontMapEntry systemFontMap[] = {
    ThemeFont(System, 			"TkDefaultFont", "TkIconFont"),
    ThemeFont(EmphasizedSystem,		"TkCaptionFont"),
    ThemeFont(SmallSystem,		"TkHeadingFont", "TkTooltipFont"),
    ThemeFont(SmallEmphasizedSystem),
    ThemeFont(Application,		"TkTextFont"),
    ThemeFont(Label,			"TkSmallCaptionFont"),
    ThemeFont(Views),
    ThemeFont(MenuTitle),
    ThemeFont(MenuItem,			"TkMenuFont"),
    ThemeFont(MenuItemMark),
    ThemeFont(MenuItemCmdKey),
    ThemeFont(WindowTitle),
    ThemeFont(PushButton),
    ThemeFont(UtilityWindowTitle),
    ThemeFont(AlertHeader),
    ThemeFont(Toolbar),
    ThemeFont(MiniSystem),
    { kThemeSystemFontDetail,		"systemDetailSystemFont" },
    { kThemeSystemFontDetailEmphasized,	"systemDetailEmphasizedSystemFont" },
    { -1, NULL }
};
#undef ThemeFont

/*
 * Procedures used only in this file.
 */

static void LayoutSetString(const MacFont *fontPtr,
	const TkMacOSXDrawingContext *drawingContextPtr,
	const UniChar * uchars, int ulen);

/*
 * The actual workers.
 */

static int MeasureStringWidth(const MacFont *fontPtr, int start, int end);

#if TK_MAC_COALESCE_LINE
static const Tcl_UniChar *UpdateLineBuffer(const MacFont *fontPtr,
	const TkMacOSXDrawingContext *drawingContextPtr, const char *source,
	int numBytes, int x, int y, int * offset);
#endif /* TK_MAC_COALESCE_LINE */

/*
 * Initialization and setup of a font data structure.
 */

static const char *FamilyNameForFamilyID(FMFontFamily familyId);
static void InitFont(FMFontFamily familyId, const char *familyName,
	int size, int qdStyle, MacFont *fontPtr);
static void InitATSUObjects(FMFontFamily familyId, short qdsize, short qdStyle,
	ATSUFontID *fontIdPtr, ATSUTextLayout *layoutPtr, ATSUStyle *stylePtr);
static void InitATSUStyle(ATSUFontID fontId, short ptSize, short qdStyle,
	ATSUStyle style);
static void SetFontFeatures(ATSUFontID fontId, int fixed, ATSUStyle style);
static void AdjustFontHeight(MacFont *fontPtr);
static void InitATSULayout(const TkMacOSXDrawingContext *drawingContextPtr,
	ATSUTextLayout layout, int fixed);
static void ReleaseFont(MacFont *fontPtr);

/*
 * Finding fonts by name.
 */

static const MacFontFamily *FindFontFamilyOrAlias(const char *name);
static const MacFontFamily *FindFontFamilyOrAliasOrFallback(const char *name);

/*
 * Doing interesting things with font families and fonts.
 */

static void InitFontFamilies(void);
static OSStatus GetFontFamilyName(FMFontFamily fontFamily, char *name,
	int numBytes);

/*
 * Accessor functions and internal utilities for the font family list.
 */

static const MacFontFamily *AddFontFamily(const char *name,
	FMFontFamily familyId);
static const MacFontFamily *FindFontFamily(const char *name);
static Tcl_Obj *EnumFontFamilies(void);

static OSStatus FontFamilyEnumCallback(ATSFontFamilyRef family, void *refCon);
static void SortFontFamilies(void);
static int CompareFontFamilies(const void *vp1, const void *vp2);
static const char *AddString(const char *in);

static OSStatus GetThemeFontAndFamily(const ThemeFontID themeFontId,
	FMFontFamily *fontFamily, unsigned char *fontName, SInt16 *fontSize,
	Style *fontStyle);
static void InitSystemFonts(TkMainInfo *mainPtr);
static int CreateNamedSystemFont(Tcl_Interp *interp, Tk_Window tkwin,
	const char* name, TkFontAttributes *faPtr);


/*
 *-------------------------------------------------------------------------
 *
 * TkpFontPkgInit --
 *
 *	This procedure is called when an application is created. It
 *	initializes all the structures that are used by the
 *	platform-dependant code on a per application basis.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	Initialization of variables local to this file.
 *
 *-------------------------------------------------------------------------
 */

void
TkpFontPkgInit(
    TkMainInfo *mainPtr)	/* The application being created. */
{
    InitFontFamilies();
    InitSystemFonts(mainPtr);

#if TK_MAC_COALESCE_LINE
    Tcl_DStringInit(&currentLine);
#endif
}

/*
 *-------------------------------------------------------------------------
 *
 * InitSystemFonts --
 *
 *	Initialize named system fonts.
 *
 * Results:
 *
 *	None.
 *
 * Side effects:
 *
 *	None.
 *
 *-------------------------------------------------------------------------
 */

static void
InitSystemFonts(
    TkMainInfo *mainPtr)
{
    Tcl_Interp *interp = mainPtr->interp;
    Tk_Window tkwin = (Tk_Window) mainPtr->winPtr;
    const struct SystemFontMapEntry *systemFont = systemFontMap;
    TkFontAttributes fa;

    /* force this for now */
    if (!mainPtr->winPtr->mainPtr) {
	mainPtr->winPtr->mainPtr = mainPtr;
    }
    TkInitFontAttributes(&fa);
    while (systemFont->systemName) {
	Str255 fontName;
	SInt16 fontSize;
	Style  fontStyle;

	if (GetThemeFont(systemFont->id, smSystemScript, fontName,
		&fontSize, &fontStyle) == noErr) {
	    CopyPascalStringToC(fontName, (char*)fontName);
	    fa.family = Tk_GetUid((char*)fontName);
	    fa.size = fontSize;
	    fa.weight = (fontStyle & bold) ? TK_FW_BOLD : TK_FW_NORMAL;
	    fa.slant = (fontStyle & italic) ? TK_FS_ITALIC : TK_FS_ROMAN;
	    fa.underline = ((fontStyle & underline) != 0);
	    CreateNamedSystemFont(interp, tkwin, systemFont->systemName, &fa);
	    if (systemFont->tkName) {
		CreateNamedSystemFont(interp, tkwin, systemFont->tkName, &fa);
	    }
	    if (systemFont->tkName1) {
		CreateNamedSystemFont(interp, tkwin, systemFont->tkName1, &fa);
	    }
	}
	systemFont++;
    }
    fa.family = Tk_GetUid("monaco");
    fa.size = 11;
    fa.weight = TK_FW_NORMAL;
    fa.slant = TK_FS_ROMAN;
    fa.underline = 0;
    CreateNamedSystemFont(interp, tkwin, "TkFixedFont", &fa);
}

/*
 *-------------------------------------------------------------------------
 *
 * CreateNamedSystemFont --
 *
 *	Register a system font with the Tk named font mechanism.
 *
 * Results:
 *
 *	Result from TkCreateNamedFont().
 *
 * Side effects:
 *
 *	A new named font is added to the Tk font registry.
 *
 *-------------------------------------------------------------------------
 */

static int
CreateNamedSystemFont(
    Tcl_Interp *interp,
    Tk_Window tkwin,
    const char* name,
    TkFontAttributes *faPtr)
{
    TkDeleteNamedFont(NULL, tkwin, name);
    return TkCreateNamedFont(interp, tkwin, name, faPtr);
}

/*
 *---------------------------------------------------------------------------
 *
 * GetThemeFontAndFamily --
 *
 *	Wrapper around the GetThemeFont and FMGetFontFamilyFromName APIs.
 *
 *---------------------------------------------------------------------------
 */

OSStatus
GetThemeFontAndFamily(
    const ThemeFontID themeFontId,
    FMFontFamily* fontFamily,
    unsigned char *fontName,
    SInt16 *fontSize,
    Style *fontStyle)
{
    OSStatus err = ChkErr(GetThemeFont, themeFontId, smSystemScript, fontName,
	    fontSize, fontStyle);

    if (err == noErr) {
	*fontFamily = FMGetFontFamilyFromName(fontName);
	if (*fontFamily == kInvalidFontFamily) {
	    err = kFMInvalidFontFamilyErr;
	    TkMacOSXDbgMsg("FMGetFontFamilyFromName failed.");
	}
    }

    return err;
}

/*
 *---------------------------------------------------------------------------
 *
 * TkpGetNativeFont --
 *
 *	Map a platform-specific native font name to a TkFont.
 *
 * Results:
 *	The return value is a pointer to a TkFont that represents the
 *	native font. If a native font by the given name could not be
 *	found, the return value is NULL.
 *
 *	Every call to this procedure returns a new TkFont structure, even
 *	if the name has already been seen before. The caller should call
 *	TkpDeleteFont() when the font is no longer needed.
 *
 *	The caller is responsible for initializing the memory associated
 *	with the generic TkFont when this function returns and releasing
 *	the contents of the generics TkFont before calling TkpDeleteFont().
 *
 * Side effects:
 *	None.
 *
 *---------------------------------------------------------------------------
 */

TkFont *
TkpGetNativeFont(
    Tk_Window tkwin,		/* For display where font will be used. */
    const char *name)		/* Platform-specific font name. */
{
    ThemeFontID themeFontId;
    FMFontFamily fontFamily;
    Str255 fontName;
    SInt16 fontSize;
    Style  fontStyle;
    MacFont *fontPtr;

    if (strcmp(name, SYSTEMFONT_NAME) == 0) {
	themeFontId = kThemeSystemFont;
    } else if (strcmp(name, APPLFONT_NAME) == 0) {
	themeFontId = kThemeApplicationFont;
    } else if (strcmp(name, MENUITEMFONT_NAME) == 0) {
	themeFontId = kThemeMenuItemFont;
    } else {
	return NULL;
    }
    if (GetThemeFontAndFamily(themeFontId, &fontFamily, fontName, &fontSize,
	    &fontStyle) != noErr) {
	return NULL;
    }
    CopyPascalStringToC(fontName, (char*)fontName);

    fontPtr = (MacFont *) ckalloc(sizeof(MacFont));
    InitFont(fontFamily, (char*)fontName, fontSize, fontStyle, fontPtr);

    return (TkFont *) fontPtr;
}

/*
 *---------------------------------------------------------------------------
 *
 * TkpGetFontFromAttributes --
 *
 *	Given a desired set of attributes for a font, find a font with the
 *	closest matching attributes.
 *
 * Results:
 *	The return value is a pointer to a TkFont that represents the font
 *	with the desired attributes. If a font with the desired attributes
 *	could not be constructed, some other font will be substituted
 *	automatically.
 *
 *	Every call to this procedure returns a new TkFont structure, even
 *	if the specified attributes have already been seen before. The
 *	caller should call TkpDeleteFont() to free the platform- specific
 *	data when the font is no longer needed.
 *
 *	The caller is responsible for initializing the memory associated
 *	with the generic TkFont when this function returns and releasing
 *	the contents of the generic TkFont before calling TkpDeleteFont().
 *
 * Side effects:
 *	None.
 *
 *---------------------------------------------------------------------------
 */

TkFont *
TkpGetFontFromAttributes(
    TkFont *tkFontPtr,		/* If non-NULL, store the information in this
				 * existing TkFont structure, rather than
				 * allocating a new structure to hold the
				 * font; the existing contents of the font
				 * will be released. If NULL, a new TkFont
				 * structure is allocated. */
    Tk_Window tkwin,		/* For display where font will be used. */
    const TkFontAttributes *faPtr)
				/* Set of attributes to match. */
{
    short qdStyle;
    FMFontFamily familyId;
    const char *name;
    const MacFontFamily *familyPtr;
    MacFont *fontPtr;

    familyId = GetAppFont();
    name = NULL;
    qdStyle = 0;

    if (faPtr->family != NULL) {
	familyPtr = FindFontFamilyOrAliasOrFallback(faPtr->family);
	if (familyPtr != NULL) {
	    name = familyPtr->name;
	    familyId = familyPtr->familyId;
	}
    }

    if (faPtr->weight != TK_FW_NORMAL) {
	qdStyle |= bold;
    }
    if (faPtr->slant != TK_FS_ROMAN) {
	qdStyle |= italic;
    }
    if (faPtr->underline) {
	qdStyle |= underline;
    }
    if (tkFontPtr == NULL) {
	fontPtr = (MacFont *) ckalloc(sizeof(MacFont));
    } else {
	fontPtr = (MacFont *) tkFontPtr;
	ReleaseFont(fontPtr);
    }
    InitFont(familyId, name, TkFontGetPoints(tkwin, faPtr->size),
	    qdStyle, fontPtr);

    return (TkFont *) fontPtr;
}

/*
 *---------------------------------------------------------------------------
 *
 * TkpDeleteFont --
 *
 *	Called to release a font allocated by TkpGetNativeFont() or
 *	TkpGetFontFromAttributes(). The caller should have already
 *	released the fields of the TkFont that are used exclusively by the
 *	generic TkFont code.
 *
 * Results:
 *	TkFont is deallocated.
 *
 * Side effects:
 *	None.
 *
 *---------------------------------------------------------------------------
 */

void
TkpDeleteFont(
    TkFont *tkFontPtr)		/* Token of font to be deleted. */
{
    ReleaseFont((MacFont *) tkFontPtr);
}

/*
 *---------------------------------------------------------------------------
 *
 * TkpGetFontFamilies --
 *
 *	Return information about the font families that are available on
 *	the display of the given window.
 *
 * Results:
 *	Modifies interp's result object to hold a list of all the available
 *	font families.
 *
 * Side effects:
 *	None.
 *
 *---------------------------------------------------------------------------
 */

void
TkpGetFontFamilies(
    Tcl_Interp *interp,		/* Interp to hold result. */
    Tk_Window tkwin)		/* For display to query. */
{
    Tcl_SetObjResult(interp, EnumFontFamilies());
}

/*
 *-------------------------------------------------------------------------
 *
 * TkpGetSubFonts --
 *
 *	A function used by the testing package for querying the actual
 *	screen fonts that make up a font object.
 *
 * Results:
 *	Modifies interp's result object to hold a list containing the names
 *	of the screen fonts that make up the given font object.
 *
 * Side effects:
 *	None.
 *
 *-------------------------------------------------------------------------
 */

void
TkpGetSubFonts(
    Tcl_Interp *interp,		/* Interp to hold result. */
    Tk_Font tkfont)		/* Font object to query. */
{
    /* We don't know much about our fallback fonts, ATSU does all that for
     * us. We could use ATSUMatchFont to implement this function. But as
     * the information is only used for testing, such an effort seems not
     * very useful. */
}

/*
 *----------------------------------------------------------------------
 *
 * TkpGetFontAttrsForChar --
 *
 *	Retrieve the font attributes of the actual font used to render a
 *	given character.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	The font attributes are stored in *faPtr.
 *
 *----------------------------------------------------------------------
 */

void
TkpGetFontAttrsForChar(
    Tk_Window tkwin,		/* Window on the font's display */
    Tk_Font tkfont,		/* Font to query */
    Tcl_UniChar c,		/* Character of interest */
    TkFontAttributes* faPtr)	/* Output: Font attributes */
{
    const MacFont * fontPtr = (const MacFont *) tkfont;
    UniChar uchar = c;
    TkMacOSXDrawingContext drawingContext;
    OSStatus err;
    ATSUFontID fontId;
    UniCharArrayOffset changedOffset;
    UniCharCount changedLength;

    /*
     * Most of the attributes are just copied from the base font. This
     * assumes that all fonts can have all attributes.
     */

    *faPtr = fontPtr->font.fa;

    /*
     * But the name of the actual font may still differ, so we activate the
     * string as an ATSU layout and ask ATSU about the fallback.
     */
    if (!TkMacOSXSetupDrawingContext(Tk_WindowId(tkwin), NULL, 1,
	    &drawingContext)) {
	Tcl_Panic("TkpGetFontAttrsForChar: drawingContext not setup");
    }

    LayoutSetString(fontPtr, &drawingContext, &uchar, 1);

    fontId = fontPtr->atsuFontId;
    err = ATSUMatchFontsToText(
	fontPtr->atsuLayout, 0, 1,
	&fontId, &changedOffset, &changedLength);
    if (err != kATSUFontsMatched && err != noErr) {
	TkMacOSXDbgMsg("Can't match \\u%04X", (unsigned) c);
    }

    if (err == kATSUFontsMatched) {
	/*
	 * A fallback was used and the actual font is in fontId. Determine
	 * the name.
	 */

	FMFontFamily fontFamilyId;
	FMFontStyle fontStyle;
	int i;

	err = ChkErr(FMGetFontFamilyInstanceFromFont, fontId, &fontFamilyId,
		&fontStyle);
	if (err == noErr) {
	    /*
	     * Find the canonical name in our global list.
	     */

	    for (i=0; i<familyListMaxValid; ++i) {
		if (fontFamilyId == familyList[i].familyId) {
		    faPtr->family = familyList[i].name;
		    break;
		}
	    }
	    if (i >= familyListMaxValid) {
		TkMacOSXDbgMsg("Can't find font %d for \\u%04X", fontFamilyId,
			(unsigned) c);
	    }
	}
    }

    TkMacOSXRestoreDrawingContext(&drawingContext);
}

/*
 *---------------------------------------------------------------------------
 *
 * Tk_MeasureChars --
 *
 *	Determine the number of characters from the string that will fit in
 *	the given horizontal span. The measurement is done under the
 *	assumption that Tk_DrawChars() will be used to actually display the
 *	characters.
 *
 *	With ATSUI we need the line context to do this right, so we have the
 *	actual implementation in TkpMeasureCharsInContext().
 *
 * Results:
 *	The return value is the number of bytes from source that fit into the
 *	span that extends from 0 to maxLength. *lengthPtr is filled with the
 *	x-coordinate of the right edge of the last character that did fit.
 *
 * Side effects:
 *	None.
 *
 * Todo:
 *	Effects of the "flags" parameter are untested.
 *
 *---------------------------------------------------------------------------
 */

int
Tk_MeasureChars(
    Tk_Font tkfont,		/* Font in which characters will be drawn. */
    const char *source,		/* UTF-8 string to be displayed. Need not be
				 * '\0' terminated. */
    int numBytes,		/* Maximum number of bytes to consider from
				 * source string. */
    int maxLength,		/* If >= 0, maxLength specifies the longest
				 * permissible line length; don't consider any
				 * character that would cross this x-position.
				 * If < 0, then line length is unbounded and
				 * the flags argument is ignored. */
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
    return TkpMeasureCharsInContext(tkfont, source, numBytes, 0, numBytes,
	    maxLength, flags, lengthPtr);
}

/*
 *---------------------------------------------------------------------------
 *
 * TkpMeasureCharsInContext --
 *
 *	Determine the number of bytes from the string that will fit in the
 *	given horizontal span. The measurement is done under the assumption
 *	that TkpDrawCharsInContext() will be used to actually display the
 *	characters.
 *
 *	This one is almost the same as Tk_MeasureChars(), but with access to
 *	all the characters on the line for context.
 *
 * Results:
 *	The return value is the number of bytes from source that
 *	fit into the span that extends from 0 to maxLength. *lengthPtr is
 *	filled with the x-coordinate of the right edge of the last
 *	character that did fit.
 *
 * Side effects:
 *	None.
 *
 *---------------------------------------------------------------------------
 */

int
TkpMeasureCharsInContext(
    Tk_Font tkfont,		/* Font in which characters will be drawn. */
    const char * source,	/* UTF-8 string to be displayed. Need not be
				 * '\0' terminated. */
    int numBytes,		/* Maximum number of bytes to consider from
				 * source string in all. */
    int rangeStart,		/* Index of first byte to measure. */
    int rangeLength,		/* Length of range to measure in bytes. */
    int maxLength,		/* If >= 0, maxLength specifies the longest
				 * permissible line length; don't consider any
				 * character that would cross this x-position.
				 * If < 0, then line length is unbounded and
				 * the flags argument is ignored. */
    int flags,			/* Various flag bits OR-ed together:
				 * TK_PARTIAL_OK means include the last char
				 * which only partially fits on this line.
				 * TK_WHOLE_WORDS means stop on a word
				 * boundary, if possible. TK_AT_LEAST_ONE
				 * means return at least one character even
				 * if no characters fit.  If TK_WHOLE_WORDS
				 * and TK_AT_LEAST_ONE are set and the first
				 * word doesn't fit, we return at least one
				 * character or whatever characters fit into
				 * maxLength.  TK_ISOLATE_END means that the
				 * last character should not be considered in
				 * context with the rest of the string (used
				 * for breaking lines). */
    int *lengthPtr)		/* Filled with x-location just after the
				 * terminating character. */
{
    const MacFont *fontPtr = (const MacFont *) tkfont;
    int curX = -1, curByte = 0;
    UniChar *uchars;
    int ulen;
    UniCharArrayOffset urstart, urlen, urend;
    Tcl_DString ucharBuffer;
    int forceCharacterMode = 0;

    /*
     * Sanity checks.
     */

    if (rangeStart < 0 || (rangeStart+rangeLength) > numBytes) {
	TkMacOSXDbgMsg("Bad parameters");
	*lengthPtr = 0;
	return 0;
    }

    /*
     * Get simple no-brainers out of the way.
     */

    if (rangeLength == 0 || (maxLength == 0 && !(flags & TK_AT_LEAST_ONE))) {
	*lengthPtr = 0;
	return 0;
    }

    Tcl_DStringInit(&ucharBuffer);
    uchars = Tcl_UtfToUniCharDString(source, numBytes, &ucharBuffer);
    ulen = Tcl_DStringLength(&ucharBuffer) / sizeof(Tcl_UniChar);
    LayoutSetString(fontPtr, NULL, uchars, ulen);

    urstart = Tcl_NumUtfChars(source, rangeStart);
    urlen = Tcl_NumUtfChars(source+rangeStart,rangeLength);
    urend = urstart + urlen;

    if (maxLength < 0) {
	curX = MeasureStringWidth(fontPtr, urstart, urend);
	curByte = rangeLength;
    } else {
	UniCharArrayOffset offset = 0;
	OSStatus err;

	/*
	 * Have some upper limit on the size actually used.
	 */

	if (maxLength > 32767) {
	    maxLength = 32767;
	}

	offset = urstart;
	err = noErr;

	if (maxLength > 1) {
	    /*
	     * Let the system do some work by calculating a line break.
	     *
	     * Somehow ATSUBreakLine seems to assume that it needs at least
	     * one pixel padding. So we add one to the limit. Note also
	     * that ATSUBreakLine sometimes runs into an endless loop when
	     * the third parameter is equal or less than IntToFixed(2), so we
	     * need at least IntToFixed(3) (at least that's the current state
	     * of my knowledge).
	     */

	    err = ATSUBreakLine(fontPtr->atsuLayout, urstart,
		    IntToFixed(maxLength+1), false, /* !iUseAsSoftLineBreak */
		    &offset);

	    /*
	     * There is no way to signal an error from this routine, so we
	     * use predefined offset=urstart and otherwise ignore the
	     * possibility.
	     */

	    if ((err != noErr) && (err != kATSULineBreakInWord)) {
		TkMacOSXDbgMsg("ATSUBreakLine failed: %ld for '%.*s'", err,
			rangeLength, source+rangeStart);
	    }

#ifdef TK_MAC_DEBUG_FONTS
	    TkMacOSXDbgMsg("measure: '%.*s', break offset=%ld, errcode=%ld",
		    rangeLength, source+rangeStart, offset, err);
#endif

	    /*
	     * ATSUBreakLine includes the whitespace that separates words,
	     * but we don't want that. Besides, ATSUBreakLine thinks that
	     * spaces don't occupy pixels at the end of the break, which is
	     * also something we like to decide for ourself.
	     */

	    while ((offset > urstart) && (uchars[offset-1] == ' ')) {
		offset--;
	    }
	}

	/*
	 * Fix up left-overs for the TK_WHOLE_WORDS case.
	 */

	if (flags & TK_WHOLE_WORDS) {
	    if ((flags & TK_AT_LEAST_ONE) && ((offset == urstart)
		    || ((offset != urend) && (uchars[offset] != ' ')))) {
		/*
		 * With TK_AT_LEAST_ONE, if we are the the start of the
		 * range, we need to add at least one character.  If we are
		 * not at the end of a word, we must be in the middle of the
		 * first word still and we want to just use what we have so
		 * far.  In both cases we still need to find the right
		 * character boundary, so we set a flag that gets us into the
		 * code for character mode below.
		 */

		forceCharacterMode = 1;

	    } else {
		/*
		 * If we are not at the end of a word, we must be in the
		 * middle of the first word still.  Return 0.
		 */

		if ((offset != urend) && (uchars[offset] != ' ')) {
		    offset = urstart;
		    curX = 0;
		}
	    }
	}

	if (offset > urend) {
	    offset = urend;
	}

	/*
	 * If "flags" says that we don't actually want a word break, we need
	 * to find the next character break ourself, as ATSUBreakLine will
	 * only give us word breaks.  Do a simple linear search.
	 *
	 * Even do this, if ATSUBreakLine returned kATSULineBreakInWord,
	 * because we have not accounted correctly for all of the flags yet,
	 * like TK_AT_LEAST_ONE.
	 */

	if ((!(flags & TK_WHOLE_WORDS) || forceCharacterMode) && (offset <= urend)) {
	    UniCharArrayOffset lastOffset = offset;
	    UniCharArrayOffset nextoffset;
	    int lastX = -1;
	    int wantonemorechar = -1; /* undecided */

	    while (offset <= urend) {
		if (flags & TK_ISOLATE_END) {
		    LayoutSetString(fontPtr, NULL, uchars, offset);
		}
		curX = MeasureStringWidth(fontPtr, urstart, offset);

#ifdef TK_MAC_DEBUG_FONTS
		TkMacOSXDbgMsg("measure: '%.*s', try until=%ld, width=%d",
			rangeLength, source+rangeStart, offset, curX);
#endif

		if (curX > maxLength) {
		    /*
		     * Even if we are over the limit, we may want another
		     * character in some situations. Than we keep looking
		     * for one more character.
		     */

		    if (wantonemorechar == -1) {
			wantonemorechar = ((flags & TK_AT_LEAST_ONE) &&
				(lastOffset == urstart)) ||
				((flags & TK_PARTIAL_OK) &&
				(lastX != maxLength));
			if (!wantonemorechar) {
			    break;
			}
			lastX = curX;
		    }

		    /*
		     * There may belong combining marks to this character.
		     * Wait for a new curX to collect them all.
		     */

		    if (lastX != curX) {
			break;
		    }
		}

		/*
		 * Save this position, so we can come back to it.
		 */

		lastX = curX;
		lastOffset = offset;

		/*
		 * Increment offset by one character, taking combining marks
		 * into account.
		 */

		if (offset >= urend) {
		    break;
		}
		nextoffset = 0;
		if (flags & TK_ISOLATE_END) {
		    LayoutSetString(fontPtr, NULL, uchars, ulen);
		}
		err = ChkErr(ATSUNextCursorPosition, fontPtr->atsuLayout,
			offset, kATSUByCluster, &nextoffset);
		if (err != noErr) {
		    break;
		}
		if (nextoffset <= offset) {
#ifdef TK_MAC_DEBUG_FONTS
		    TkMacOSXDbgMsg("ATSUNextCursorPosition: Can't move further"
			    " (shouldn't happen, bad data?)");
#endif
		    break;
		}

		offset = nextoffset;
	    }

	    /*
	     * We have overshot one character, so backup one position.
	     */

	    curX = lastX;
	    offset = lastOffset;
	}

	if (curX < 0) {
	    if (flags & TK_ISOLATE_END) {
		LayoutSetString(fontPtr, NULL, uchars, offset);
	    }
	    curX = MeasureStringWidth(fontPtr, urstart, offset);
	}

	curByte = Tcl_UtfAtIndex(source, offset) - source;
	curByte -= rangeStart;
    }

    Tcl_DStringFree(&ucharBuffer);

#ifdef TK_MAC_DEBUG_FONTS
    TkMacOSXDbgMsg("measure: '%.*s', maxLength=%d, flags=%s%s%s%s "
	    "-> width=%d, bytes=%d",
	    rangeLength, source+rangeStart, maxLength,
	    flags & TK_PARTIAL_OK   ? "partialOk "  : "",
	    flags & TK_WHOLE_WORDS  ? "wholeWords " : "",
	    flags & TK_AT_LEAST_ONE ? "atLeastOne " : "",
	    flags & TK_ISOLATE_END  ? "isolateEnd " : "",
	    curX, curByte);
#endif

    *lengthPtr = curX;
    return curByte;
}

/*
 *---------------------------------------------------------------------------
 *
 * Tk_DrawChars --
 *
 *	Draw a string of characters on the screen.
 *
 *	With ATSUI we need the line context to do this right, so we have the
 *	actual implementation in TkpDrawCharsInContext().
 *
 * Results:
  *	None.
 *
 * Side effects:
 *	Information gets drawn on the screen.
 *
 *---------------------------------------------------------------------------
 */

void
Tk_DrawChars(
    Display *display,		/* Display on which to draw. */
    Drawable drawable,		/* Window or pixmap in which to draw. */
    GC gc,			/* Graphics context for drawing characters. */
    Tk_Font tkfont,		/* Font in which characters will be drawn; must
				 * be the same as font used in GC. */
    const char *source,		/* UTF-8 string to be displayed. Need not be
				 * '\0' terminated. All Tk meta-characters
				 * (tabs, control characters, and newlines)
				 * should be stripped out of the string that
				 * is passed to this function. If they are not
				 * stripped out, they will be displayed as
				 * regular printing characters. */
    int numBytes,		/* Number of bytes in string. */
    int x, int y)		/* Coordinates at which to place origin of the
				 * string when drawing. */
{
    TkpDrawCharsInContext(display, drawable, gc, tkfont, source, numBytes,
	    0, numBytes, x, y);
}

/*
 *---------------------------------------------------------------------------
 *
 * TkpDrawCharsInContext --
 *
 *	Draw a string of characters on the screen like Tk_DrawChars(), with
 *	access to all the characters on the line for context.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	Information gets drawn on the screen.
 *
 * Todo:
 *	Stippled text drawing.
 *
 *---------------------------------------------------------------------------
 */

void
TkpDrawCharsInContext(
    Display *display,		/* Display on which to draw. */
    Drawable drawable,		/* Window or pixmap in which to draw. */
    GC gc,			/* Graphics context for drawing characters. */
    Tk_Font tkfont,		/* Font in which characters will be drawn; must
				 * be the same as font used in GC. */
    const char * source,	/* UTF-8 string to be displayed. Need not be
				 * '\0' terminated. All Tk meta-characters
				 * (tabs, control characters, and newlines)
				 * should be stripped out of the string that
				 * is passed to this function. If they are not
				 * stripped out, they will be displayed as
				 * regular printing characters. */
    int numBytes,		/* Number of bytes in string. */
    int rangeStart,		/* Index of first byte to draw. */
    int rangeLength,		/* Length of range to draw in bytes. */
    int x, int y)		/* Coordinates at which to place origin of the
				 * whole (not just the range) string when
				 * drawing. */
{
    const MacFont * fontPtr = (const MacFont *) tkfont;
    MacDrawable *macWin = (MacDrawable *) drawable;
    Fixed fx, fy;
    int ulen, urstart, urlen;
    const UniChar * uchars;
    int lineOffset;
    TkMacOSXDrawingContext drawingContext;
#if !TK_MAC_COALESCE_LINE
    Tcl_DString runString;
#endif

    if (!TkMacOSXSetupDrawingContext(drawable, gc, tkMacOSXUseCGDrawing,
	    &drawingContext)) {
	return;
    }

#if 0
    /*
     * TODO: implement stippled text drawing
     */

    if ((gc->fill_style == FillStippled
	    || gc->fill_style == FillOpaqueStippled)
	    && gc->stipple != None) {
	#error Stippling not implemented
    }
#endif

    x += macWin->xOff;
    y += macWin->yOff;
    /* Turn the y coordinate upside-down for Quarz drawing. */
    if (drawingContext.context) {
	CGContextConcatCTM(drawingContext.context, CGAffineTransformMake(1.0,
		0.0, 0.0, -1.0, 0.0, drawingContext.portBounds.bottom -
		drawingContext.portBounds.top));
	y = drawingContext.portBounds.bottom -
		drawingContext.portBounds.top - y;
    }
    fy = IntToFixed(y);

#if TK_MAC_COALESCE_LINE
    UpdateLineBuffer(
	    fontPtr, &drawingContext, source, numBytes, x, y, &lineOffset);

    fx = IntToFixed(currentLeft);

    uchars = (const Tcl_UniChar*) Tcl_DStringValue(&currentLine);
    ulen = Tcl_DStringLength(&currentLine) / sizeof(uchars[0]);
#else
    lineOffset = 0;
    fx = IntToFixed(x);

    Tcl_DStringInit(&runString);
    uchars = Tcl_UtfToUniCharDString(source, numBytes, &runString);
    ulen = Tcl_DStringLength(&runString) / sizeof(uchars[0]);

    LayoutSetString(fontPtr, &drawingContext, uchars, ulen);
#endif

    urstart = Tcl_NumUtfChars(source, rangeStart);
    urlen = Tcl_NumUtfChars(source+rangeStart,rangeLength);

    ChkErr(ATSUDrawText, fontPtr->atsuLayout, lineOffset+urstart, urlen, fx,
	    fy);

#if !TK_MAC_COALESCE_LINE
    Tcl_DStringFree(&runString);
#endif

    TkMacOSXRestoreDrawingContext(&drawingContext);
}

/*
 *---------------------------------------------------------------------------
 *
 * MeasureStringWidth --
 *
 *	Low-level measuring of strings.
 *
 * Results:
 *	The width of the string in pixels.
 *
 * Side effects:
 *	None.
 *
 * Assumptions:
 *	fontPtr->atsuLayout is setup with the actual string data to measure.
 *
 *---------------------------------------------------------------------------
 */
static int
MeasureStringWidth(
    const MacFont *fontPtr,	/* Contains font, ATSU layout and string data
				 * to measure. */
    int start, int end)		/* Start and end positions to measure in that
				 * string. */
{
    /*
     * This implementation of measuring via ATSUGetGlyphBounds() does not
     * quite conform with the specification given for [font measure]:
     *
     *	   The return value is the total width in pixels of text, not
     *	   including the extra pixels used by highly exagerrated characters
     *	   such as cursive "f".
     *
     * Instead the result of ATSUGetGlyphBounds() *does* include these
     * "extra pixels".
     */

    ATSTrapezoid bounds;
    ItemCount numBounds;

    if (end <= start) {
	return 0;
    }

    bounds.upperRight.x = bounds.upperLeft.x = 0;
    ChkErr(ATSUGetGlyphBounds, fontPtr->atsuLayout, 0, 0, start, end-start,
	    kATSUseFractionalOrigins, 1, &bounds, &numBounds);
#ifdef TK_MAC_DEBUG_FONTS
    if (numBounds < 1 || numBounds > 1) {
	TkMacOSXDbgMsg("ATSUGetGlyphBounds: %s output",
		numBounds < 1 ? "No " : "More");
    }
#endif

    return FixedToInt(bounds.upperRight.x - bounds.upperLeft.x);
}

#if TK_MAC_COALESCE_LINE
/*
 *-------------------------------------------------------------------------
 *
 * UpdateLineBuffer --
 *
 *	See the general dicussion of TK_MAC_COALESCE_LINE on the header
 *	pages. This function maintains the data for this feature.
 *
 * Results:
 *
 *	The Tcl_UniChar string of the whole line as seen so far.
 *
 * Side effects:
 *	"*offset" is filled with the index of the first new character in
 *	"currentLine". The globals currentLine, currentY, currentLeft,
 *	currentRight and currentFontPtr are updated as necessary.
 *
 *	The currentLine string is set as the current text in
 *	fontPtr->atsuLayout (see LayoutSetString()).
 *
 *-------------------------------------------------------------------------
 */

static const Tcl_UniChar *
UpdateLineBuffer(
    const MacFont *fontPtr,	/* The font to be used for the new piece of
				 * text. */
    const TkMacOSXDrawingContext *drawingContextPtr,
				/* The Quarz drawing parameters. Needed for
				 * measuring the new piece. */
    const char *source,		/* A new piece of line to be added. */
    int numBytes,		/* Length of the new piece. */
    int x, int y,		/* Position of the new piece in the window. */
    int *offset)		/* Filled with the offset of the new piece in
				 * currentLine. */
{
    const Tcl_UniChar * uchars;
    int ulen;

    if (y != currentY
	    || x < currentRight-1 || x > currentRight+2
	    || currentFontPtr != fontPtr) {
	Tcl_DStringFree(&currentLine);
	Tcl_DStringInit(&currentLine);
	currentY = y;
	currentLeft = x;
	currentFontPtr = fontPtr;
	*offset = 0;
    } else {
	*offset = Tcl_DStringLength(&currentLine) / 2;
    }

    Tcl_UtfToUniCharDString(source, numBytes, &currentLine);
    uchars = (const Tcl_UniChar*) Tcl_DStringValue(&currentLine);
    ulen = Tcl_DStringLength(&currentLine) / sizeof(*uchars);
    LayoutSetString(fontPtr, drawingContextPtr, uchars, ulen);
    currentRight = x + MeasureStringWidth(fontPtr, *offset, ulen);

    return uchars;
}
#endif /* TK_MAC_COALESCE_LINE */

/*
 *---------------------------------------------------------------------------
 *
 * FamilyNameForFamilyID --
 *
 *	Helper for InitFont() and TkMacOSXFontDescriptionForFMFontInfo().
 *	Retrieves font family names for a given font family ID.
 *
 * Results:
 *	Font family name or NULL.
 *
 * Side effects:
 *	None.
 *
 *---------------------------------------------------------------------------
 */

static const char *
FamilyNameForFamilyID(
    FMFontFamily familyId)
{
    OSStatus err;
    char name[256] = "";
    const MacFontFamily * familyPtr = NULL;

    err = ChkErr(GetFontFamilyName, familyId, name, sizeof(name));
    if (err == noErr) {
	/*
	 * We find the canonical font name, so we can avoid unnecessary
	 * memory management.
	 */

	familyPtr = FindFontFamily(name);
#ifdef TK_MAC_DEBUG_FONTS
	if (!familyPtr) {
	    TkMacOSXDbgMsg("Font family '%s' not found", name);
	}
#endif
    }
    return familyPtr ? familyPtr->name : NULL;
}

/*
 *---------------------------------------------------------------------------
 *
 * InitFont --
 *
 *	Helper for TkpGetNativeFont() and TkpGetFontFromAttributes().
 *	Initializes the memory for a MacFont that wraps the
 *	platform-specific data.
 *
 *	The caller is responsible for initializing the fields of the TkFont
 *	that are used exclusively by the generic TkFont code, and for
 *	releasing those fields before calling TkpDeleteFont().
 *
 * Results:
 *	Fills the MacFont structure.
 *
 * Side effects:
 *	Memory allocated.
 *
 *---------------------------------------------------------------------------
 */

static void
InitFont(
    FMFontFamily familyId,	/* The font family to initialize for. */
    const char * familyName,	/* The font family name, if known. Otherwise
				 * this can be NULL. */
    int size,			/* Point size for the font. */
    int qdStyle,		/* QuickDraw style bits. */
    MacFont * fontPtr)		/* Filled with information constructed from the
				 * above arguments. */
{
    FontInfo fi;
    TkFontAttributes * faPtr;
    TkFontMetrics * fmPtr;
    int periodWidth, wWidth;

    if (size == 0) {
	size = GetDefFontSize();
    }
    ChkErr(FetchFontInfo, familyId, size, qdStyle, &fi);
    if (!familyName) {
	familyName = FamilyNameForFamilyID(familyId);
    }

    fontPtr->font.fid = (Font) fontPtr;

    faPtr = &fontPtr->font.fa;
    faPtr->family = familyName;
    faPtr->size = size;
    faPtr->weight = (qdStyle & bold) ? TK_FW_BOLD : TK_FW_NORMAL;
    faPtr->slant = (qdStyle & italic) ? TK_FS_ITALIC : TK_FS_ROMAN;
    faPtr->underline = ((qdStyle & underline) != 0);
    faPtr->overstrike = 0;

    fmPtr = &fontPtr->font.fm;

    /*
     * Note: Macs measure the line height as ascent + descent +
     * leading. Leading as a separate entity does not exist in X11
     * and Tk. We add it to the ascent at the moment, because adding
     * it to the descent, as the Mac docs would indicate, would change
     * the position of self-drawn underlines.
     */

    fmPtr->ascent = fi.ascent + fi.leading;
    fmPtr->descent = fi.descent;
    fmPtr->maxWidth = fi.widMax;

    fontPtr->qdFont = familyId;
    fontPtr->qdSize = size;
    fontPtr->qdStyle = (short) qdStyle;

    InitATSUObjects(familyId, size, qdStyle, &fontPtr->atsuFontId,
	    &fontPtr->atsuLayout, &fontPtr->atsuStyle);

    Tk_MeasureChars((Tk_Font)fontPtr, ".", 1, -1, 0, &periodWidth);
    Tk_MeasureChars((Tk_Font)fontPtr, "W", 1, -1, 0, &wWidth);
    fmPtr->fixed = periodWidth == wWidth;

    SetFontFeatures(fontPtr->atsuFontId, fmPtr->fixed, fontPtr->atsuStyle);

    AdjustFontHeight(fontPtr);
}

/*
 *---------------------------------------------------------------------------
 *
 * InitATSUObjects --
 *
 *	Helper for InitFont(). Initializes the ATSU data handles for a
 *	MacFont.
 *
 * Results:
 *	Sets up all we know and can do at this point in time in fontIdPtr,
 *	layoutPtr and stylePtr.
 *
 * Side effects:
 *	Allocates data structures inside of ATSU.
 *
 *---------------------------------------------------------------------------
 */

static void
InitATSUObjects(
    FMFontFamily familyId,	/* The font family to use. */
    short ptSize, short qdStyles,
				/* The additional font parameters. */
    ATSUFontID *fontIdPtr,	/* Filled with the font id. */
    ATSUTextLayout *layoutPtr,	/* Filled with the ATSU layout handle. */
    ATSUStyle *stylePtr)	/* Filled with the ATSU style handle,
				 * configured with all parameters. */
{
    FMFontStyle stylesDone, stylesLeft;

    /*
     * Defaults in case of error.
     */

    *fontIdPtr = GetAppFont();
    *stylePtr = 0;
    *layoutPtr = 0;

    /*
     * Generate a font id from family id and QD style bits.
     */

    ChkErr(FMGetFontFromFontFamilyInstance, familyId, qdStyles, fontIdPtr,
	    &stylesDone);

    /*
     * We see what style bits are left and tell ATSU to synthesize what's
     * left like QD does it.
     */

    stylesLeft = qdStyles & ~(unsigned)stylesDone;

    /*
     * Create the style and set its attributes.
     */

    ChkErr(ATSUCreateStyle, stylePtr);
    InitATSUStyle(*fontIdPtr, ptSize, stylesLeft, *stylePtr);

    /*
     * Create the layout. Note: We can't set the layout attributes here,
     * because the text and the style must be set first.
     */

    ChkErr(ATSUCreateTextLayout, layoutPtr);
    /*InitATSULayout(*layoutPtr);*/
}

/*
 *---------------------------------------------------------------------------
 *
 * InitATSUStyle --
 *
 *	Helper for InitATSUObjects(). Initializes the ATSU style for a
 *	MacFont.
 *
 * Results:
 *	Sets up all parameters needed for an ATSU style.
 *
 * Side effects:
 *	Allocates data structures for the style inside of ATSU.
 *
 *---------------------------------------------------------------------------
 */

static void
InitATSUStyle(
    ATSUFontID fontId,		/* The font id to use. */
    short ptSize, short qdStyles,
				/* Additional font parameters. */
    ATSUStyle style)		/* The style handle to configure. */
{
    /*
     * Attributes for the style.
     */

    Fixed fsize = IntToFixed(ptSize);
    Boolean
	isBold = (qdStyles&bold) != 0,
	isUnderline = (qdStyles&underline) != 0,
	isItalic = (qdStyles&italic) != 0;

    ATSStyleRenderingOptions options =
	antialiasedTextEnabled == -1 ? kATSStyleNoOptions :
	antialiasedTextEnabled == 0  ? kATSStyleNoAntiAliasing :
				       kATSStyleApplyAntiAliasing;

    static const ATSUAttributeTag styleTags[] = {
	kATSUFontTag, kATSUSizeTag,
	kATSUQDBoldfaceTag, kATSUQDItalicTag, kATSUQDUnderlineTag,
	kATSUStyleRenderingOptionsTag,
    };
    static const ByteCount styleSizes[] = {
	sizeof(ATSUFontID), sizeof(Fixed),
	sizeof(Boolean), sizeof(Boolean), sizeof(Boolean),
	sizeof(ATSStyleRenderingOptions),
    };
    const ATSUAttributeValuePtr styleValues[] = {
	&fontId, &fsize,
	&isBold, &isItalic, &isUnderline,
	&options,
    };

    ChkErr(ATSUSetAttributes, style, sizeof(styleTags)/sizeof(styleTags[0]),
	    styleTags, styleSizes, styleValues);
}

/*
 *---------------------------------------------------------------------------
 *
 * SetFontFeatures --
 *
 *	Helper for InitFont(). Request specific font features of the ATSU
 *	style object for a MacFont.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	Specific font features are enabled on the ATSU style object.
 *
 *---------------------------------------------------------------------------
 */

static void
SetFontFeatures(
    ATSUFontID fontId,		/* The font id to use. */
    int fixed,			/* Is this a fixed font? */
    ATSUStyle style)		/* The style handle to configure. */
{
    /*
     * Don't use the standard latin ligatures, if this is determined to be a
     * fixed-width font.
     */

    static const ATSUFontFeatureType fixed_featureTypes[] = {
	kLigaturesType, kLigaturesType
    };
    static const ATSUFontFeatureSelector fixed_featureSelectors[] = {
	kCommonLigaturesOffSelector, kRareLigaturesOffSelector
    };

    if (fixed) {
	ChkErr(ATSUSetFontFeatures, style, sizeof(fixed_featureTypes) /
		sizeof(fixed_featureTypes[0]), fixed_featureTypes,
		fixed_featureSelectors);
    }
}

/*
 *---------------------------------------------------------------------------
 *
 * AdjustFontHeight --
 *
 *	Helper for InitFont(). Check font height against some real world
 *	examples.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	The metrics in fontPtr->font.fm are adjusted so that typical combined
 *	characters fit into ascent+descent.
 *
 *---------------------------------------------------------------------------
 */

static void
AdjustFontHeight(
    MacFont * fontPtr)
{
    /*
     * The standard values for ascent, descent and leading as determined in
     * InitFont do not take composition into account, they are designed for
     * plain ASCII characters. This code measures the actual size of some
     * typical composed characters from the Latin-1 range and corrects these
     * factors, especially the ascent.
     *
     * A font requested with a pixel size may thus have a larger line height
     * than requested.
     *
     * An alternative would be to instruct ATSU to shrink oversized combined
     * characters. I think I have seen that feature somewhere, but I can't
     * find it now [BR].
     */

    static const UniChar chars[]
	    /* Auml,   Aacute, Acirc,  Atilde, Ccedilla */
	    = {0x00C4, 0x00C1, 0x00C2, 0x00C3, 0x00C7};
    static const int charslen = sizeof(chars) / sizeof(chars[0]);
    Rect size;
    OSStatus err;

    LayoutSetString(fontPtr, NULL, chars, charslen);

    size.top = size.bottom = 0;
    err = ChkErr(ATSUMeasureTextImage, fontPtr->atsuLayout, 0, charslen, 0, 0,
	    &size);

    if (err == noErr) {
	TkFontMetrics * fmPtr = &fontPtr->font.fm;
	int ascent = -size.top;
	int descent = size.bottom;

	if (ascent > fmPtr->ascent) {
	    fmPtr->ascent = ascent;
	}
	if (descent > fmPtr->descent) {
	    fmPtr->descent = descent;
	}
    }
}

/*
 *---------------------------------------------------------------------------
 *
 * InitATSULayout --
 *
 *	Helper for LayoutSetString(). Initializes the ATSU layout
 *	object for a MacFont and a specific string.
 *
 * Results:
 *	Sets up all parameters needed for an ATSU layout object.
 *
 * Side effects:
 *	Allocates data structures for the layout object inside of ATSU.
 *
 * Assumptions:
 *	The actual string data and style information is already set by
 *	ATSUSetTextPointerLocation() and ATSUSetRunStyle() (see
 *	LayoutSetString()).
 *
 *---------------------------------------------------------------------------
 */

static void
InitATSULayout(
    const TkMacOSXDrawingContext  *drawingContextPtr,
				/* Specifies the CGContext to use. */
    ATSUTextLayout layout,	/* The layout object to configure. */
    int fixed)			/* Is this a fixed font? */
{
    /*
     * Attributes for the layout.
     */

    ATSLineLayoutOptions layoutOptions = 0
#if TK_MAC_COALESCE_LINE
	    /*
	     * Options to use unconditionally  when we try to do coalescing.
	     */
	    | kATSLineDisableAllLayoutOperations
	    | kATSLineFractDisable
	    | kATSLineUseDeviceMetrics
#endif
	    ;
    CGContextRef context = drawingContextPtr ?
	drawingContextPtr->context : NULL;

    static const ATSUAttributeTag layoutTags[] = {
	kATSUCGContextTag,
	kATSULineLayoutOptionsTag,
    };
    static const ByteCount layoutSizes[] = {
	sizeof(CGContextRef),
	sizeof(ATSLineLayoutOptions),
    };
    const ATSUAttributeValuePtr layoutValues[] = {
	&context,
	&layoutOptions,
    };

    /*
     * Ensure W(abcdefg) == W(a)*7 for fixed fonts (Latin scripts only).
     */

    if (fixed) {
	layoutOptions |= kATSLineFractDisable | kATSLineUseDeviceMetrics;
    }

    ChkErr(ATSUSetLayoutControls, layout, sizeof(layoutTags) /
	    sizeof(layoutTags[0]), layoutTags, layoutSizes, layoutValues);
    ChkErr(ATSUSetTransientFontMatching, layout, true);
}

/*
 *---------------------------------------------------------------------------
 *
 * LayoutSetString --
 *
 *	Setup the MacFont for a specific string.
 *
 * Results:
 *	Sets up all parameters so that ATSU can work with the objects in
 *	MacFont.
 *
 * Side effects:
 *	Sets parameters on the layout object fontPtr->atsuLayout.
 *
 *---------------------------------------------------------------------------
 */

void
LayoutSetString(
    const MacFont *fontPtr,	/* The fontPtr to configure. */
    const TkMacOSXDrawingContext *drawingContextPtr,
				/* For the CGContext to be used.*/
    const UniChar *uchars, int ulen)
				/* The UniChar string to set into
				 * fontPtr->atsuLayout. */
{
    ChkErr(ATSUSetTextPointerLocation, fontPtr->atsuLayout, uchars,
	    kATSUFromTextBeginning, ulen, ulen);

    /*
     * Styles can only be set after the text is set.
     */

    ChkErr(ATSUSetRunStyle, fontPtr->atsuLayout, fontPtr->atsuStyle,
	    kATSUFromTextBeginning, kATSUToTextEnd);

    /*
     * Layout attributes can only be set after the styles are set.
     */

    InitATSULayout(drawingContextPtr, fontPtr->atsuLayout,
	    fontPtr->font.fm.fixed);
}

/*
 *-------------------------------------------------------------------------
 *
 * ReleaseFont --
 *
 *	Called to release the Macintosh-specific contents of a TkFont. The
 *	caller is responsible for freeing the memory used by the font
 *	itself.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	Memory is freed.
 *
 *---------------------------------------------------------------------------
 */

static void
ReleaseFont(
    MacFont *fontPtr)		/* The font to delete. */
{
    ATSUDisposeTextLayout(fontPtr->atsuLayout);
    ATSUDisposeStyle(fontPtr->atsuStyle);
}

/*
 *-------------------------------------------------------------------------
 *
 * FindFontFamilyOrAlias, FindFontFamilyOrAliasOrFallback --
 *
 *	Determine if any physical screen font exists on the system with the
 *	given family name. If the family exists, then it should be possible
 *	to construct some physical screen font with that family name.
 *
 *	FindFontFamilyOrAlias also considers font aliases as determined by
 *	TkFontGetAliasList().
 *
 *	FindFontFamilyOrAliasOrFallback also considers font aliases as
 *	determined by TkFontGetFallbacks().
 *
 *	The overall algorithm to get the closest font to the one requested is
 *	this:
 *
 *		try fontname
 *		try all aliases for fontname
 *		foreach fallback for fontname
 *			try the fallback
 *			try all aliases for the fallback
 *
 * Results:
 *
 *	The return value is NULL if the specified font family does not exist,
 *	a valid MacFontFamily* otherwise.
 *
 * Side effects:
 *
 *	None.
 *
 *-------------------------------------------------------------------------
 */

static const MacFontFamily *
FindFontFamilyOrAlias(
    const char *name)		/* Name or alias name of the font to find. */
{
    const MacFontFamily * familyPtr;
    char ** aliases;
    int i;

    familyPtr = FindFontFamily(name);
    if (familyPtr != NULL) {
	return familyPtr;
    }

    aliases = TkFontGetAliasList(name);
    if (aliases != NULL) {
	for (i = 0; aliases[i] != NULL; i++) {
	    familyPtr = FindFontFamily(aliases[i]);
	    if (familyPtr != NULL) {
		return familyPtr;
	    }
	}
    }
    return NULL;
}

static const MacFontFamily *
FindFontFamilyOrAliasOrFallback(
    const char *name)		/* Name or alias name of the font to find. */
{
    const MacFontFamily * familyPtr;
    const char * fallback;
    char *** fallbacks;
    int i, j;

    familyPtr = FindFontFamilyOrAlias(name);
    if (familyPtr != NULL) {
	return familyPtr;
    }
    fallbacks = TkFontGetFallbacks();
    for (i = 0; fallbacks[i] != NULL; i++) {
	for (j = 0; (fallback = fallbacks[i][j]) != NULL; j++) {
	    if (strcasecmp(name, fallback) == 0) {
		for (j = 0; (fallback = fallbacks[i][j]) != NULL; j++) {
		    familyPtr = FindFontFamilyOrAlias(fallback);
		    if (familyPtr != NULL) {
			return familyPtr;
		    }
		}
	    }
	    break; /* benny: This "break" is a carry-over from
		    * tkMacOSXFont.c, but what is actually its purpose
		    * ???? */
	}
    }


    /*
     * FIXME: We would have liked to recover by re-enumerating fonts. But
     * that doesn't work, because Carbon seems to cache the inital list of
     * fonts. Fonts newly installed don't show up with
     * FMCreateFontFamilyIterator()/FMGetNextFontFamily() without a restart
     * of the app. Similar problem with fonts removed.
     */

#ifdef TK_MAC_DEBUG_FONTS
    TkMacOSXDbgMsg("Font family '%s' not found", name);
#endif

    return NULL;
}

/*
 *-------------------------------------------------------------------------
 *
 * InitFontFamilies --
 *
 *	Helper to TkpFontPkgInit. Use the Font Manager to fill in the
 *	familyList global array.
 *
 * Results:
 *
 *	None.
 *
 * Side effects:
 *
 *	Allocates memory.
 *
 *-------------------------------------------------------------------------
 */

static void
InitFontFamilies(void)
{
    FMFontFamily fontFamily;
    Str255 fontName;
    SInt16 fontSize;
    Style  fontStyle;

    /*
     * Has this been called before?
     */

    if (familyListNextFree > 0) {
	return;
    }

    ChkErr(ATSFontFamilyApplyFunction, FontFamilyEnumCallback,NULL);

    if (GetThemeFontAndFamily(kThemeSystemFont, &fontFamily, fontName,
	    &fontSize, &fontStyle) == noErr) {
	AddFontFamily(SYSTEMFONT_NAME, fontFamily);
    }
    if (GetThemeFontAndFamily(kThemeApplicationFont, &fontFamily, fontName,
	    &fontSize, &fontStyle) == noErr) {
	AddFontFamily(APPLFONT_NAME, fontFamily);
    }
    if (GetThemeFontAndFamily(kThemeMenuItemFont, &fontFamily, fontName,
	    &fontSize, &fontStyle) == noErr) {
	AddFontFamily(MENUITEMFONT_NAME, fontFamily);
    }

    SortFontFamilies();
}

/*
 *-------------------------------------------------------------------------
 *
 * FontFamilyEnumCallback --
 *
 *	Callback for ATSFontFamilyApplyFunction().
 *
 * Results:
 *
 *	noErr.
 *
 * Side effects:
 *
 *	None.
 *
 *-------------------------------------------------------------------------
 */

static OSStatus
FontFamilyEnumCallback(
    ATSFontFamilyRef family,
    void *refCon)
{
    OSStatus err;
    char name[260] = "";

    (void) refCon;

    err = ChkErr(GetFontFamilyName, family, name, sizeof(name));
    if (err == noErr) {
	AddFontFamily(name, family);
    }

    return noErr;
}

/*
 *-------------------------------------------------------------------------
 *
 * GetFontFamilyName --
 *
 *	Use the Font Manager to get the name of a given FMFontfamily. This
 *	currently gets the standard, non-localized QuickDraw name. Other
 *	names would be possible, see docs for ATSUFindFontName for a
 *	selection. The MacOSX font selector seems to use the localized
 *	family name given by ATSUFindFontName(kFontFamilyName), but that API
 *	doesn't give us a name at all for some fonts.
 *
 * Results:
 *	An OS error code, noErr on success. name is filled with the
 *	resulting name.
 *
 * Side effects:
 *	None.
 *
 *-------------------------------------------------------------------------
 */

static OSStatus
GetFontFamilyName(
    FMFontFamily fontFamily,	/* The font family for which to find the
				 * name. */
    char * name, int numBytes)	/* Filled with the result. */
{
    OSStatus err;
    Str255 nativeName;
    CFStringRef cfString;
    TextEncoding encoding;
    ScriptCode nameencoding;

    nativeName[0] = 0;
    name[0] = 0;
    err = ChkErr(FMGetFontFamilyName, fontFamily, nativeName);
    if (err != noErr) {
	return err;
    }

    /*
     * QuickDraw font names are encoded with the script that the font uses.
     * So we determine that encoding and than we reencode the name.
     */

    encoding = kTextEncodingMacRoman;
    ChkErr(FMGetFontFamilyTextEncoding, fontFamily, &encoding);
    nameencoding = encoding;
    ChkErr(RevertTextEncodingToScriptInfo, encoding, &nameencoding, NULL,
	    NULL);

    /*
     * Note: We could use Tcl facilities to do the re-encoding here. We'd
     * have to maintain tables to map OS encoding codes to Tcl encoding names
     * like tkMacOSXFont.c did. Using native re-encoding directly instead is
     * a lot easier and future-proof than that. There is one snag, though: I
     * have seen CFStringGetCString() crash with invalid encoding ids. But
     * than if that happens it would be a bug in
     * FMGetFontFamilyTextEncoding() or RevertTextEncodingToScriptInfo().
     */

    cfString = CFStringCreateWithPascalStringNoCopy(
	    NULL, nativeName, nameencoding, kCFAllocatorNull);
    CFStringGetCString(
	    cfString, name, numBytes, kCFStringEncodingUTF8);
    CFRelease(cfString);

    return noErr;
}

/*
 *-------------------------------------------------------------------------
 *
 * FindFontFamily --
 *
 *	Find the font family with the given name in the global familyList.
 *	Uses bsearch() for convenient access. Comparision is done
 *	non-case-sensitively with CompareFontFamilies() which see.
 *
 * Results:
 *
 *	MacFontFamily: A pair of family id and the actual name registered for
 *	the font.
 *
 * Side effects:
 *
 *	None.
 *
 * Assumption:
 *
 *	Requires the familyList array to be sorted.
 *
 *-------------------------------------------------------------------------
 */

static const MacFontFamily *
FindFontFamily(
    const char *name)		/* The family name. Note: Names are compared
				 * non-case-sensitive. */
{
    const MacFontFamily key = {name,-1};

    if(familyListMaxValid <= 0) {
	return NULL;
    }

    return bsearch(&key, familyList, familyListMaxValid, sizeof(*familyList),
	    CompareFontFamilies);
}

/*
 *-------------------------------------------------------------------------
 *
 * EnumFontFamilies --
 *
 *	Create a Tcl list with the registered names in the global familyList.
 *
 * Results:
 *	A Tcl list of names.
 *
 * Side effects:
 *	None.
 *
 *-------------------------------------------------------------------------
 */

static Tcl_Obj *
EnumFontFamilies(void)
{
    int i;
    Tcl_Obj * tclList;

    tclList = Tcl_NewListObj(0, NULL);
    for (i=0; i<familyListMaxValid; ++i) {
	Tcl_ListObjAppendElement(NULL, tclList,
		Tcl_NewStringObj(familyList[i].name, -1));
    }

    return tclList;
}

/*
 *-------------------------------------------------------------------------
 *
 * AddFontFamily --
 *
 *	Register a font family in familyList. Until SortFontFamilies() is
 *	called, this is not actually available for FindFontFamily().
 *
 * Results:
 *
 *	MacFontFamily: The new pair of family id and the actual name
 *	registered for the font.
 *
 * Side effects:
 *
 *	New entry in familyList and familyListNextFree updated.
 *
 *-------------------------------------------------------------------------
 */

static const MacFontFamily *
AddFontFamily(
    const char *name,		/* Font family name to register. */
    FMFontFamily familyId)	/* Font family id to register. */
{
    MacFontFamily * familyPtr;

    if (familyListNextFree >= familyListSize) {
	familyListSize += 100;
	familyList = (MacFontFamily *) ckrealloc((void*) familyList,
		familyListSize * sizeof(*familyList));
    }

    familyPtr = familyList + familyListNextFree;
    ++familyListNextFree;

    familyPtr->name = AddString(name);
    familyPtr->familyId = familyId;

    return familyPtr;
}

/*
 *-------------------------------------------------------------------------
 *
 * SortFontFamilies --
 *
 *	Sort the entries in familyList. Only after calling
 *	SortFontFamilies(), the new families registered with AddFontFamily()
 *	are actually available for FindFontFamily(), because FindFontFamily()
 *	requires the array to be sorted.
 *
 * Results:
 *
 *	None.
 *
 * Side effects:
 *
 *	familyList is sorted and familyListMaxValid is updated.
 *
 *-------------------------------------------------------------------------
 */

static void
SortFontFamilies(void)
{
    if (familyListNextFree > 0) {
	qsort(familyList, familyListNextFree, sizeof(*familyList),
		CompareFontFamilies);
    }
    familyListMaxValid = familyListNextFree;
}

/*
 *-------------------------------------------------------------------------
 *
 * CompareFontFamilies --
 *
 *	Comparison function used by SortFontFamilies() and FindFontFamily().
 *
 * Results:
 *	Result as required to generate a stable sort order for bsearch() and
 *	qsort(). The ordering is not case-sensitive as far as
 *	Tcl_UtfNcasecmp() (which see) can provide that.
 *
 *	Note: It would be faster to compare first the length and the actual
 *	strings only as a tie-breaker, but than the ordering wouldn't look so
 *	pretty in [font families] ;-).
 *
 * Side effects:
 *	None.
 *
 *-------------------------------------------------------------------------
 */

static int
CompareFontFamilies(
    const void * vp1,
    const void * vp2)
{
    const char * name1;
    const char * name2;
    int len1, len2, diff;

    name1 = ((const MacFontFamily *) vp1)->name;
    name2 = ((const MacFontFamily *) vp2)->name;

    len1 = Tcl_NumUtfChars(name1, -1);
    len2 = Tcl_NumUtfChars(name2, -1);

    diff = Tcl_UtfNcasecmp(name1, name2, len1<len2 ? len1 : len2);

    return diff == 0 ? len1-len2 : diff;
}

/*
 *-------------------------------------------------------------------------
 *
 * AddString --
 *
 *	Helper for AddFontFamily(). Allocates a string in the one-shot
 *	allocator.
 *
 * Results:
 *	A duplicated string in the one-shot allocator.
 *
 * Side effects:
 *	May allocate a new memory block.
 *
 *-------------------------------------------------------------------------
 */

static const char *
AddString(
    const char *in)		/* String to add, zero-terminated. */
{
    int len;
    char *result;

    len = strlen(in) +1;

    if (stringMemory == NULL
	    || (stringMemory->nextFree+len) > STRING_BLOCK_MAX) {
	StringBlock * newblock = (StringBlock *) ckalloc(sizeof(StringBlock));

	newblock->next = stringMemory;
	newblock->nextFree = 0;
	stringMemory = newblock;
    }

    result = stringMemory->strings + stringMemory->nextFree;
    stringMemory->nextFree += len;

    memcpy(result, in, len);

    return result;
}

/*
 *---------------------------------------------------------------------------
 *
 * TkMacOSXIsCharacterMissing --
 *
 *	Given a tkFont and a character determine whether the character has
 *	a glyph defined in the font or not.
 *
 * Results:
 *	Returns a 1 if the character is missing, a 0 if it is not.
 *
 * Side effects:
 *	None.
 *
 *---------------------------------------------------------------------------
 */

int
TkMacOSXIsCharacterMissing(
    Tk_Font tkfont,		/* The font we are looking in. */
    unsigned int searchChar)	/* The character we are looking for. */
{
    /* Background: This function is private and only used in
     * tkMacOSXMenu.c:FindMarkCharacter().
     *
     * We could use ATSUMatchFont() to implement. We'd have to change the
     * definition of the encoding of the parameter searchChar from MacRoman
     * to UniChar for that.
     *
     * The system uses font fallback for controls, so we don't really need
     * this. */

    return 0;
}

/*
 *----------------------------------------------------------------------
 *
 * TkMacOSXInitControlFontStyle --
 *
 *	This procedure sets up the appropriate ControlFontStyleRec
 *	for a Mac control.
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
TkMacOSXInitControlFontStyle(
    Tk_Font tkfont,		/* Tk font object to use for the control. */
    ControlFontStylePtr fsPtr)	/* The style object to configure. */
{
    const MacFont * fontPtr = (MacFont *) tkfont;

    fsPtr->flags = kControlUseFontMask | kControlUseSizeMask |
	    kControlUseFaceMask | kControlUseJustMask;
    fsPtr->font = fontPtr->qdFont;
    fsPtr->size = fontPtr->qdSize;
    fsPtr->style = fontPtr->qdStyle;
    fsPtr->just = teCenter;
}

/*
 *----------------------------------------------------------------------
 *
 * TkMacOSXUseAntialiasedText --
 *
 *	Enables or disables application-wide use of antialiased text (where
 *	available). Sets up a linked Tcl global variable to allow
 *	disabling of antialiased text from tcl.
 *	The possible values for this variable are:
 *
 *	-1 - Use system default as configurable in "System Prefs" -> "General".
 *	 0 - Unconditionally disable antialiasing.
 *	 1 - Unconditionally enable antialiasing.
 *
 * Results:
 *
 *	TCL_OK.
 *
 * Side effects:
 *
 *	None.
 *
 *----------------------------------------------------------------------
 */

MODULE_SCOPE int
TkMacOSXUseAntialiasedText(
    Tcl_Interp * interp,	/* The Tcl interpreter to receive the
				 * variable.*/
    int enable)			/* Initial value. */
{
    static Boolean initialized = FALSE;

    if (!initialized) {
	initialized = TRUE;

	if (Tcl_CreateNamespace(interp, "::tk::mac", NULL, NULL) == NULL) {
	    Tcl_ResetResult(interp);
	}
	if (Tcl_LinkVar(interp, "::tk::mac::antialiasedtext",
		(char *) &antialiasedTextEnabled,
		TCL_LINK_INT) != TCL_OK) {
	    Tcl_ResetResult(interp);
	}
    }
    antialiasedTextEnabled = enable;
    return TCL_OK;
}

/*
 * Local Variables:
 * mode: c
 * c-basic-offset: 4
 * fill-column: 79
 * coding: utf-8
 * End:
 */
