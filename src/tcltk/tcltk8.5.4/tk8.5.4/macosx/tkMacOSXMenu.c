/*
 * tkMacOSXMenu.c --
 *
 *	This module implements the Mac-platform specific features of menus.
 *
 * Copyright (c) 1996-1997 by Sun Microsystems, Inc.
 * Copyright 2001, Apple Computer, Inc.
 * Copyright (c) 2005-2007 Daniel A. Steffen <das@users.sourceforge.net>
 *
 * See the file "license.terms" for information on usage and redistribution
 * of this file, and for a DISCLAIMER OF ALL WARRANTIES.
 *
 * RCS: @(#) $Id: tkMacOSXMenu.c,v 1.45 2007/12/13 15:27:10 dgp Exp $
 */

#include "tkMacOSXPrivate.h"
#include "tkMenubutton.h"
#include "tkMenu.h"
#include "tkColor.h"
#include "tkFont.h"
#include "tkMacOSXDebug.h"

/*
#ifdef TK_MAC_DEBUG
#define TK_MAC_DEBUG_MENUS
#endif
*/

#define USE_TK_MDEF

typedef struct MacMenu {
    MenuRef menuHdl;		/* The Menu Manager data structure. */
#ifdef USE_TK_MDEF
    int useMDEF;		/* true if this menu uses the MDEF */
#endif
} MacMenu;

typedef struct MenuEntryUserData {
    Drawable mdefDrawable;
    TkMenuEntry *mePtr;
    Tk_Font tkfont;
    Tk_FontMetrics *fmPtr;
} MenuEntryUserData;

/*
 * Platform specific flags for menu entries
 *
 * ENTRY_COMMAND_ACCEL		Indicates the entry has the command key
 *				in its accelerator string.
 * ENTRY_OPTION_ACCEL		Indicates the entry has the option key
 *				in its accelerator string.
 * ENTRY_SHIFT_ACCEL		Indicates the entry has the shift key
 *				in its accelerator string.
 * ENTRY_CONTROL_ACCEL		Indicates the entry has the control key
 *				in its accelerator string.
 */

#define ENTRY_COMMAND_ACCEL	ENTRY_PLATFORM_FLAG1
#define ENTRY_OPTION_ACCEL	ENTRY_PLATFORM_FLAG2
#define ENTRY_SHIFT_ACCEL	ENTRY_PLATFORM_FLAG3
#define ENTRY_CONTROL_ACCEL	ENTRY_PLATFORM_FLAG4
#define ENTRY_ACCEL_MASK	(ENTRY_COMMAND_ACCEL | ENTRY_OPTION_ACCEL \
				| ENTRY_SHIFT_ACCEL | ENTRY_CONTROL_ACCEL)
#define MODIFIER_NUM 4

/*
 * This structure is used to keep track of subfields within Macintosh menu
 * items.
 */

typedef struct EntryGeometry {
    int accelTextStart;		/* Offset into the accel string where
				 * the text starts. Everything before
				 * this is modifier key descriptions.
				 */
    int modifierWidth;		/* Width of modifier symbols. */
    int accelTextWidth;		/* Width of the text after the modifier
				 * keys. */
    int nonAccelMargin;		/* The width of the margin for entries
				 * without accelerators. */
    int modifierNum;		/* Number of modifiers */
    Tcl_UniChar modifierUniChars[MODIFIER_NUM];
				/* Modifiers in unicode */
    char accelGlyph;		/* Accelerator glyph, if any */
} EntryGeometry;

/*
 * Structure to keep track of toplevel windows and their menubars.
 */

typedef struct TopLevelMenubarList {
    struct TopLevelMenubarList *nextPtr;
				/* The next window in the list. */
    Tk_Window tkwin;		/* The toplevel window. */
    TkMenu *menuPtr;		/* The menu associated with this
				 * toplevel. */
} TopLevelMenubarList;

/*
 * Platform-specific flags for menus.
 *
 * MENU_APPLE_MENU		0 indicates a custom Apple menu has
 *				not been installed; 1 a custom Apple
 *				menu has been installed.
 * MENU_HELP_MENU		0 indicates a custom Help menu has
 *				not been installed; 1 a custom Help
 *				menu has been installed.
 * MENU_RECONFIGURE_PENDING	1 indicates that an idle handler has
 *				been scheduled to reconfigure the
 *				Macintosh MenuHandle.
 */

#define MENU_APPLE_MENU			MENU_PLATFORM_FLAG1
#define MENU_HELP_MENU			MENU_PLATFORM_FLAG2
#define MENU_RECONFIGURE_PENDING	MENU_PLATFORM_FLAG3

#define CASCADE_CMD (0x1b)	/* The special command char for cascade
				 * menus. */
#define MENUBAR_REDRAW_PENDING 1

static int gNoTkMenus = 0;	/* This is used by Tk_MacOSXTurnOffMenus as the
				 * flag that Tk is not to draw any menus. */

static Tcl_HashTable commandTable;
				/* The list of menuInstancePtrs associated with
				 * menu ids */
static short currentAppleMenuID;
				/* The id of the current Apple menu. 0 for
				 * none. */
static short currentHelpMenuID; /* The id of the current Help menu. 0 for
				 * none. */
static Tcl_Interp *currentMenuBarInterp;
				/* The interpreter of the window that owns
				 * the current menubar. */
static char *currentMenuBarName;
				/* Malloced. Name of current menu in menu bar.
				 * NULL if no menu set. TO DO: make this a
				 * DString. */
static Tk_Window currentMenuBarOwner;
				/* Which window owns the current menu bar. */
static int inPostMenu;		/* We cannot be re-entrant like X
				 * windows. */
static short lastMenuID;	/* To pass to NewMenu; need to figure out
				 * a good way to do this. */
static short lastCascadeID;
				/* Cascades have to have ids that are
				 * less than 256. */
static int menuBarFlags;	/* Used for whether the menu bar needs
				 * redrawing or not. */

struct MenuCommandHandlerData { /* This is the ClientData we pass to */
    TkMenu *menuPtr;		/* Tcl_DoWhenIdle to move handling */
    int index;			/* menu commands to the event loop. */
};

static TopLevelMenubarList *windowListPtr;
				/* A list of windows that have menubars set. */

/*
 * Array of unicode, charcode and utf representations of the most common
 * special menu symbols.
 */
typedef struct MenuSymbol {
    const Tcl_UniChar unicode;
    const char charCode;
    /* char padding; */
    int utfLen, width;
    char utf[TCL_UTF_MAX + 1];
} MenuSymbol;

static MenuSymbol menuSymbols[] = {
    {kCommandUnicode,	kCommandCharCode},
    {kOptionUnicode,	kMenuOptionGlyph},
    {kControlUnicode,	kMenuControlGlyph},
    {kShiftUnicode,	kMenuShiftGlyph},
    {kCheckUnicode,	kCheckCharCode},
    {kDiamondUnicode,	kDiamondCharCode},
    {kBulletUnicode,	kBulletCharCode},
    {0x2026,		kNullCharCode},
    {0,			0},
};

enum MenuSymbolIdx {
    COMMAND_SYMBOL,
    OPTION_SYMBOL,
    CONTROL_SYMBOL,
    SHIFT_SYMBOL,
    CHECK_SYMBOL,
    DIAMDOND_SYMBOL,
    BULLET_SYMBOL,
    ELLIPSIS_SYMBOL,
};

MenuRef tkCurrentAppleMenu = NULL;

static SInt32 menuMarkColumnWidth = 0, menuMarkIndent = 0;
static SInt32 menuTextLeadingEdgeMargin = 0, menuTextTrailingEdgeMargin = 0;
static SInt16 menuItemExtraHeight = 0, menuItemExtraWidth = 0;
static SInt16 menuSeparatorHeight = 0;

/*
 * Forward declarations for procedures defined later in this file:
 */

MODULE_SCOPE int TkMacOSXGetNewMenuID(Tcl_Interp *interp, TkMenu *menuInstPtr,
	int cascade, short *menuIDPtr);
MODULE_SCOPE void TkMacOSXFreeMenuID(short menuID);

static void CompleteIdlers(TkMenu *menuPtr);
static void DrawMenuBarWhenIdle(ClientData clientData);
static void DrawMenuEntryAccelerator(TkMenu *menuPtr, TkMenuEntry *mePtr,
	Drawable d, GC gc, Tk_Font tkfont, const Tk_FontMetrics *fmPtr,
	Tk_3DBorder activeBorder, int x, int y, int width, int height,
	int drawArrow);
static void DrawMenuEntryBackground(TkMenu *menuPtr, TkMenuEntry *mePtr,
	Drawable d, Tk_3DBorder activeBorder, Tk_3DBorder bgBorder, int x,
	int y, int width, int heigth);
static void DrawMenuEntryIndicator(TkMenu *menuPtr, TkMenuEntry *mePtr,
	Drawable d, GC gc, GC indicatorGC, Tk_Font tkfont,
	const Tk_FontMetrics *fmPtr, int x, int y, int width, int height);
static void DrawMenuEntryLabel(TkMenu * menuPtr, TkMenuEntry *mePtr,
	Drawable d, GC gc, Tk_Font tkfont, const Tk_FontMetrics *fmPtr, int x,
	int y, int width, int height);
static void DrawMenuSeparator(TkMenu *menuPtr, TkMenuEntry *mePtr, Drawable d,
	GC gc, Tk_Font tkfont, const Tk_FontMetrics *fmPtr, int x, int y,
	int width, int height);
static void DrawTearoffEntry(TkMenu *menuPtr, TkMenuEntry *mePtr, Drawable d,
	GC gc, Tk_Font tkfont, const Tk_FontMetrics *fmPtr, int x, int y,
	int width, int height);
static void EventuallyInvokeMenu(ClientData data);
static void GetEntryText(TkMenuEntry *mePtr, Tcl_DString *dStringPtr);
static void GetMenuAccelGeometry(TkMenu *menuPtr, TkMenuEntry *mePtr,
	Tk_Font tkfont, const Tk_FontMetrics *fmPtr, int *modWidthPtr,
	int *textWidthPtr, int *heightPtr);
static void GetMenuLabelGeometry(TkMenuEntry *mePtr, Tk_Font tkfont,
	const Tk_FontMetrics *fmPtr, int *widthPtr, int *heightPtr);
static void GetMenuIndicatorGeometry(TkMenu *menuPtr, TkMenuEntry *mePtr,
	Tk_Font tkfont, const Tk_FontMetrics *fmPtr, int *widthPtr,
	int *heightPtr);
static void GetMenuSeparatorGeometry(TkMenu *menuPtr, TkMenuEntry *mePtr,
	Tk_Font tkfont, const Tk_FontMetrics *fmPtr, int *widthPtr,
	int *heightPtr);
static TkMenuEntry* GetParentMenuEntry(TkMenu *menuPtr);
static void GetTearoffEntryGeometry(TkMenu *menuPtr, TkMenuEntry *mePtr,
	Tk_Font tkfont, const Tk_FontMetrics *fmPtr, int *widthPtr,
	int *heightPtr);
static char FindMarkCharacter(TkMenuEntry *mePtr);
static int GetUtfMarkCharacter(char markChar, const char **markUtfPtr);
static TkMenu* MenuPtrForMenuRef(MenuRef menu);
static int ParseAccelerators(const char **accelStringPtr, int *modifierNumPtr,
	Tcl_UniChar *modifierUniChars, int *modifierWidth);
static void MenuSelectEvent(TkMenu *menuPtr);
static void ReconfigureIndividualMenu(TkMenu *menuPtr, MenuHandle macMenuHdl,
	int base);
static void ReconfigureMacintoshMenu(ClientData clientData);
static void RecursivelyClearActiveMenu(TkMenu *menuPtr);
static void RecursivelyDeleteMenu(TkMenu *menuPtr);
static void RecursivelyInsertMenu(TkMenu *menuPtr);
static void SetDefaultMenubar(void);
static int SetMenuCascade(TkMenu *menuPtr);

#ifdef USE_TK_MDEF
#define SCREEN_MARGIN 5
static MacDrawable macMDEFDrawable;
				/* Drawable for use by MDEF code */
static int MDEFScrollFlag = 0;	/* Used so that popups don't scroll too soon.*/
static MenuItemDrawingUPP tkThemeMenuItemDrawingUPP;
				/* Points to the UPP for theme Item drawing. */
static Tcl_Obj *useMDEFVar;

static void  DrawMenuBackground(TkMenu *menuPtr, Rect *menuRectPtr,
	Drawable d);
static void MenuDefProc(short message, MenuHandle menu, Rect *menuRectPtr,
	Point hitPt, short *whichItem );
static void HandleMenuHiliteMsg(MenuRef menu, Rect *menuRectPtr, Point hitPt,
	SInt16 *whichItem, TkMenu *menuPtr);
static void HandleMenuDrawMsg(MenuRef menu, Rect *menuRectPtr, Point hitPt,
	SInt16 *whichItem, TkMenu *menuPtr);
static void HandleMenuFindItemMsg(MenuRef menu, Rect *menuRectPtr,
	Point hitPt, SInt16 *whichItem, TkMenu *menuPtr);
static void HandleMenuPopUpMsg(MenuRef menu, Rect *menuRectPtr, Point hitPt,
	SInt16 *whichItem, TkMenu *menuPtr);
static void HandleMenuCalcItemMsg(MenuRef menu, Rect *menuRectPtr, Point hitPt,
	SInt16 *whichItem, TkMenu *menuPtr);
static void AppearanceEntryDrawWrapper(TkMenuEntry *mePtr, Rect * menuRectPtr,
	MenuTrackingData *mtdPtr, Drawable d, Tk_FontMetrics *fmPtr,
	Tk_Font tkfont, int erase);
static pascal void ThemeMenuItemDrawingProc(const Rect *inBounds,
	SInt16 inDepth, Boolean inIsColorDevice, SInt32 inUserData);
#else /* USE_TK_MDEF */
#   define useMDEF 0
#endif /* USE_TK_MDEF */

#define IS_THEME_MENU_FONT(tkfont) (strcmp(Tk_NameOfFont(tkfont), "menu") == 0)


/*
 *----------------------------------------------------------------------
 *
 * DrawThemeText --
 *
 *	Wrapper for DrawThemeTextBox API.
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
DrawThemeText(
    Drawable d,
    GC gc,
    CFStringRef string,
    ThemeFontID font,
    ThemeDrawState drawState,
    const Rect* bounds,
    int baseline,
    int just)
{
    TkMacOSXDrawingContext dc;
    Rect adjustedBounds;

    /*
     * Menu item text drawn with the .Keyboard font (used for
     * kThemeMenuItemCmdKeyFont) won't always have the same ascent and
     * baseline as text drawn with the regular menu item font, since the
     * glyphs in the .Keyboard font may have a different height. Therefore, we
     * first determine the baseline of the text and then adjust the bounds
     * rect so the baseline aligns with the overall baseline of the menu item.
     */
    if (font == kThemeMenuItemCmdKeyFont) {
	Point size;
	SInt16 cmdKeyBaseline;

	GetThemeTextDimensions(string, font, drawState, false, &size,
		&cmdKeyBaseline);
	adjustedBounds = *bounds;
	OffsetRect(&adjustedBounds, 0, baseline - bounds->top - size.v -
		cmdKeyBaseline);
	bounds = &adjustedBounds;
    }
    if (TkMacOSXSetupDrawingContext(d, gc, 1, &dc)) {
	ChkErr(DrawThemeTextBox, string, font, drawState, false, bounds, just,
		dc.context);
	TkMacOSXRestoreDrawingContext(&dc);
    }
}

/*
 *----------------------------------------------------------------------
 *
 * MeasureThemeText --
 *
 *	Wrapper for GetThemeTextDimensions API.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */

static int
MeasureThemeText(
    CFStringRef string,
    ThemeFontID font)
{
    Point pt;

    ChkErr(GetThemeTextDimensions, string, font, kThemeStateActive, false, &pt,
	NULL);
    return pt.h;
}

/*
 *----------------------------------------------------------------------
 *
 * TkMacOSXUseID --
 *
 *	Take the ID out of the available list for new menus. Used by the
 *	default menu bar's menus so that they do not get created at the tk
 *	level. See TkMacOSXGetNewMenuID for more information.
 *
 * Results:
 *	Returns TCL_OK if the id was not in use. Returns TCL_ERROR if the
 *	id was in use.
 *
 * Side effects:
 *	A hash table entry in the command table is created with a NULL
 *	value.
 *
 *----------------------------------------------------------------------
 */

int
TkMacOSXUseMenuID(
    short macID)		/* The id to take out of the table */
{
    Tcl_HashEntry *commandEntryPtr;
    int newEntry;
    int iMacID = macID; /* Do this to remove compiler warning */

    TkMenuInit();
    commandEntryPtr = Tcl_CreateHashEntry(&commandTable, (char *) iMacID,
	    &newEntry);
    if (!newEntry) {
	return TCL_ERROR;
    }
    Tcl_SetHashValue(commandEntryPtr, NULL);
    return TCL_OK;
}

/*
 *----------------------------------------------------------------------
 *
 * TkMacOSXGetNewMenuID --
 *
 *	Allocates a new menu id and marks it in use. Each menu on the
 *	mac must be designated by a unique id, which is a short. In
 *	addition, some ids are reserved by the system. Since Tk uses
 *	mostly dynamic menus, we must allocate and free these ids on
 *	the fly. We use the id as a key into a hash table; if there
 *	is no hash entry, we know that we can use the id.
 *
 *	Carbon allows a much larger number of menus than the old APIs.
 *	I believe this is 32768, but am not sure. This code just uses
 *	2000 as the upper limit. Unfortunately tk leaks menus when
 *	cloning, under some circumstances (see bug on sourceforge).
 *
 * Results:
 *	Returns TCL_OK if succesful; TCL_ERROR if there are no more
 *	ids of the appropriate type to allocate. menuIDPtr contains
 *	the new id if succesful.
 *
 * Side effects:
 *	An entry is created for the menu in the command hash table,
 *	and the hash entry is stored in the appropriate field in the
 *	menu data structure.
 *
 *----------------------------------------------------------------------
 */

int
 TkMacOSXGetNewMenuID(
    Tcl_Interp *interp,		/* Used for error reporting */
    TkMenu *menuPtr,		/* The menu we are working with */
    int cascade,		/* 0 if we are working with a normal menu;
				 * 1 if we are working with a cascade */
    short *menuIDPtr)		/* The resulting id */
{
    int found = 0;
    int newEntry;
    Tcl_HashEntry *commandEntryPtr = NULL;
    short returnID = *menuIDPtr;

    /*
     * The following code relies on shorts and unsigned chars wrapping
     * when the highest value is incremented. Also, the values between
     * 236 and 255 inclusive are reserved for DA's by the Mac OS.
     */

    if (!cascade) {
	short curID = lastMenuID + 1;

	if (curID == 236) {
	    curID = 256;
	}

	while (curID != lastMenuID) {
	    int iCurID = curID;
	    commandEntryPtr = Tcl_CreateHashEntry(&commandTable,
		    (char *) iCurID, &newEntry);
	    if (newEntry == 1) {
		found = 1;
		lastMenuID = returnID = curID;
		break;
	    }
	    curID++;
	    if (curID == 236) {
		curID = 256;
	    }
	}
    } else {
	/*
	 * Cascade ids must be between 0 and 235 only, so they must be
	 * dealt with separately.
	 */

	short curID = lastCascadeID + 1;

	if (curID == 2000) {
	    curID = 0;
	}

	while (curID != lastCascadeID) {
	    int iCurID = curID;
	    commandEntryPtr = Tcl_CreateHashEntry(&commandTable,
		    (char *) iCurID, &newEntry);
	    if (newEntry == 1) {
		found = 1;
		lastCascadeID = returnID = curID;
		break;
	    }
	    curID++;
	    if (curID == 2000) {
		curID = 0;
	    }
	}
    }

    if (!found) {
	Tcl_ResetResult(interp);
	Tcl_AppendResult(interp, "No more menus can be allocated.", NULL);
	return TCL_ERROR;
    }
    Tcl_SetHashValue(commandEntryPtr, (char *) menuPtr);
    *menuIDPtr = returnID;
    return TCL_OK;
}

/*
 *----------------------------------------------------------------------
 *
 * TkMacOSXFreeMenuID --
 *
 *	Marks the id as free.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	The hash table entry for the ID is cleared.
 *
 *----------------------------------------------------------------------
 */

void
TkMacOSXFreeMenuID(
    short menuID)		/* The id to free */
{
    Tcl_HashEntry *entryPtr = Tcl_FindHashEntry(&commandTable,
	    (char*)(intptr_t)menuID);

    if (entryPtr != NULL) {
	 Tcl_DeleteHashEntry(entryPtr);
    }
    if (menuID == currentAppleMenuID) {
	currentAppleMenuID = 0;
    }
    if (menuID == currentHelpMenuID) {
	currentHelpMenuID = 0;
    }
}

/*
 *----------------------------------------------------------------------
 *
 * MenuPtrForMenuRef --
 *
 *	Returns a pointer to the TkMenu corresponding to a given
 *	Carbon MenuRef.
 *
 * Results:
 *	Returns a pointer to a TkMenu or NULL.
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */

TkMenu*
MenuPtrForMenuRef(
    MenuRef menu)
{
    TkMenu *menuPtr = NULL;
    MenuID menuID = GetMenuID(menu);
    Tcl_HashEntry *commandEntryPtr = Tcl_FindHashEntry(&commandTable,
	    (char*)(intptr_t)menuID);

    if (commandEntryPtr) {
	menuPtr = (TkMenu *) Tcl_GetHashValue(commandEntryPtr);
    }
    return menuPtr;
}

/*
 *----------------------------------------------------------------------
 *
 * GetParentMenuEntry --
 *
 *	Returns a pointer to the parent's TkMenuEntry of a given TkMenu.
 *
 * Results:
 *	Returns a pointer to a TkMenuEntry or NULL.
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */

TkMenuEntry*
GetParentMenuEntry(
    TkMenu *menuPtr)
{
    TkMenuEntry *cascadeEntryPtr;

    for (cascadeEntryPtr = menuPtr->menuRefPtr->parentEntryPtr;
	    cascadeEntryPtr != NULL;
	    cascadeEntryPtr = cascadeEntryPtr->nextCascadePtr) {
	const char *name = (cascadeEntryPtr->namePtr == NULL) ? ""
		: Tcl_GetString(cascadeEntryPtr->namePtr);

	if (strcmp(name, Tk_PathName(menuPtr->tkwin)) == 0) {
	    break;
	}
    }
    return cascadeEntryPtr;
}

/*
 *----------------------------------------------------------------------
 *
 * TkpNewMenu --
 *
 *	Gets a new blank menu. Only the platform specific options are filled
 *	in.
 *
 * Results:
 *	Returns a standard TCL error.
 *
 * Side effects:
 *	Allocates a Macintosh menu handle and puts in the platformData
 *	field of the menuPtr.
 *
 *----------------------------------------------------------------------
 */

int
TkpNewMenu(
    TkMenu *menuPtr)		/* The common structure we are making the
				 * platform structure for. */
{
    short menuID;
    MenuRef macMenuHdl;
#ifdef USE_TK_MDEF
    MenuDefSpec menuDefSpec;
    Tcl_Obj *useMDEFObjPtr;
    int useMDEF = 1;
#endif
    int error = TCL_OK;
    OSStatus err;
    CFStringRef cfStr;

    error = TkMacOSXGetNewMenuID(menuPtr->interp, menuPtr, 0, &menuID);
    if (error != TCL_OK) {
	return error;
    }
    err = ChkErr(CreateNewMenu, menuID, kMenuAttrDoNotUseUserCommandKeys,
	    &macMenuHdl);
    if (err != noErr) {
	Tcl_AppendResult(menuPtr->interp, "CreateNewMenu failed.", NULL);
	return TCL_ERROR;
    }
    cfStr = CFStringCreateWithCString(NULL, Tk_PathName(menuPtr->tkwin),
	    kCFStringEncodingUTF8);
    if (!cfStr) {
	Tcl_AppendResult(menuPtr->interp, "CFStringCreateWithCString failed.",
		NULL);
	return TCL_ERROR;
    }
    err = ChkErr(SetMenuTitleWithCFString, macMenuHdl, cfStr);
    CFRelease(cfStr);
    if (err != noErr) {
	Tcl_AppendResult(menuPtr->interp, "SetMenuTitleWithCFString failed.",
		NULL);
	return TCL_ERROR;
    }

    menuPtr->platformData = (TkMenuPlatformData) ckalloc(sizeof(MacMenu));
    ((MacMenu *) menuPtr->platformData)->menuHdl = macMenuHdl;

#ifdef USE_TK_MDEF
    /*
     * Check whether we want to use the custom mdef or not. For now
     * the default is to use it unless the variable is explicitly
     * set to no.
     */

    useMDEFObjPtr = Tcl_ObjGetVar2(menuPtr->interp, useMDEFVar, NULL,
	    TCL_GLOBAL_ONLY);
    if (useMDEFObjPtr == NULL || Tcl_GetBooleanFromObj(NULL, useMDEFObjPtr,
	    &useMDEF) == TCL_ERROR || useMDEF) {
	menuDefSpec.defType = kMenuDefProcPtr;
	menuDefSpec.u.defProc = MenuDefProc;
	ChkErr(SetMenuDefinition, macMenuHdl, &menuDefSpec);
    }
    ((MacMenu *) menuPtr->platformData)->useMDEF = useMDEF;
#endif /* USE_TK_MDEF */

    if ((currentMenuBarInterp == menuPtr->interp)
	    && (currentMenuBarName != NULL)) {
	Tk_Window parentWin = Tk_Parent(menuPtr->tkwin);

	if (strcmp(currentMenuBarName, Tk_PathName(parentWin)) == 0) {
	    if ((strcmp(Tk_PathName(menuPtr->tkwin)
		    + strlen(Tk_PathName(parentWin)), ".apple") == 0)
		    || (strcmp(Tk_PathName(menuPtr->tkwin)
		    + strlen(Tk_PathName(parentWin)), ".help") == 0)) {
		if (!(menuBarFlags & MENUBAR_REDRAW_PENDING)) {
		    Tcl_DoWhenIdle(DrawMenuBarWhenIdle, NULL);
		    menuBarFlags |= MENUBAR_REDRAW_PENDING;
		}
	    }
	}
    }

    menuPtr->menuFlags |= MENU_RECONFIGURE_PENDING;
    Tcl_DoWhenIdle(ReconfigureMacintoshMenu, (ClientData) menuPtr);
    return TCL_OK;
}

/*
 *----------------------------------------------------------------------
 *
 * TkpDestroyMenu --
 *
 *	Destroys platform-specific menu structures.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	All platform-specific allocations are freed up.
 *
 *----------------------------------------------------------------------
 */

void
TkpDestroyMenu(
    TkMenu *menuPtr)		/* The common menu structure */
{
    MenuRef macMenuHdl = ((MacMenu *) menuPtr->platformData)->menuHdl;

    if (menuPtr->menuFlags & MENU_RECONFIGURE_PENDING) {
	Tcl_CancelIdleCall(ReconfigureMacintoshMenu, (ClientData) menuPtr);
	menuPtr->menuFlags &= ~MENU_RECONFIGURE_PENDING;
    }
    if (GetMenuID(macMenuHdl) == currentHelpMenuID) {
	MenuRef helpMenuHdl;
	MenuItemIndex helpIndex;

	if ((HMGetHelpMenu(&helpMenuHdl,&helpIndex) == noErr)
		&& (helpMenuHdl != NULL)) {
	    int i, count = CountMenuItems(helpMenuHdl);

	    for (i = helpIndex; i <= count; i++) {
		DeleteMenuItem(helpMenuHdl, helpIndex);
	    }
	}
	currentHelpMenuID = 0;
    }
    if (menuPtr->platformData != NULL) {
	MenuID menuID = GetMenuID(macMenuHdl);

	DeleteMenu(menuID);
	TkMacOSXFreeMenuID(menuID);
	DisposeMenu(macMenuHdl);
	ckfree((char *) menuPtr->platformData);
	menuPtr->platformData = NULL;
    }
}

/*
 *----------------------------------------------------------------------
 *
 * SetMenuCascade --
 *
 *	Does any cleanup to change a menu from a normal to a cascade.
 *
 * Results:
 *	Standard Tcl error.
 *
 * Side effects:
 *	The mac menu id is reset.
 *
 *----------------------------------------------------------------------
 */

int
SetMenuCascade(
    TkMenu* menuPtr)		/* The menu we are setting up to be a
				 * cascade. */
{
    MenuHandle macMenuHdl = ((MacMenu *) menuPtr->platformData)->menuHdl;
    MenuID newMenuID, menuID = GetMenuID(macMenuHdl);
    int error = TCL_OK;

    if (menuID >= 256) {
	error = TkMacOSXGetNewMenuID(menuPtr->interp, menuPtr, 1, &newMenuID);
	if (error == TCL_OK) {
	    TkMacOSXFreeMenuID(menuID);
	    SetMenuID(macMenuHdl,newMenuID);
	}
    }
    return error;
}

/*
 *----------------------------------------------------------------------
 *
 * TkpDestroyMenuEntry --
 *
 *	Cleans up platform-specific menu entry items.
 *
 * Results:
 *	None
 *
 * Side effects:
 *	All platform-specific allocations are freed up.
 *
 *----------------------------------------------------------------------
 */

void
TkpDestroyMenuEntry(
    TkMenuEntry *mePtr)		/* The common structure for the menu entry. */
{
    TkMenu *menuPtr = mePtr->menuPtr;

    ckfree((char *) mePtr->platformEntryData);
    if ((menuPtr->platformData != NULL)
	    && !(menuPtr->menuFlags & MENU_RECONFIGURE_PENDING)) {
	menuPtr->menuFlags |= MENU_RECONFIGURE_PENDING;
	Tcl_DoWhenIdle(ReconfigureMacintoshMenu, (ClientData) menuPtr);
    }
}

/*
 *----------------------------------------------------------------------
 *
 * GetEntryText --
 *
 *	Given a menu entry, gives back the text that should go in it.
 *	Separators should be done by the caller, as they have to be
 *	handled specially. This is primarily used to do a substitution
 *	between "..." and the ellipsis character which looks nicer.
 *
 * Results:
 *	itemText points to the new text for the item.
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */

void
GetEntryText(
    TkMenuEntry *mePtr,		/* A pointer to the menu entry. */
    Tcl_DString *dStringPtr)	/* The DString to put the text into. This
				 * will be initialized by this routine. */
{
#ifdef USE_TK_MDEF
    const int useMDEF = ((MacMenu *) mePtr->menuPtr->platformData)->useMDEF;
#endif
    int noLabel = (mePtr->labelPtr == NULL || mePtr->labelLength == 0);

    Tcl_DStringInit(dStringPtr);
    if (mePtr->type == TEAROFF_ENTRY && (useMDEF || noLabel)) {
	Tcl_DStringAppend(dStringPtr, "(Tear-off)", -1);
    } else if (mePtr->imagePtr != NULL && (useMDEF || noLabel) &&
	    mePtr->compound == COMPOUND_NONE) {
	Tcl_DStringAppend(dStringPtr, "(Image)", -1);
    } else if (mePtr->bitmapPtr != NULL && (useMDEF || noLabel) &&
	    mePtr->compound == COMPOUND_NONE) {
	Tcl_DStringAppend(dStringPtr, "(Pixmap)", -1);
    } else if (noLabel) {
	/*
	 * The Mac menu manager does not like null strings.
	 */

	Tcl_DStringAppend(dStringPtr, " ", -1);
    } else {
	int length;
	char *text = Tcl_GetStringFromObj(mePtr->labelPtr, &length);
	char *dStringText;
	int i;

	for (i = 0; *text; text++, i++) {
	    if ((*text == '.') && (*(text+1) == '.') && (*(text+2) == '.')) {
		Tcl_DStringAppend(dStringPtr, menuSymbols[ELLIPSIS_SYMBOL].utf,
			menuSymbols[ELLIPSIS_SYMBOL].utfLen);
		i += menuSymbols[ELLIPSIS_SYMBOL].utfLen - 1;
		text += 2;
	    } else {
		Tcl_DStringSetLength(dStringPtr,
			Tcl_DStringLength(dStringPtr) + 1);
		dStringText = Tcl_DStringValue(dStringPtr);
		dStringText[i] = *text;
	    }
	}
    }
}

/*
 *----------------------------------------------------------------------
 *
 * FindMarkCharacter --
 *
 *	Finds the Macintosh mark character based on the font of the
 *	item. We calculate a good mark character based on the font
 *	that this item is rendered in.
 *
 * Results:
 *	Mark char.
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */

char
FindMarkCharacter(
    TkMenuEntry *mePtr)		/* The entry we are finding the character
				 * for. */
{
    static const char markChars[] = {kCheckCharCode, kDiamondCharCode,
	    kBulletCharCode, '-', kCheckCharCode};
    const char *markChar = markChars;
    int i = sizeof(markChars);
    Tk_Font tkfont;

    tkfont = Tk_GetFontFromObj(mePtr->menuPtr->tkwin,
	    (mePtr->fontPtr == NULL) ? mePtr->menuPtr->fontPtr
	    : mePtr->fontPtr);

    while (--i) {
	if (!TkMacOSXIsCharacterMissing(tkfont, *markChar)) {
	    break;
	}
	markChar++;
    }
    return *markChar;
}

/*
 *----------------------------------------------------------------------
 *
 * GetUtfMarkCharacter --
 *
 *	Get the utf8 string for the given mark character, taking into
 *	account the special menu font char codes.
 *
 * Results:
 *	Length of returned utf8 string.
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */

int
GetUtfMarkCharacter(
    char markChar,
    const char **markUtfPtr)
{
    const MenuSymbol *ms = menuSymbols;
    int len = 0;

    while (ms->unicode) {
	if (ms->charCode && ms->charCode == markChar) {
	    *markUtfPtr = ms->utf;
	    len = ms->utfLen;
	    break;
	}
	ms++;
    }
    if (!len) {
	static char markUtf[TCL_UTF_MAX + 1];

	Tcl_ExternalToUtf(NULL, TkMacOSXCarbonEncoding, &markChar, 1, 0, NULL,
		markUtf, TCL_UTF_MAX + 1, NULL, &len, NULL);
	*markUtfPtr = markUtf;
    }
    return len;
}

/*
 *----------------------------------------------------------------------
 *
 * ParseAccelerators --
 *
 *	Parse menu accelerator string.
 *
 * Results:
 *	Accelerator flags.
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */

int
ParseAccelerators(
    const char **accelStringPtr,
    int *modifierNumPtr,
    Tcl_UniChar *modifierUniChars,
    int *modifierWidth)
{
    struct Modif {
	const char *name;
	const size_t len;
	const int flag, symbol;
    };
#define MODIF(n, f) { #n, sizeof(#n)-1, ENTRY_##f##_ACCEL, f##_SYMBOL }
    static const struct Modif modifs[] = {
	MODIF(Control,	CONTROL),
	MODIF(Ctrl,	CONTROL),
	MODIF(Option,	OPTION),
	MODIF(Opt,	OPTION),
	MODIF(Alt,	OPTION),
	MODIF(Shift,	SHIFT),
	MODIF(Command,	COMMAND),
	MODIF(Cmd,	COMMAND),
	MODIF(Meta,	COMMAND),
	{ NULL, 0, 0, 0}
    };
#undef MODIF
    const char *accelString = *accelStringPtr;
    int flags = 0, num = 0, seen = 0, width = 0;
    const struct Modif *m;

    while (1) {
	m = modifs;
	while (m->name) {
	    int l = m->len;

	    if (!strncasecmp(accelString, m->name, l) &&
		    (accelString[l] == '-' || accelString[l] == '+')) {
		flags |= m->flag;
		accelString += l+1;
		break;
	    }
	    m++;
	}
	if (!m->name || !*accelString) {
	    break;
	}
    }
    m = modifs;
    while (m->name && num < MODIFIER_NUM) {
	if (flags & m->flag && !(seen & m->flag)) {
	    modifierUniChars[num++] = menuSymbols[m->symbol].unicode;
	    width += menuSymbols[m->symbol].width;
	    seen |= m->flag;
	}
	m++;
    }
    *accelStringPtr = accelString;
    *modifierNumPtr = num;
    *modifierWidth = width;
    return flags;
}

/*
 *----------------------------------------------------------------------
 *
 * TkpConfigureMenuEntry --
 *
 *	Processes configurations for menu entries.
 *
 * Results:
 *	Returns standard TCL result. If TCL_ERROR is returned, then
 *	the interp's result contains an error message.
 *
 * Side effects:
 *	Configuration information get set for mePtr; old resources
 *	get freed, if any need it.
 *
 *----------------------------------------------------------------------
 */

int
TkpConfigureMenuEntry(
    TkMenuEntry *mePtr) 	/* Information about menu entry; may
				 * or may not already have values for
				 * some fields. */
{
    TkMenu *menuPtr = mePtr->menuPtr;
    EntryGeometry *geometryPtr = (EntryGeometry *) mePtr->platformEntryData;

    /*
     * Cascade menus have to have menu IDs of less than 256. So
     * we need to change the child menu if this has been configured
     * for a cascade item.
     */

    if (mePtr->type == CASCADE_ENTRY) {
	if ((mePtr->childMenuRefPtr != NULL)
		&& (mePtr->childMenuRefPtr->menuPtr != NULL)) {
	    MenuHandle childMenuHdl = ((MacMenu *) mePtr
		    ->childMenuRefPtr->menuPtr->platformData)->menuHdl;

	    if (childMenuHdl != NULL) {
		int error = SetMenuCascade(mePtr->childMenuRefPtr->menuPtr);

		if (error != TCL_OK) {
		    return error;
		}

		if (menuPtr->menuType == MENUBAR) {
		    CFStringRef cfStr = CFStringCreateWithCString(NULL,
			    (!(mePtr->labelPtr) ? "" :
			    Tcl_GetString(mePtr->labelPtr)),
			    kCFStringEncodingUTF8);

		    if (cfStr) {
			SetMenuTitleWithCFString(childMenuHdl, cfStr);
			CFRelease(cfStr);
		    }
		}
	    }
	}
    }

    /*
     * We need to parse the accelerator string. If it has the strings
     * for Command, Control, Shift or Option, we need to flag it
     * so we can draw the symbols for it. We also need to precalcuate
     * the position of the first real character we are drawing.
     */

    if (0 == mePtr->accelLength) {
	geometryPtr->accelTextStart = -1;
    } else {
	const char *accelString = (mePtr->accelPtr == NULL) ? ""
		: Tcl_GetString(mePtr->accelPtr);
	const char *accelStart = accelString;

	mePtr->entryFlags &= ~ENTRY_ACCEL_MASK;
	mePtr->entryFlags |= ParseAccelerators(&accelString,
		&geometryPtr->modifierNum, geometryPtr->modifierUniChars,
		&geometryPtr->modifierWidth);
	geometryPtr->accelTextStart = (ptrdiff_t)(accelString - accelStart);
    }

    if (!(menuPtr->menuFlags & MENU_RECONFIGURE_PENDING)) {
	menuPtr->menuFlags |= MENU_RECONFIGURE_PENDING;
	Tcl_DoWhenIdle(ReconfigureMacintoshMenu, (ClientData) menuPtr);
    }

    return TCL_OK;
}

/*
 *----------------------------------------------------------------------
 *
 * ReconfigureIndividualMenu --
 *
 *	This routine redoes the guts of the menu. It works from
 *	a base item and offset, so that a regular menu will
 *	just have all of its items added, but the help menu will
 *	have all of its items appended after the apple-defined
 *	items.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	The Macintosh menu handle is updated
 *
 *----------------------------------------------------------------------
 */

void
ReconfigureIndividualMenu(
    TkMenu *menuPtr,		/* The menu we are affecting. */
    MenuHandle macMenuHdl,	/* The macintosh menu we are affecting.
				 * Will not necessarily be
				 * menuPtr->platformData because this could
				 * be the help menu. */
    int base)			/* The last index that we do not want
				 * touched. 0 for normal menus;
				 * # of system help menu items
				 * for help menus. */
{
    int count;
    int index;
    TkMenuEntry *mePtr;
    int parentDisabled = 0;

#ifdef TK_MAC_DEBUG_MENUS
    /*
     * Carbon-internal menu debugging (c.f. Technote 2124)
     */

    TkMacOSXInitNamedDebugSymbol(HIToolbox, void, DebugPrintMenu,
	MenuRef menu);
    if (DebugPrintMenu) {
	DebugPrintMenu(macMenuHdl);
    }
#endif

    mePtr = GetParentMenuEntry(menuPtr);
    if (mePtr && mePtr->state == ENTRY_DISABLED) {
	parentDisabled = 1;
    }

    /*
     * First, we get rid of all of the old items.
     */

    count = CountMenuItems(macMenuHdl);
    for (index = base; index < count; index++) {
	DeleteMenuItem(macMenuHdl, base + 1);
    }

    count = menuPtr->numEntries;

    for (index = 1; index <= count; index++) {
	mePtr = menuPtr->entries[index - 1];

	/*
	 * We have to do separators separately because SetMenuItemText
	 * does not parse meta-characters.
	 */

	if (mePtr->type == SEPARATOR_ENTRY) {
	    AppendMenuItemTextWithCFString(macMenuHdl, NULL,
		    kMenuItemAttrSeparator | kMenuItemAttrDisabled, 0, NULL);
	} else {
	    Tcl_DString itemTextDString;
	    CFStringRef cfStr;

	    GetEntryText(mePtr, &itemTextDString);
	    cfStr = CFStringCreateWithCString(NULL,
		    Tcl_DStringValue(&itemTextDString), kCFStringEncodingUTF8);
	    if (cfStr) {
		AppendMenuItemTextWithCFString(macMenuHdl, cfStr, 0, 0, NULL);
		CFRelease(cfStr);
	    } else {
		AppendMenuItemTextWithCFString(macMenuHdl, CFSTR ("<Error>"),
		    0, 0, NULL);
	    }
	    Tcl_DStringFree(&itemTextDString);

	    /*
	     * Set enabling and disabling correctly.
	     */

	    if (parentDisabled || (mePtr->state == ENTRY_DISABLED)) {
		DisableMenuItem(macMenuHdl, base + index);
	    } else {
		EnableMenuItem(macMenuHdl, base + index);
	    }

	    /*
	     * Set the check mark for check entries and radio entries.
	     */

	    SetItemMark(macMenuHdl, base + index, 0);
	    if ((mePtr->type == CHECK_BUTTON_ENTRY)
		    || (mePtr->type == RADIO_BUTTON_ENTRY)) {
		CheckMenuItem(macMenuHdl, base + index, (mePtr->entryFlags
		& ENTRY_SELECTED) && mePtr->indicatorOn);
		if (mePtr->indicatorOn
			&& (mePtr->entryFlags & ENTRY_SELECTED)) {
		    SetItemMark(macMenuHdl, base + index,
			    FindMarkCharacter(mePtr));
		}
	    }

	    if (mePtr->type == CASCADE_ENTRY) {
		if ((mePtr->childMenuRefPtr != NULL)
			&& (mePtr->childMenuRefPtr->menuPtr != NULL)) {
		    MenuHandle childMenuHdl =
			    ((MacMenu *) mePtr->childMenuRefPtr
			    ->menuPtr->platformData)->menuHdl;

		    if (childMenuHdl != NULL) {
			ChkErr(SetMenuItemHierarchicalID, macMenuHdl,
				base + index, GetMenuID(childMenuHdl));
		    }
		    /*
		     * If we changed the highligthing of this menu, its
		     * children all have to be reconfigured so that
		     * their state will be reflected in the menubar.
		     */

		    if (!(mePtr->childMenuRefPtr->menuPtr->menuFlags
				& MENU_RECONFIGURE_PENDING)) {
			mePtr->childMenuRefPtr->menuPtr->menuFlags
				|= MENU_RECONFIGURE_PENDING;
			Tcl_DoWhenIdle(ReconfigureMacintoshMenu,
				(ClientData) mePtr->childMenuRefPtr->menuPtr);
		    }
		}
	    }

	    if ((mePtr->type != CASCADE_ENTRY) && (mePtr->accelPtr != NULL)) {
		int accelLen, modifiers = 0, hasCmd = 0;
		EntryGeometry *geometryPtr =
			(EntryGeometry*)mePtr->platformEntryData;
		int offset = geometryPtr->accelTextStart;
		char *accel = Tcl_GetStringFromObj(mePtr->accelPtr, &accelLen);

		accelLen -= offset;
		accel += offset;
		if (mePtr->entryFlags & ENTRY_OPTION_ACCEL) {
		    modifiers |= kMenuOptionModifier;
		}
		if (mePtr->entryFlags & ENTRY_SHIFT_ACCEL) {
		    modifiers |= kMenuShiftModifier;
		}
		if (mePtr->entryFlags & ENTRY_CONTROL_ACCEL) {
		    modifiers |= kMenuControlModifier;
		}
		if (mePtr->entryFlags & ENTRY_COMMAND_ACCEL) {
		    hasCmd = 1;
		}
		if (accelLen == 1) {
		    if (hasCmd || (modifiers != 0 && modifiers !=
			    kMenuShiftModifier)) {
			SetItemCmd(macMenuHdl, base + index, accel[0]);
			if (!hasCmd) {
			    modifiers |= kMenuNoCommandModifier;
			}
		    }
		} else {
		    /*
		     * Convert from accelerator names to Carbon menu glyphs.
		     */
		    struct Glyph {
			const char *name;
			const size_t len;
			const char glyph;
		    };
#define GLYPH(n, g) { #n, sizeof(#n)-1, kMenu##g##Glyph }
		    static const struct Glyph glyphs[] = {
			GLYPH(PageUp,	PageUp),
			GLYPH(PageDown, PageDown),
			GLYPH(Left,	LeftArrow),
			GLYPH(Right,	RightArrow),
			GLYPH(Up,	UpArrow),
			GLYPH(Down,	DownArrow),
			GLYPH(Escape,	Escape),
			GLYPH(Clear,	Clear),
			GLYPH(Enter,	Enter),
			GLYPH(Backspace,DeleteLeft),
			GLYPH(Space,	Space),
			GLYPH(Tab,	TabRight),
			GLYPH(Delete,	DeleteRight),
			GLYPH(Home,	NorthwestArrow),
			GLYPH(End,	SoutheastArrow),
			GLYPH(Return,	Return),
			GLYPH(Help,	Help),
			GLYPH(Power,	Power),
			{ NULL, 0, 0}
		    };
#undef GLYPH
		    const struct Glyph *g = glyphs;
		    char glyph = 0;

		    if (accel[0] == 'F' && accelLen < 4 &&
			    (accel[1] > '0' && accel[1] <= '9')) {
			int fkey = accel[1] - '0';

			if (accelLen == 3) {
			    if (accel[2] >= '0' && accel[2] <= '9') {
				fkey = 10 * fkey + (accel[2] - '0');
			    } else {
				fkey = 0;
			    }
			}
			if (fkey >= 1 && fkey <= 12) {
			    glyph = kMenuF1Glyph + fkey - 1;
			} else if (fkey >= 13 && fkey <= 15) {
			    glyph = kMenuF13Glyph + fkey - 13;
			}
		    } else while (g->name) {
			if (accel[0] == g->name[0] &&
				(size_t)accelLen == g->len &&
				!strncasecmp(accel, g->name, g->len)) {
			    glyph = g->glyph;
			    break;
			}
			g++;
		    }
		    if (glyph) {
			ChkErr(SetMenuItemKeyGlyph, macMenuHdl, base + index,
				glyph);
			if (!hasCmd) {
			    modifiers |= kMenuNoCommandModifier;
			}
			geometryPtr->accelGlyph = glyph;
		    }
		}
		ChkErr(SetMenuItemModifiers, macMenuHdl, base + index,
			modifiers);
	    }
	}
    }
}

/*
 *----------------------------------------------------------------------
 *
 * ReconfigureMacintoshMenu --
 *
 *	Rebuilds the Macintosh MenuHandle items from the menu. Called
 *	usually as an idle handler, but can be called synchronously
 *	if the menu is about to be posted.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	Configuration information get set for mePtr; old resources
 *	get freed, if any need it.
 *
 *----------------------------------------------------------------------
 */

void
ReconfigureMacintoshMenu(
    ClientData clientData)	/* Information about menu entry; may
				 * or may not already have values for
				 * some fields. */
{
    TkMenu *menuPtr = (TkMenu *) clientData;
    MenuHandle macMenuHdl = ((MacMenu *) menuPtr->platformData)->menuHdl;
    MenuHandle helpMenuHdl = NULL;

    menuPtr->menuFlags &= ~MENU_RECONFIGURE_PENDING;

    if (NULL == macMenuHdl) {
	return;
    }

    ReconfigureIndividualMenu(menuPtr, macMenuHdl, 0);

    if (GetMenuID(macMenuHdl) == currentHelpMenuID) {
	MenuItemIndex helpIndex;
	HMGetHelpMenu(&helpMenuHdl,&helpIndex);
	if (helpMenuHdl != NULL) {
	    ReconfigureIndividualMenu(menuPtr, helpMenuHdl, helpIndex - 1);
	}
    }

    if (menuPtr->menuType == MENUBAR) {
	if (!(menuBarFlags & MENUBAR_REDRAW_PENDING)) {
	    Tcl_DoWhenIdle(DrawMenuBarWhenIdle, NULL);
	    menuBarFlags |= MENUBAR_REDRAW_PENDING;
	}
    }
}

/*
 *----------------------------------------------------------------------
 *
 * CompleteIdlers --
 *
 *	Completes all idle handling so that the menus are in sync when
 *	the user invokes them with the mouse.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	The Macintosh menu handles are flushed out.
 *
 *----------------------------------------------------------------------
 */

void
CompleteIdlers(
    TkMenu *menuPtr)		/* The menu we are completing. */
{
    int i;

    if (menuPtr->menuFlags & MENU_RECONFIGURE_PENDING) {
	Tcl_CancelIdleCall(ReconfigureMacintoshMenu, (ClientData) menuPtr);
	ReconfigureMacintoshMenu((ClientData) menuPtr);
    }

    for (i = 0; i < menuPtr->numEntries; i++) {
	if ((menuPtr->entries[i]->type == CASCADE_ENTRY) &&
		(menuPtr->entries[i]->childMenuRefPtr != NULL) &&
		(menuPtr->entries[i]->childMenuRefPtr->menuPtr != NULL)) {
	    CompleteIdlers(menuPtr->entries[i]->childMenuRefPtr->menuPtr);
	}
    }
}

/*
 *----------------------------------------------------------------------
 *
 * TkpPostMenu --
 *
 *	Posts a menu on the screen
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	The menu is posted and handled.
 *
 *----------------------------------------------------------------------
 */

int
TkpPostMenu(
    Tcl_Interp *interp,		/* The interpreter this menu lives in */
    TkMenu *menuPtr,		/* The menu we are posting */
    int x,			/* The global x-coordinate of the top, left-
				 * hand corner of where the menu is supposed
				 * to be posted. */
    int y)			/* The global y-coordinate */
{
    MenuHandle macMenuHdl = ((MacMenu *) menuPtr->platformData)->menuHdl;
    long popUpResult;
    int result;

    if (inPostMenu > 0) {
	Tcl_AppendResult(interp,
		"Cannot call post menu while already posting menu", NULL);
	result = TCL_ERROR;
    } else {
	short menuID;
	Window window;
	int oldWidth = menuPtr->totalWidth;

	inPostMenu++;
	result = TkPreprocessMenu(menuPtr);
	/*
	 * The post commands could have deleted the menu, which means
	 * we are dead and should go away.
	 */

	if (result != TCL_OK || !menuPtr->tkwin) {
	    goto endPostMenu;
	}

	CompleteIdlers(menuPtr);
	if (menuBarFlags & MENUBAR_REDRAW_PENDING) {
	    Tcl_CancelIdleCall(DrawMenuBarWhenIdle, NULL);
	    DrawMenuBarWhenIdle(NULL);
	}
	RecursivelyInsertMenu(menuPtr);

	TkMacOSXTrackingLoop(1);
	popUpResult = PopUpMenuSelect(macMenuHdl, y, x, menuPtr->active);
	TkMacOSXTrackingLoop(0);
	menuPtr->totalWidth = oldWidth;

	/*
	 * Simulate the mouse up.
	 */

	window = Tk_WindowId(menuPtr->tkwin);
	TkGenerateButtonEventForXPointer(window);

	/*
	 * Dispatch the command.
	 */

	menuID = HiWord(popUpResult);
	if (menuID != 0) {
	    result = TkMacOSXDispatchMenuEvent(menuID, LoWord(popUpResult));
	}

endPostMenu:
	inPostMenu--;
    }
    return result;
}

/*
 *----------------------------------------------------------------------
 *
 * TkpMenuNewEntry --
 *
 *	Adds a pointer to a new menu entry structure with the platform-
 *	specific fields filled in. The Macintosh uses the
 *	platformEntryData field of the TkMenuEntry record to store
 *	geometry information.
 *
 * Results:
 *	Standard TCL error.
 *
 * Side effects:
 *	Storage gets allocated. New menu entry data is put into the
 *	platformEntryData field of the mePtr.
 *
 *----------------------------------------------------------------------
 */

int
TkpMenuNewEntry(
    TkMenuEntry *mePtr)		/* The menu we are adding an entry to */
{
    EntryGeometry *geometryPtr =
	    (EntryGeometry *) ckalloc(sizeof(EntryGeometry));
    TkMenu *menuPtr = mePtr->menuPtr;

    geometryPtr->accelTextStart = 0;
    geometryPtr->accelTextWidth = 0;
    geometryPtr->nonAccelMargin = 0;
    geometryPtr->modifierWidth = 0;
    geometryPtr->modifierNum = 0;
    geometryPtr->accelGlyph = 0;
    mePtr->platformEntryData = (TkMenuPlatformEntryData) geometryPtr;
    if (!(menuPtr->menuFlags & MENU_RECONFIGURE_PENDING)) {
	menuPtr->menuFlags |= MENU_RECONFIGURE_PENDING;
	Tcl_DoWhenIdle(ReconfigureMacintoshMenu, (ClientData) menuPtr);
    }
    return TCL_OK;
}

/*
 *----------------------------------------------------------------------
 *
 * Tk_MacOSXTurnOffMenus --
 *
 *	Turns off all the menu drawing code. This is more than just disabling
 *	the "menu" command, this means that Tk will NEVER touch the menubar.
 *	It is needed in the Plugin, where Tk does not own the menubar.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	A flag is set which will disable all menu drawing.
 *
 *----------------------------------------------------------------------
 */

void
Tk_MacOSXTurnOffMenus(void)
{
    gNoTkMenus = 1;
}

/*
 *----------------------------------------------------------------------
 *
 * DrawMenuBarWhenIdle --
 *
 *	Update the menu bar next time there is an idle event.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	Menu bar is redrawn.
 *
 *----------------------------------------------------------------------
 */

void
DrawMenuBarWhenIdle(
    ClientData clientData)	/* ignored here */
{
    TkMenuReferences *menuRefPtr;
    TkMenu *appleMenuPtr, *helpMenuPtr, *menuBarPtr = NULL;
    MenuHandle macMenuHdl;
    Tcl_HashEntry *hashEntryPtr;

    /*
     * If we have been turned off, exit.
     */

    if (gNoTkMenus) {
	return;
    }

    /*
     * We need to clear the apple and help menus of any extra items.
     */

    if (currentAppleMenuID != 0) {
	hashEntryPtr = Tcl_FindHashEntry(&commandTable,
		(char*)(intptr_t)currentAppleMenuID);
	appleMenuPtr = (TkMenu *) Tcl_GetHashValue(hashEntryPtr);
	TkpDestroyMenu(appleMenuPtr);
	TkpNewMenu(appleMenuPtr);
	appleMenuPtr->menuFlags &= ~MENU_APPLE_MENU;
	appleMenuPtr->menuFlags |= MENU_RECONFIGURE_PENDING;
	Tcl_DoWhenIdle(ReconfigureMacintoshMenu, (ClientData) appleMenuPtr);
    }

    if (currentHelpMenuID != 0) {
	hashEntryPtr = Tcl_FindHashEntry(&commandTable,
		(char*)(intptr_t)currentHelpMenuID);
	helpMenuPtr = (TkMenu *) Tcl_GetHashValue(hashEntryPtr);
	TkpDestroyMenu(helpMenuPtr);
	TkpNewMenu(helpMenuPtr);
	helpMenuPtr->menuFlags &= ~MENU_HELP_MENU;
	helpMenuPtr->menuFlags |= MENU_RECONFIGURE_PENDING;
	Tcl_DoWhenIdle(ReconfigureMacintoshMenu,
		(ClientData) helpMenuPtr);
    }

    /*
     * We need to find the clone of this menu that is the menubar.
     * Once we do that, for every cascade in the menu, we need to
     * insert the Mac menu in the Mac menubar. Finally, we need
     * to redraw the menubar.
     */

    menuRefPtr = NULL;
    if (currentMenuBarName != NULL) {
	menuRefPtr = TkFindMenuReferences(currentMenuBarInterp,
		currentMenuBarName);
    }
    if (menuRefPtr) {
	TkMenu *menuPtr;
	TkMenu *cascadeMenuPtr;
	char *appleMenuName, *helpMenuName;
	int appleIndex = -1, helpIndex = -1, i;

	menuPtr = menuRefPtr->menuPtr;
	if (menuPtr != NULL) {
	    TkMenuReferences *specialMenuRefPtr;
	    TkMenuEntry *specialEntryPtr;

	    appleMenuName = ckalloc(strlen(currentMenuBarName) + 1 +
		    strlen(".apple") + 1);
	    sprintf(appleMenuName, "%s.apple", Tk_PathName(menuPtr->tkwin));
	    specialMenuRefPtr = TkFindMenuReferences(currentMenuBarInterp,
		    appleMenuName);
	    if ((specialMenuRefPtr != NULL)
		    && (specialMenuRefPtr->menuPtr != NULL)) {
		for (specialEntryPtr = specialMenuRefPtr->parentEntryPtr;
			specialEntryPtr != NULL;
			specialEntryPtr = specialEntryPtr->nextCascadePtr) {
		    if (specialEntryPtr->menuPtr == menuPtr) {
			appleIndex = specialEntryPtr->index;
			break;
		    }
		}
	    }
	    ckfree(appleMenuName);

	    helpMenuName = ckalloc(strlen(currentMenuBarName) + 1 +
		    strlen(".help") + 1);
	    sprintf(helpMenuName, "%s.help", Tk_PathName(menuPtr->tkwin));
	    specialMenuRefPtr = TkFindMenuReferences(currentMenuBarInterp,
		    helpMenuName);
	    if ((specialMenuRefPtr != NULL)
		    && (specialMenuRefPtr->menuPtr != NULL)) {
		for (specialEntryPtr = specialMenuRefPtr->parentEntryPtr;
			specialEntryPtr != NULL;
			specialEntryPtr = specialEntryPtr->nextCascadePtr) {
		    if (specialEntryPtr->menuPtr == menuPtr) {
			helpIndex = specialEntryPtr->index;
			break;
		    }
		}
	    }
	    ckfree(helpMenuName);
	}

	for (menuBarPtr = menuPtr;
		(menuBarPtr != NULL) && (menuBarPtr->menuType != MENUBAR);
		menuBarPtr = menuBarPtr->nextInstancePtr) {
	    /*
	     * Null loop body.
	     */
	}

	if (menuBarPtr) {
	    if (menuBarPtr->tearoff != menuPtr->tearoff) {
		if (menuBarPtr->tearoff) {
		    appleIndex = (-1 == appleIndex) ? appleIndex
			    : appleIndex + 1;
		    helpIndex = (-1 == helpIndex) ? helpIndex
			    : helpIndex + 1;
		} else {
		    appleIndex = (-1 == appleIndex) ? appleIndex
			    : appleIndex - 1;
		    helpIndex = (-1 == helpIndex) ? helpIndex
			    : helpIndex - 1;
		}
	    }
	    ClearMenuBar();

	    if (appleIndex == -1) {
		InsertMenu(tkAppleMenu, 0);
		currentAppleMenuID = 0;
		tkCurrentAppleMenu = tkAppleMenu;
	    } else {
		short appleID;

		appleMenuPtr = menuBarPtr->entries[appleIndex]
			->childMenuRefPtr->menuPtr;
		TkpDestroyMenu(appleMenuPtr);
		TkMacOSXGetNewMenuID(appleMenuPtr->interp, appleMenuPtr, 0,
			&appleID);
		macMenuHdl = NewMenu(appleID, "\p\024");
		appleMenuPtr->platformData =
			(TkMenuPlatformData) ckalloc(sizeof(MacMenu));
		((MacMenu *)appleMenuPtr->platformData)->menuHdl
			= macMenuHdl;
		appleMenuPtr->menuFlags |= MENU_APPLE_MENU;
		if (!(appleMenuPtr->menuFlags
			& MENU_RECONFIGURE_PENDING)) {
		    appleMenuPtr->menuFlags |= MENU_RECONFIGURE_PENDING;
		    Tcl_DoWhenIdle(ReconfigureMacintoshMenu,
			    (ClientData) appleMenuPtr);
		}
		InsertMenu(macMenuHdl, 0);
		RecursivelyInsertMenu(appleMenuPtr);
		currentAppleMenuID = appleID;
		tkCurrentAppleMenu = macMenuHdl;
	    }
	    if (helpIndex == -1) {
		currentHelpMenuID = 0;
	    }

	    for (i = 0; i < menuBarPtr->numEntries; i++) {
		if (i == appleIndex) {
		    if (menuBarPtr->entries[i]->state == ENTRY_DISABLED) {
			DisableMenuItem(((MacMenu *) menuBarPtr->entries[i]
				->childMenuRefPtr->menuPtr
				->platformData)->menuHdl, 0);
		    } else {
			EnableMenuItem(((MacMenu *) menuBarPtr->entries[i]
				->childMenuRefPtr->menuPtr
				->platformData)->menuHdl, 0);
		    }
		    continue;
		} else if (i == helpIndex) {
		    TkMenu *helpMenuPtr = menuBarPtr->entries[i]
			    ->childMenuRefPtr->menuPtr;

		    if (helpMenuPtr == NULL) {
			continue;
		    }
		    helpMenuPtr->menuFlags |= MENU_HELP_MENU;
		    if (!(helpMenuPtr->menuFlags
			    & MENU_RECONFIGURE_PENDING)) {
			helpMenuPtr->menuFlags
				|= MENU_RECONFIGURE_PENDING;
			Tcl_DoWhenIdle(ReconfigureMacintoshMenu,
				(ClientData) helpMenuPtr);
		    }
		    macMenuHdl =
			    ((MacMenu *) helpMenuPtr->platformData)->menuHdl;
		    currentHelpMenuID = GetMenuID(macMenuHdl);
		} else if (menuBarPtr->entries[i]->type
			== CASCADE_ENTRY) {
		    if ((menuBarPtr->entries[i]->childMenuRefPtr != NULL)
			    && menuBarPtr->entries[i]->childMenuRefPtr
			    ->menuPtr != NULL) {
			cascadeMenuPtr = menuBarPtr->entries[i]
				->childMenuRefPtr->menuPtr;
			macMenuHdl = ((MacMenu *) cascadeMenuPtr
				->platformData)->menuHdl;
			DeleteMenu(GetMenuID(macMenuHdl));
			InsertMenu(macMenuHdl, 0);
			RecursivelyInsertMenu(cascadeMenuPtr);
			if (menuBarPtr->entries[i]->state == ENTRY_DISABLED) {
			    DisableMenuItem(((MacMenu *) menuBarPtr->entries[i]
				    ->childMenuRefPtr->menuPtr
				    ->platformData)->menuHdl, 0);
			} else {
			    EnableMenuItem(((MacMenu *) menuBarPtr->entries[i]
				    ->childMenuRefPtr->menuPtr
				    ->platformData)->menuHdl, 0);
			 }
		    }
		}
	    }
	}
    }
    if (!menuRefPtr || !menuBarPtr) {
	SetDefaultMenubar();
    }
    DrawMenuBar();
    menuBarFlags &= ~MENUBAR_REDRAW_PENDING;
}

/*
 *----------------------------------------------------------------------
 *
 * RecursivelyInsertMenu --
 *
 *	Puts all of the cascades of this menu in the Mac hierarchical list.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	The menubar is changed.
 *
 *----------------------------------------------------------------------
 */

void
RecursivelyInsertMenu(
    TkMenu *menuPtr)		/* All of the cascade items in this menu
				 * will be inserted into the mac menubar. */
{
    int i;
    TkMenu *cascadeMenuPtr;
    MenuHandle macMenuHdl;

    for (i = 0; i < menuPtr->numEntries; i++) {
	if (menuPtr->entries[i]->type == CASCADE_ENTRY) {
	    if ((menuPtr->entries[i]->childMenuRefPtr != NULL) &&
		    (menuPtr->entries[i]->childMenuRefPtr->menuPtr != NULL)) {
		cascadeMenuPtr = menuPtr->entries[i]->childMenuRefPtr->menuPtr;
		macMenuHdl =
			((MacMenu *) cascadeMenuPtr->platformData)->menuHdl;
		InsertMenu(macMenuHdl, -1);
		RecursivelyInsertMenu(cascadeMenuPtr);
	    }
	}
    }
}

/*
 *----------------------------------------------------------------------
 *
 * RecursivelyDeleteMenu --
 *
 *	Takes all of the cascades of this menu out of the Mac hierarchical
 *	list.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	The menubar is changed.
 *
 *----------------------------------------------------------------------
 */

void
RecursivelyDeleteMenu(
    TkMenu *menuPtr)		/* All of the cascade items in this menu
				 * will be deleted from the mac menubar. */
{
    int i;
    TkMenu *cascadeMenuPtr;
    MenuHandle macMenuHdl;

    for (i = 0; i < menuPtr->numEntries; i++) {
	if (menuPtr->entries[i]->type == CASCADE_ENTRY) {
	    if ((menuPtr->entries[i]->childMenuRefPtr != NULL) &&
		    (menuPtr->entries[i]->childMenuRefPtr->menuPtr != NULL)) {
		cascadeMenuPtr = menuPtr->entries[i]->childMenuRefPtr->menuPtr;
		macMenuHdl =
			((MacMenu *) cascadeMenuPtr->platformData)->menuHdl;
		DeleteMenu(GetMenuID(macMenuHdl));
		RecursivelyDeleteMenu(cascadeMenuPtr);
	    }
	}
    }
}

/*
 *----------------------------------------------------------------------
 *
 * SetDefaultMenubar --
 *
 *	Puts the Apple, File and Edit menus into the Macintosh menubar.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	The menubar is changed.
 *
 *----------------------------------------------------------------------
 */

void
SetDefaultMenubar(void)
{
    if (currentMenuBarName != NULL) {
	ckfree(currentMenuBarName);
	currentMenuBarName = NULL;
    }
    currentMenuBarOwner = NULL;
    ClearMenuBar();
    InsertMenu(tkAppleMenu, 0);
    InsertMenu(tkFileMenu, 0);
    InsertMenu(tkEditMenu, 0);
    if (!(menuBarFlags & MENUBAR_REDRAW_PENDING)) {
	Tcl_DoWhenIdle(DrawMenuBarWhenIdle, NULL);
	menuBarFlags |= MENUBAR_REDRAW_PENDING;
    }
}

/*
 *----------------------------------------------------------------------
 *
 * TkpSetMainMenubar --
 *
 *	Puts the menu associated with a window into the menubar. Should
 *	only be called when the window is in front.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	The menubar is changed.
 *
 *----------------------------------------------------------------------
 */

void
TkpSetMainMenubar(
    Tcl_Interp *interp,		/* The interpreter of the application */
    Tk_Window tkwin,		/* The frame we are setting up */
    char *menuName)		/* The name of the menu to put in front.
				 * If NULL, use the default menu bar.
				 */
{
    TkWindow *winPtr = (TkWindow *) tkwin;
    WindowRef macWindowPtr;
    WindowRef frontNonFloating;

    macWindowPtr = TkMacOSXDrawableWindow(winPtr->window);

    frontNonFloating = ActiveNonFloatingWindow();
    if ((macWindowPtr == NULL) || (macWindowPtr != frontNonFloating)) {
	return;
    }

    if ((currentMenuBarInterp != interp) || (currentMenuBarOwner != tkwin)
	    || (currentMenuBarName == NULL) || (menuName == NULL)
	    || (strcmp(menuName, currentMenuBarName) != 0)) {
	Tk_Window searchWindow;
	TopLevelMenubarList *listPtr;

	if (currentMenuBarName != NULL) {
	    ckfree(currentMenuBarName);
	}

	if (menuName == NULL) {
	    searchWindow = tkwin;
	    if (strcmp(Tk_Class(searchWindow), "Menu") == 0) {
		TkMenuReferences *menuRefPtr;

		menuRefPtr = TkFindMenuReferences(interp, Tk_PathName(tkwin));
		if (menuRefPtr != NULL) {
		    TkMenu *menuPtr = menuRefPtr->menuPtr;

		    if (menuPtr != NULL) {
			searchWindow = menuPtr->masterMenuPtr->tkwin;
		    }
		}
	    }
	    for (; searchWindow != NULL;
		    searchWindow = Tk_Parent(searchWindow)) {
		for (listPtr = windowListPtr; listPtr != NULL;
			listPtr = listPtr->nextPtr) {
		    if (listPtr->tkwin == searchWindow) {
			break;
		    }
		}
		if (listPtr != NULL) {
		    menuName = Tk_PathName(
			    listPtr->menuPtr->masterMenuPtr->tkwin);
		    break;
		}
	    }
	}

	if (menuName == NULL) {
	    currentMenuBarName = NULL;
	} else {
	    currentMenuBarName = ckalloc(strlen(menuName) + 1);
	    strcpy(currentMenuBarName, menuName);
	}
	currentMenuBarOwner = tkwin;
	currentMenuBarInterp = interp;
    }
    if (!(menuBarFlags & MENUBAR_REDRAW_PENDING)) {
	Tcl_DoWhenIdle(DrawMenuBarWhenIdle, NULL);
	menuBarFlags |= MENUBAR_REDRAW_PENDING;
    }
}

/*
 *----------------------------------------------------------------------
 *
 * TkpSetWindowMenuBar --
 *
 *	Associates a given menu with a window.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	On Windows and UNIX, associates the platform menu with the
 *	platform window.
 *
 *----------------------------------------------------------------------
 */

void
TkpSetWindowMenuBar(
    Tk_Window tkwin,		/* The window we are setting the menu in */
    TkMenu *menuPtr)		/* The menu we are setting */
{
    TopLevelMenubarList *listPtr, *prevPtr;

    /*
     * Remove any existing reference to this window.
     */

    for (prevPtr = NULL, listPtr = windowListPtr;
	    listPtr != NULL;
	    prevPtr = listPtr, listPtr = listPtr->nextPtr) {
	if (listPtr->tkwin == tkwin) {
	    break;
	}
    }

    if (listPtr != NULL) {
	if (prevPtr != NULL) {
	    prevPtr->nextPtr = listPtr->nextPtr;
	} else {
	    windowListPtr = listPtr->nextPtr;
	}
	ckfree((char *) listPtr);
    }

    if (menuPtr != NULL) {
	listPtr = (TopLevelMenubarList *) ckalloc(sizeof(TopLevelMenubarList));
	listPtr->nextPtr = windowListPtr;
	windowListPtr = listPtr;
	listPtr->tkwin = tkwin;
	listPtr->menuPtr = menuPtr;
    }
}

/*
 *----------------------------------------------------------------------
 *
 * EventuallyInvokeMenu --
 *
 *	This IdleTime callback actually invokes the menu command
 *	scheduled in TkMacOSXDispatchMenuEvent.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	Commands get executed.
 *
 *----------------------------------------------------------------------
 */

void
EventuallyInvokeMenu (
    ClientData data)
{
    struct MenuCommandHandlerData *realData =
	    (struct MenuCommandHandlerData *) data;
    int code;

    code = TkInvokeMenu(realData->menuPtr->interp, realData->menuPtr,
	    realData->index);

    if (code != TCL_OK && code != TCL_CONTINUE && code != TCL_BREAK) {
	Tcl_AddErrorInfo(realData->menuPtr->interp, "\n    (menu invoke)");
	Tcl_BackgroundError(realData->menuPtr->interp);
    }

    if (realData->menuPtr->tkwin) {
	RecursivelyClearActiveMenu(realData->menuPtr);
    }
    TkMacOSXClearMenubarActive();

    Tcl_Release(realData->menuPtr->interp);
    Tcl_Release(realData->menuPtr);
}

/*
 *----------------------------------------------------------------------
 *
 * TkMacOSXDispatchMenuEvent --
 *
 *	Given a menu id and an item, dispatches the command associated
 *	with it.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	Commands for the event are scheduled for execution at idle time.
 *
 *----------------------------------------------------------------------
 */

int
TkMacOSXDispatchMenuEvent(
    int menuID,			/* The menu id of the menu we are invoking */
    int index)			/* The one-based index of the item that was
				 * selected. */
{
    int result = TCL_OK;

    if (menuID != 0) {
	if (menuID == kHMHelpMenuID) {
	    if (currentMenuBarOwner != NULL) {
		TkMenuReferences *helpMenuRef;
		char *helpMenuName = ckalloc(strlen(currentMenuBarName)
			+ strlen(".help") + 1);

		sprintf(helpMenuName, "%s.help", currentMenuBarName);
		helpMenuRef = TkFindMenuReferences(currentMenuBarInterp,
			helpMenuName);
		ckfree(helpMenuName);
		if ((helpMenuRef != NULL) && (helpMenuRef->menuPtr != NULL)) {
		    MenuRef outHelpMenu;
		    MenuItemIndex itemIndex;
		    int newIndex;

		    HMGetHelpMenu(&outHelpMenu, &itemIndex);
		    newIndex = index - itemIndex;
		    result = TkInvokeMenu(currentMenuBarInterp,
			    helpMenuRef->menuPtr, newIndex);
		}
	    }
	} else {
	    Tcl_HashEntry *commandEntryPtr =
		    Tcl_FindHashEntry(&commandTable, (char*)(intptr_t)menuID);
	    if (commandEntryPtr != NULL) {
		TkMenu *menuPtr = (TkMenu *) Tcl_GetHashValue(commandEntryPtr);

		if ((currentAppleMenuID == menuID)
			&& (index > menuPtr->numEntries + 1)) {
		    /*
		     * We don't need to do anything here, the standard
		     * Application event handler will open the built-in
		     * Apple menu item for us.
		     */
		    result = TCL_OK;
		} else {
		    struct MenuCommandHandlerData *data
			    = (struct MenuCommandHandlerData *)
			    ckalloc(sizeof(struct MenuCommandHandlerData));

		    Tcl_Preserve(menuPtr->interp);
		    Tcl_Preserve(menuPtr);
		    data->menuPtr = menuPtr;
		    data->index = index - 1;
		    Tcl_DoWhenIdle(EventuallyInvokeMenu,
			    (ClientData) data);
		    /* result = TkInvokeMenu(menuPtr->interp, menuPtr, index - 1); */
		}
	    } else {
		return TCL_ERROR;
	    }
	}
    }
    return result;
}

/*
 *----------------------------------------------------------------------
 *
 * GetMenuIndicatorGeometry --
 *
 *	Gets the width and height of the indicator area of a menu.
 *
 * Results:
 *	widthPtr and heightPtr are set.
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */

void
GetMenuIndicatorGeometry (
    TkMenu *menuPtr,		/* The menu we are drawing */
    TkMenuEntry *mePtr,		/* The entry we are measuring */
    Tk_Font tkfont,		/* Precalculated font */
    const Tk_FontMetrics *fmPtr,/* Precalculated font metrics */
    int *widthPtr,		/* The resulting width */
    int *heightPtr)		/* The resulting height */
{
    *heightPtr = fmPtr->linespace + menuItemExtraHeight;
    if (IS_THEME_MENU_FONT(tkfont)) {
	*widthPtr = menuMarkColumnWidth;
    } else {
	const char markChar = FindMarkCharacter(mePtr);
	const char *markUtf = NULL;
	int len;

	len = GetUtfMarkCharacter(markChar, &markUtf);
	*widthPtr = Tk_TextWidth(tkfont, markUtf, len) + 2*menuMarkIndent;
    }
}

/*
 *----------------------------------------------------------------------
 *
 * GetMenuAccelGeometry --
 *
 *	Gets the width and height of the accelerator area of a menu.
 *
 * Results:
 *	widthPtr and heightPtr are set.
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */

void
GetMenuAccelGeometry (
    TkMenu *menuPtr,		/* The menu we are measuring */
    TkMenuEntry *mePtr,		/* The entry we are measuring */
    Tk_Font tkfont,		/* The precalculated font */
    const Tk_FontMetrics *fmPtr,/* The precalculated font metrics */
    int *modWidthPtr,		/* The width of all of the key
				 * modifier symbols. */
    int *textWidthPtr,		/* The resulting width */
    int *heightPtr)		/* The resulting height */
{
    *heightPtr = fmPtr->linespace + menuItemExtraHeight;
    *modWidthPtr = menuSymbols[COMMAND_SYMBOL].width;
    *textWidthPtr = 0;
    if (mePtr->type != CASCADE_ENTRY && mePtr->accelLength > 0) {
	const char *accel = (mePtr->accelPtr == NULL) ? ""
		: Tcl_GetString(mePtr->accelPtr);
	EntryGeometry *geometryPtr = (EntryGeometry*)mePtr->platformEntryData;

	if (IS_THEME_MENU_FONT(tkfont)) {
	    CFStringRef cfStr;
	    int width = 0;
	    int maxWidth = ((TkFont *)tkfont)->fm.maxWidth;

	    if (geometryPtr->accelGlyph) {
		cfStr = CFStringCreateWithBytes(NULL,
			(UInt8*)&geometryPtr->accelGlyph, 1,
			kTextEncodingMacKeyboardGlyphs, false);
		if (cfStr) {
		    width = MeasureThemeText(cfStr, kThemeMenuItemCmdKeyFont);
		    CFRelease(cfStr);
		}
	    }
	    if ((mePtr->entryFlags & ENTRY_ACCEL_MASK) == 0) {
		if (!geometryPtr->accelGlyph) {
		     width = Tk_TextWidth(tkfont, accel, mePtr->accelLength);
		 }
		*textWidthPtr = maxWidth;
		if (width < maxWidth) {
		    *modWidthPtr = 0;
		} else {
		    *modWidthPtr = width - maxWidth;
		}
	    } else {
		if (!geometryPtr->accelGlyph) {
		    width = Tk_TextWidth(tkfont, accel +
			    geometryPtr->accelTextStart, mePtr->accelLength -
			    geometryPtr->accelTextStart);
		}
		if (width < maxWidth) {
		    *textWidthPtr = maxWidth;
		} else {
		    *textWidthPtr = width;
		}
		if (geometryPtr->modifierNum) {
		    *modWidthPtr = geometryPtr->modifierWidth;
		}
	    }
	} else {
	    *textWidthPtr = Tk_TextWidth(tkfont, accel, mePtr->accelLength);
	}
    }
}

/*
 *----------------------------------------------------------------------
 *
 * GetTearoffEntryGeometry --
 *
 *	Gets the width and height of of a tearoff entry.
 *
 * Results:
 *	widthPtr and heightPtr are set.
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */

void
GetTearoffEntryGeometry (
    TkMenu *menuPtr,		/* The menu we are drawing */
    TkMenuEntry *mePtr,		/* The entry we are measuring */
    Tk_Font tkfont,		/* The precalculated font */
    const Tk_FontMetrics *fmPtr,/* The precalculated font metrics */
    int *widthPtr,		/* The resulting width */
    int *heightPtr)		/* The resulting height */
{
#ifdef USE_TK_MDEF
    const int useMDEF = ((MacMenu *) menuPtr->platformData)->useMDEF;
#endif
    if (useMDEF && menuPtr->menuType != TEAROFF_MENU) {
	*heightPtr = fmPtr->linespace + menuItemExtraHeight;
	*widthPtr = menuPtr->totalWidth;
    } else {
	*widthPtr = *heightPtr = 0;
    }
}

/*
 *----------------------------------------------------------------------
 *
 * GetMenuSeparatorGeometry --
 *
 *	Gets the width and height of menu separator.
 *
 * Results:
 *	widthPtr and heightPtr are set.
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */

void
GetMenuSeparatorGeometry(
    TkMenu *menuPtr,		/* The menu we are drawing */
    TkMenuEntry *mePtr,		/* The entry we are measuring */
    Tk_Font tkfont,		/* The precalculated font */
    const Tk_FontMetrics *fmPtr,/* The precalcualted font metrics */
    int *widthPtr,		/* The resulting width */
    int *heightPtr)		/* The resulting height */
{
    *widthPtr = 0;
    *heightPtr = menuSeparatorHeight;
}

/*
 *----------------------------------------------------------------------
 *
 * DrawMenuEntryIndicator --
 *
 *	This procedure draws the indicator part of a menu.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	Commands are output to X to display the menu in its
 *	current mode.
 *
 *----------------------------------------------------------------------
 */

void
DrawMenuEntryIndicator(
    TkMenu *menuPtr,		/* The menu we are drawing */
    TkMenuEntry *mePtr,		/* The entry we are drawing */
    Drawable d,			/* The drawable we are drawing */
    GC gc,			/* The GC we are drawing with */
    GC indicatorGC,		/* The GC to use for the indicator */
    Tk_Font tkfont,		/* The precalculated font */
    const Tk_FontMetrics *fmPtr,/* The precalculated font metrics */
    int x,			/* topleft hand corner of entry */
    int y,			/* topleft hand corner of entry */
    int width,			/* width of entry */
    int height)			/* height of entry */
{
    if ((mePtr->type == CHECK_BUTTON_ENTRY) ||
	    (mePtr->type == RADIO_BUTTON_ENTRY)) {
	if (mePtr->indicatorOn && (mePtr->entryFlags & ENTRY_SELECTED)) {
	    short mark;
	    int baseline = y + (height + fmPtr->ascent - fmPtr->descent)/2;

	    GetItemMark(((MacMenu *) menuPtr->platformData)->menuHdl,
		    mePtr->index + 1, &mark);
	    if (IS_THEME_MENU_FONT(tkfont)) {
		ThemeFontID font = kThemeMenuItemMarkFont;
		TextEncoding encoding = GetApplicationTextEncoding();
		CFStringRef cfStr;
		ThemeDrawState drawState;
		Rect bounds = {y, x + menuMarkIndent, y + height, x + width};

		if (mark < kSpaceCharCode) {
		    font = kThemeMenuItemCmdKeyFont;
		    encoding = kTextEncodingMacKeyboardGlyphs;
		}
		switch (mePtr->state) {
		    case ENTRY_ACTIVE:
			drawState = kThemeStatePressed;
			break;
		    case ENTRY_DISABLED:
			drawState = kThemeStateInactive;
			break;
		    default:
			drawState = kThemeStateActive;
			break;
		}
		cfStr = CFStringCreateWithBytes(NULL, (UInt8*)&mark, 1,
			encoding, false);
		if (cfStr) {
		    DrawThemeText(d, gc, cfStr, font, drawState, &bounds,
			    baseline, teFlushDefault);
		    CFRelease(cfStr);
		}
	    } else if (mark != 0) {
		const char *markUtf = NULL;
		int len;

		len = GetUtfMarkCharacter(mark, &markUtf);
		Tk_DrawChars(menuPtr->display, d, gc, tkfont, markUtf, len,
		    x + menuMarkIndent, baseline);
	    }
	}
    }
}

#ifdef USE_TK_MDEF
/*
 *----------------------------------------------------------------------
 *
 * DrawMenuBackground --
 *
 *	If Appearance is present, draws the Appearance background
 *
 * Results:
 *	Nothing
 *
 * Side effects:
 *	Commands are output to X to display the menu in its
 *	current mode.
 *
 *----------------------------------------------------------------------
 */
void
DrawMenuBackground(
    TkMenu *menuPtr,
    Rect     *menuRectPtr,	/* The menu rect */
    Drawable d)			/* What we are drawing into */
{
    Tk_3DBorder border;

    EraseMenuBackground(((MacMenu *) menuPtr->platformData)->menuHdl,
	    menuRectPtr, ((MacDrawable*)d)->context);
    border = Tk_Get3DBorderFromObj(menuPtr->tkwin, menuPtr->borderPtr);
    Tk_Fill3DRectangle(menuPtr->tkwin, d, border,
	    menuRectPtr->left, menuRectPtr->top,
	    menuRectPtr->right - menuRectPtr->left,
	    menuRectPtr->bottom - menuRectPtr->top, 0, TK_RELIEF_FLAT);
}
#endif /* USE_TK_MDEF */

/*
 *----------------------------------------------------------------------
 *
 * DrawMenuEntryAccelerator --
 *
 *	This procedure draws the accelerator part of a menu.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	Commands are output to X to display the menu in its
 *	current mode.
 *
 *----------------------------------------------------------------------
 */

void
DrawMenuEntryAccelerator(
    TkMenu *menuPtr,		/* The menu we are drawing */
    TkMenuEntry *mePtr,		/* The entry we are drawing */
    Drawable d,			/* The drawable we are drawing in */
    GC gc,			/* The gc to draw into */
    Tk_Font tkfont,		/* The precalculated font */
    const Tk_FontMetrics *fmPtr,/* The precalculated font metrics */
    Tk_3DBorder activeBorder,	/* border for menu background */
    int x,			/* The left side of the entry */
    int y,			/* The top of the entry */
    int width,			/* The width of the entry */
    int height,			/* The height of the entry */
    int drawArrow)		/* Whether or not to draw cascade arrow */
{
    if (mePtr->type != CASCADE_ENTRY && mePtr->accelLength > 0) {
	const char *accel = (mePtr->accelPtr == NULL) ? ""
		: Tcl_GetString(mePtr->accelPtr);
	EntryGeometry *geometryPtr = (EntryGeometry*)mePtr->platformEntryData;
	int leftEdge = x + width - geometryPtr->accelTextWidth;
	int baseline = y + (height + fmPtr->ascent - fmPtr->descent) / 2;

	if (IS_THEME_MENU_FONT(tkfont)) {
	    CFStringRef cfStr;
	    ThemeDrawState drawState;

	    switch (mePtr->state) {
		case ENTRY_ACTIVE:
		    drawState = kThemeStatePressed;
		    break;
		case ENTRY_DISABLED:
		    drawState = kThemeStateInactive;
		    break;
		default:
		    drawState = kThemeStateActive;
		    break;
	    }
	    if ((mePtr->entryFlags & ENTRY_ACCEL_MASK) == 0) {
		leftEdge -= geometryPtr->modifierWidth;
	    }
	    if (geometryPtr->accelGlyph) {
		Rect bounds = {y, leftEdge, y + height, leftEdge +
			geometryPtr->accelTextWidth};

		cfStr = CFStringCreateWithBytes(NULL,
			(UInt8*)&geometryPtr->accelGlyph, 1,
			kTextEncodingMacKeyboardGlyphs, false);
		if (cfStr) {
		    DrawThemeText(d, gc, cfStr, kThemeMenuItemCmdKeyFont,
			    drawState, &bounds, baseline, teFlushDefault);
		    CFRelease(cfStr);
		}
	    } else {
		Tk_DrawChars(menuPtr->display, d, gc, tkfont, accel + 
			geometryPtr->accelTextStart, mePtr->accelLength -
			geometryPtr->accelTextStart, leftEdge, baseline);
	    }
	    if (geometryPtr->modifierNum) {
		Rect bounds = {y, leftEdge - geometryPtr->modifierWidth,
			y + height, leftEdge};

		cfStr = CFStringCreateWithCharacters(NULL,
			geometryPtr->modifierUniChars,
			geometryPtr->modifierNum);
		if (cfStr) {
		    DrawThemeText(d, gc, cfStr, kThemeMenuItemCmdKeyFont,
			    drawState, &bounds, baseline, teFlushDefault);
		    CFRelease(cfStr);
		}
	    }
	} else {
	    Tk_DrawChars(menuPtr->display, d, gc, tkfont, accel,
		    mePtr->accelLength, leftEdge, baseline);
	}
    }
}

/*
 *----------------------------------------------------------------------
 *
 * DrawMenuSeparator --
 *
 *	The menu separator is drawn.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	Commands are output to X to display the menu in its
 *	current mode.
 *
 *----------------------------------------------------------------------
 */

void
DrawMenuSeparator(
    TkMenu *menuPtr,		/* The menu we are drawing */
    TkMenuEntry *mePtr,		/* The entry we are drawing */
    Drawable d,			/* The drawable we are drawing into */
    GC gc,			/* The gc we are drawing with */
    Tk_Font tkfont,		/* The precalculated font */
    const Tk_FontMetrics *fmPtr,/* The precalculated font metrics */
    int x,			/* left coordinate of entry */
    int y,			/* top coordinate of entry */
    int width,			/* width of entry */
    int height)			/* height of entry */
{
    TkMacOSXDrawingContext dc;
    Rect r;

    r.top = y;
    r.left = x;
    r.bottom = y + height;
    r.right = x + width;
    if (TkMacOSXSetupDrawingContext(d, gc, 1, &dc)) {
	ChkErr(DrawThemeMenuSeparator, &r);
	TkMacOSXRestoreDrawingContext(&dc);
    }
}

#ifdef USE_TK_MDEF
/*
 *----------------------------------------------------------------------
 *
 * AppearanceEntryDrawWrapper --
 *
 *	It routes to the Appearance Managers DrawThemeEntry, which will
 *	then call us back after setting up the drawing context.
 *
 * Results:
 *	A menu entry is drawn
 *
 * Side effects:
 *	None
 *
 *----------------------------------------------------------------------
 */
void
AppearanceEntryDrawWrapper(
    TkMenuEntry *mePtr,
    Rect *menuRectPtr,
    MenuTrackingData *mtdPtr,
    Drawable d,
    Tk_FontMetrics *fmPtr,
    Tk_Font tkfont,
    int erase)
{
    MenuEntryUserData meData;
    Rect itemRect;
    ThemeMenuState theState;
    ThemeMenuItemType theType;
    Tk_FontMetrics entryMetrics;

    meData.mePtr = mePtr;
    meData.mdefDrawable = d;
    if (mePtr->fontPtr == NULL) {
	meData.fmPtr = fmPtr;
	meData.tkfont = tkfont;
    } else {
	meData.tkfont = Tk_GetFontFromObj(mePtr->menuPtr->tkwin,
		mePtr->fontPtr);
	Tk_GetFontMetrics(meData.tkfont, &entryMetrics);
	fmPtr = &entryMetrics;
    }
    itemRect.left = menuRectPtr->left + mePtr->x;
    itemRect.top = mtdPtr->virtualMenuTop + mePtr->y;
    itemRect.right = mePtr->entryFlags & ENTRY_LAST_COLUMN ?
	    menuRectPtr->right : itemRect.left + mePtr->width;
    itemRect.bottom = itemRect.top + mePtr->height;

    if (mePtr->state == ENTRY_ACTIVE) {
	theState = kThemeMenuSelected;
    } else if (mePtr->state == ENTRY_DISABLED) {
	theState = kThemeMenuDisabled;
    } else {
	theState = kThemeMenuActive;
    }
    if (mePtr->type == CASCADE_ENTRY) {
	theType = kThemeMenuItemHierarchical;
    } else {
	theType = kThemeMenuItemPlain;
    }
    if (erase) {
	DisableScreenUpdates();
	DrawMenuBackground(mePtr->menuPtr, &itemRect, d);
    }
    DrawThemeMenuItem(menuRectPtr, &itemRect,
	mtdPtr->virtualMenuTop, mtdPtr->virtualMenuBottom, theState,
	theType | kThemeMenuItemNoBackground, tkThemeMenuItemDrawingUPP,
	(unsigned long) &meData);
    if (erase) {
	EnableScreenUpdates();
    }
}

/*
 *----------------------------------------------------------------------
 *
 * ThemeMenuItemDrawingProc --
 *
 *	This routine is called from the Appearance DrawThemeMenuEntry
 *
 * Results:
 *	A menu entry is drawn
 *
 * Side effects:
 *	None
 *
 *----------------------------------------------------------------------
 */
pascal void
ThemeMenuItemDrawingProc(
    const Rect *inBounds,
    SInt16 inDepth,
    Boolean inIsColorDevice,
    SInt32 inUserData)
{
    MenuEntryUserData *meData = (MenuEntryUserData *) inUserData;

    TkpDrawMenuEntry(meData->mePtr, meData->mdefDrawable, meData->tkfont,
	    meData->fmPtr, inBounds->left, inBounds->top, inBounds->right -
	    inBounds->left + menuItemExtraWidth, inBounds->bottom -
	    inBounds->top + menuItemExtraHeight, 0, 1);
}
#endif /* USE_TK_MDEF */

/*
 *----------------------------------------------------------------------
 *
 * TkMacOSXHandleTearoffMenu() --
 *
 *	This routine sees if the MDEF has set a menu and a mouse position
 *	for tearing off and makes a tearoff menu if it has.
 *
 * Results:
 *	menuPtr->interp will have the result of the tearoff command.
 *
 * Side effects:
 *	A new tearoff menu is created if it is supposed to be.
 *
 *----------------------------------------------------------------------
 */

void
TkMacOSXHandleTearoffMenu(void)
{
    /*
     * Obsolete: Nothing to do.
     */
}

/*
 *--------------------------------------------------------------
 *
 * TkpInitializeMenuBindings --
 *
 *	For every interp, initializes the bindings for Windows
 *	menus. Does nothing on Mac or XWindows.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	C-level bindings are setup for the interp which will
 *	handle Alt-key sequences for menus without beeping
 *	or interfering with user-defined Alt-key bindings.
 *
 *--------------------------------------------------------------
 */

void
TkpInitializeMenuBindings(
    Tcl_Interp *interp,		/* The interpreter to set. */
    Tk_BindingTable bindingTable)
				/* The table to add to. */
{
    /*
     * Nothing to do.
     */
}

/*
 *--------------------------------------------------------------
 *
 * TkpComputeMenubarGeometry --
 *
 *	This procedure is invoked to recompute the size and
 *	layout of a menu that is a menubar clone.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	Fields of menu entries are changed to reflect their
 *	current positions, and the size of the menu window
 *	itself may be changed.
 *
 *--------------------------------------------------------------
 */

void
TkpComputeMenubarGeometry(
    TkMenu *menuPtr)		/* Structure describing menu. */
{
    TkpComputeStandardMenuGeometry(menuPtr);
}

/*
 *----------------------------------------------------------------------
 *
 * DrawTearoffEntry --
 *
 *	This procedure draws a tearoff entry.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	Commands are output to X to display the menu in its
 *	current mode.
 *
 *----------------------------------------------------------------------
 */

void
DrawTearoffEntry(
    TkMenu *menuPtr,		/* The menu we are drawing */
    TkMenuEntry *mePtr,		/* The entry we are drawing */
    Drawable d,			/* The drawable we are drawing into */
    GC gc,			/* The gc we are drawing with */
    Tk_Font tkfont,		/* The font we are drawing with */
    const Tk_FontMetrics *fmPtr,/* The metrics we are drawing with */
    int x,			/* Left edge of entry. */
    int y,			/* Top edge of entry. */
    int width,			/* Width of entry. */
    int height)			/* Height of entry. */
{
    XPoint points[2];
    int margin, segmentWidth, maxX;
    Tk_3DBorder border;

    if (menuPtr->menuType != MASTER_MENU ) {
	return;
    }

    margin = fmPtr->linespace/2;
    points[0].x = x;
    points[0].y = y + height/2;
    points[1].y = points[0].y;
    segmentWidth = 6;
    maxX  = x + menuPtr->totalWidth - 1;
    border = Tk_Get3DBorderFromObj(menuPtr->tkwin, menuPtr->borderPtr);

    while (points[0].x < maxX) {
	points[1].x = points[0].x + segmentWidth;
	if (points[1].x > maxX) {
	    points[1].x = maxX;
	}
	Tk_Draw3DPolygon(menuPtr->tkwin, d, border, points, 2, 1,
		TK_RELIEF_RAISED);
	points[0].x += 2*segmentWidth;
    }
}

/*
 *----------------------------------------------------------------------
 *
 * TkMacOSXSetHelpMenuItemCount --
 *
 *	Has to be called after the first call to InsertMenu. Sets
 *	up the global variable for the number of items in the
 *	unmodified help menu.
 *	NB. Nobody uses this any more, since you can get the number
 *	of system help items from HMGetHelpMenu trivially.
 *	But it is in the stubs table...
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	Nothing.
 *
 *----------------------------------------------------------------------
 */

void
TkMacOSXSetHelpMenuItemCount(void)
{
    /*
     * Obsolete: Nothing to do.
     */
}

/*
 *----------------------------------------------------------------------
 *
 * TkMacOSXMenuClick --
 *
 *	Prepares a menubar for MenuSelect or MenuKey.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	Any pending configurations of the menubar are completed.
 *
 *----------------------------------------------------------------------
 */

void
TkMacOSXMenuClick(void)
{
    TkMenu *menuPtr;
    TkMenuReferences *menuRefPtr;

    if ((currentMenuBarInterp != NULL) && (currentMenuBarName != NULL)) {
	menuRefPtr = TkFindMenuReferences(currentMenuBarInterp,
		currentMenuBarName);
	for (menuPtr = menuRefPtr->menuPtr->masterMenuPtr;
		menuPtr != NULL; menuPtr = menuPtr->nextInstancePtr) {
	    if (menuPtr->menuType == MENUBAR) {
		CompleteIdlers(menuPtr);
		break;
	    }
	}
    }

    if (menuBarFlags & MENUBAR_REDRAW_PENDING) {
	Tcl_CancelIdleCall(DrawMenuBarWhenIdle, NULL);
	DrawMenuBarWhenIdle(NULL);
    }
}

/*
 *----------------------------------------------------------------------
 *
 * TkpDrawMenuEntry --
 *
 *	Draws the given menu entry at the given coordinates with the
 *	given attributes.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	X Server commands are executed to display the menu entry.
 *
 *----------------------------------------------------------------------
 */

void
TkpDrawMenuEntry(
    TkMenuEntry *mePtr,		/* The entry to draw */
    Drawable d,			/* What to draw into */
    Tk_Font tkfont,		/* Precalculated font for menu */
    const Tk_FontMetrics *menuMetricsPtr,
				/* Precalculated metrics for menu */
    int x,			/* X-coordinate of topleft of entry */
    int y,			/* Y-coordinate of topleft of entry */
    int width,			/* Width of the entry rectangle */
    int height,			/* Height of the current rectangle */
    int strictMotif,		/* Boolean flag */
    int drawArrow)		/* Whether or not to draw the cascade
				 * arrow for cascade items. Only applies
				 * to Windows. */
{
    GC gc;
    TkMenu *menuPtr = mePtr->menuPtr;
    int padY = (menuPtr->menuType == MENUBAR) ? 3 : 0;
    GC indicatorGC;
    Tk_3DBorder bgBorder, activeBorder;
    const Tk_FontMetrics *fmPtr;
    Tk_FontMetrics entryMetrics;
    int adjustedY = y + padY;
    int adjustedHeight = height - 2 * padY;

    /*
     * Choose the gc for drawing the foreground part of the entry.
     * Under Appearance, we pass a null (appearanceGC) to tell
     * ourselves not to change whatever color the appearance manager has set.
     */

    if ((mePtr->state == ENTRY_ACTIVE) && !strictMotif) {
	gc = mePtr->activeGC;
	if (gc == NULL) {
	    gc = menuPtr->activeGC;
	}
    } else {
	TkMenuEntry *parentEntryPtr = GetParentMenuEntry(menuPtr);

	if (((parentEntryPtr && parentEntryPtr->state == ENTRY_DISABLED) ||
		(mePtr->state == ENTRY_DISABLED)) &&
		(menuPtr->disabledFgPtr != NULL)) {
	    gc = mePtr->disabledGC;
	    if (gc == NULL) {
		gc = menuPtr->disabledGC;
	    }
	} else {
	    gc = mePtr->textGC;
	    if (gc == NULL) {
		gc = menuPtr->textGC;
	    }
	}
    }

    indicatorGC = mePtr->indicatorGC;
    if (indicatorGC == NULL) {
	indicatorGC = menuPtr->indicatorGC;
    }

    bgBorder = Tk_Get3DBorderFromObj(menuPtr->tkwin,
	    (mePtr->borderPtr == NULL)
	    ? menuPtr->borderPtr : mePtr->borderPtr);
    if (strictMotif) {
	activeBorder = bgBorder;
    } else {
	activeBorder = Tk_Get3DBorderFromObj(menuPtr->tkwin,
	    (mePtr->activeBorderPtr == NULL)
	    ? menuPtr->activeBorderPtr : mePtr->activeBorderPtr);
    }

    if (mePtr->fontPtr == NULL) {
	fmPtr = menuMetricsPtr;
    } else {
	tkfont = Tk_GetFontFromObj(menuPtr->tkwin, mePtr->fontPtr);
	Tk_GetFontMetrics(tkfont, &entryMetrics);
	fmPtr = &entryMetrics;
    }

    /*
     * Need to draw the entire background, including padding. On Unix,
     * for menubars, we have to draw the rest of the entry taking
     * into account the padding.
     */

    DrawMenuEntryBackground(menuPtr, mePtr, d, activeBorder, bgBorder, x, y,
	    width, height);

    if (mePtr->type == SEPARATOR_ENTRY) {
	DrawMenuSeparator(menuPtr, mePtr, d, gc, tkfont,
		fmPtr, x, adjustedY, width, adjustedHeight);
    } else if (mePtr->type == TEAROFF_ENTRY) {
	DrawTearoffEntry(menuPtr, mePtr, d, gc, tkfont, fmPtr, x, adjustedY,
		width, adjustedHeight);
    } else {
	DrawMenuEntryLabel(menuPtr, mePtr, d, gc, tkfont, fmPtr, x,
		adjustedY, width, adjustedHeight);
	DrawMenuEntryAccelerator(menuPtr, mePtr, d, gc, tkfont, fmPtr,
		activeBorder, x, adjustedY, width, adjustedHeight, drawArrow);
	if (!mePtr->hideMargin) {
	    DrawMenuEntryIndicator(menuPtr, mePtr, d, gc, indicatorGC, tkfont,
		    fmPtr, x, adjustedY, width, adjustedHeight);
	}
    }
}

/*
 *--------------------------------------------------------------
 *
 * TkpComputeStandardMenuGeometry --
 *
 *	This procedure is invoked to recompute the size and
 *	layout of a menu that is not a menubar clone.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	Fields of menu entries are changed to reflect their
 *	current positions, and the size of the menu window
 *	itself may be changed.
 *
 *--------------------------------------------------------------
 */

void
TkpComputeStandardMenuGeometry(
    TkMenu *menuPtr)		/* Structure describing menu. */
{
    Tk_Font tkfont, menuFont;
    Tk_FontMetrics menuMetrics, entryMetrics, *fmPtr;
    int x, y, height, modifierWidth, labelWidth, indicatorSpace;
    int windowWidth, windowHeight, accelWidth, maxAccelTextWidth;
    int i, j, lastColumnBreak, maxModifierWidth, maxWidth, nonAccelMargin;
    int maxNonAccelMargin, maxEntryWithAccelWidth, maxEntryWithoutAccelWidth;
    int entryWidth, maxIndicatorSpace, borderWidth, activeBorderWidth;
    TkMenuEntry *mePtr, *columnEntryPtr;
    EntryGeometry *geometryPtr;
    int haveAccel = 0;

    if (menuPtr->tkwin == NULL) {
	return;
    }

    Tk_GetPixelsFromObj(NULL, menuPtr->tkwin, menuPtr->borderWidthPtr,
	    &borderWidth);
    Tk_GetPixelsFromObj(NULL, menuPtr->tkwin, menuPtr->activeBorderWidthPtr,
	    &activeBorderWidth);
    x = y = borderWidth;
    indicatorSpace = labelWidth = accelWidth = maxAccelTextWidth = 0;
    windowHeight = windowWidth = maxWidth = lastColumnBreak = 0;
    maxModifierWidth = nonAccelMargin = maxNonAccelMargin = 0;
    maxEntryWithAccelWidth = maxEntryWithoutAccelWidth = 0;
    maxIndicatorSpace = 0;

    /*
     * On the Mac especially, getting font metrics can be quite slow,
     * so we want to do it intelligently. We are going to precalculate
     * them and pass them down to all of the measuring and drawing
     * routines. We will measure the font metrics of the menu once.
     * If an entry does not have its own font set, then we give
     * the geometry/drawing routines the menu's font and metrics.
     * If an entry has its own font, we will measure that font and
     * give all of the geometry/drawing the entry's font and metrics.
     */

    menuFont = Tk_GetFontFromObj(menuPtr->tkwin, menuPtr->fontPtr);
    Tk_GetFontMetrics(menuFont, &menuMetrics);

    for (i = 0; i < menuPtr->numEntries; i++) {
	mePtr = menuPtr->entries[i];
	if (mePtr->type == CASCADE_ENTRY || mePtr->accelLength > 0) {
	    haveAccel = 1;
	    break;
	}
    }

    for (i = 0; i < menuPtr->numEntries; i++) {
	mePtr = menuPtr->entries[i];
	if (mePtr->fontPtr == NULL) {
	    tkfont = menuFont;
	    fmPtr = &menuMetrics;
	} else {
	    tkfont = Tk_GetFontFromObj(menuPtr->tkwin, mePtr->fontPtr);
	    Tk_GetFontMetrics(tkfont, &entryMetrics);
	    fmPtr = &entryMetrics;
	}

	if ((i > 0) && mePtr->columnBreak) {
	    if (maxIndicatorSpace != 0) {
		maxIndicatorSpace += 2;
	    }
	    for (j = lastColumnBreak; j < i; j++) {
		columnEntryPtr = menuPtr->entries[j];
		geometryPtr =
			(EntryGeometry *) columnEntryPtr->platformEntryData;

		columnEntryPtr->indicatorSpace = maxIndicatorSpace;
		columnEntryPtr->width = maxIndicatorSpace + maxWidth
			+ 2 * activeBorderWidth;
		geometryPtr->accelTextWidth = maxAccelTextWidth;
		geometryPtr->modifierWidth = maxModifierWidth;
		columnEntryPtr->x = x;
		columnEntryPtr->entryFlags &= ~ENTRY_LAST_COLUMN;
		if (maxEntryWithoutAccelWidth > maxEntryWithAccelWidth) {
		    geometryPtr->nonAccelMargin = maxEntryWithoutAccelWidth
			    - maxEntryWithAccelWidth;
		    if (geometryPtr->nonAccelMargin > maxNonAccelMargin) {
			geometryPtr->nonAccelMargin = maxNonAccelMargin;
		    }
		} else {
		    geometryPtr->nonAccelMargin = 0;
		}
	    }
	    x += maxIndicatorSpace + maxWidth + 2 * borderWidth;
	    windowWidth = x;
	    maxWidth = maxIndicatorSpace = maxAccelTextWidth = 0;
	    maxModifierWidth = maxNonAccelMargin = maxEntryWithAccelWidth = 0;
	    maxEntryWithoutAccelWidth = 0;
	    lastColumnBreak = i;
	    y = borderWidth;
	}
	geometryPtr = (EntryGeometry *) mePtr->platformEntryData;

	if (mePtr->type == SEPARATOR_ENTRY) {
	    GetMenuSeparatorGeometry(menuPtr, mePtr, tkfont,
		    fmPtr, &entryWidth, &height);
	    mePtr->height = height;
	} else if (mePtr->type == TEAROFF_ENTRY) {
	    GetTearoffEntryGeometry(menuPtr, mePtr, tkfont,
		    fmPtr, &entryWidth, &height);
	    mePtr->height = height;
	} else {
	    /*
	     * For each entry, compute the height required by that
	     * particular entry, plus three widths:  the width of the
	     * label, the width to allow for an indicator to be displayed
	     * to the left of the label (if any), and the width of the
	     * accelerator to be displayed to the right of the label
	     * (if any). These sizes depend, of course, on the type
	     * of the entry.
	     */

	    GetMenuLabelGeometry(mePtr, tkfont, fmPtr, &labelWidth, &height);
	    mePtr->height = height;

	    nonAccelMargin = 0;
	    if (mePtr->type == CASCADE_ENTRY) {
		GetMenuAccelGeometry(menuPtr, mePtr, tkfont, fmPtr,
			&modifierWidth, &accelWidth, &height);
	    } else if (mePtr->accelLength == 0) {
		if (haveAccel && !mePtr->hideMargin) {
		    if (IS_THEME_MENU_FONT(tkfont)) {
			nonAccelMargin = menuSymbols[COMMAND_SYMBOL].width;
		    } else {
			nonAccelMargin = Tk_TextWidth(tkfont,
				menuSymbols[COMMAND_SYMBOL].utf,
				menuSymbols[COMMAND_SYMBOL].utfLen);
		    }
		}
		accelWidth = modifierWidth = 0;
	    } else {
		GetMenuAccelGeometry(menuPtr, mePtr, tkfont,
			fmPtr, &modifierWidth, &accelWidth, &height);
		if (height > mePtr->height) {
		    mePtr->height = height;
		}
	    }

	    if (!(mePtr->hideMargin)) {
		GetMenuIndicatorGeometry(menuPtr, mePtr, tkfont,
			fmPtr, &indicatorSpace, &height);
		if (height > mePtr->height) {
		    mePtr->height = height;
		}
	    } else {
		indicatorSpace = 0;
	    }

	    if (nonAccelMargin > maxNonAccelMargin) {
		maxNonAccelMargin = nonAccelMargin;
	    }
	    if (accelWidth > maxAccelTextWidth) {
		maxAccelTextWidth = accelWidth;
	    }
	    if (modifierWidth > maxModifierWidth) {
		maxModifierWidth = modifierWidth;
	    }
	    if (indicatorSpace > maxIndicatorSpace) {
		maxIndicatorSpace = indicatorSpace;
	    }

	    entryWidth = labelWidth + modifierWidth + accelWidth
		    + nonAccelMargin;

	    if (entryWidth > maxWidth) {
		maxWidth = entryWidth;
	    }

	    if (mePtr->accelLength > 0) {
		if (entryWidth > maxEntryWithAccelWidth) {
		    maxEntryWithAccelWidth = entryWidth;
		}
	    } else {
		if (entryWidth > maxEntryWithoutAccelWidth) {
		    maxEntryWithoutAccelWidth = entryWidth;
		}
	    }
	    mePtr->height += 2 * activeBorderWidth;
	}
	mePtr->y = y;
	y += menuPtr->entries[i]->height + borderWidth;
	if (y > windowHeight) {
	    windowHeight = y;
	}
    }

    for (j = lastColumnBreak; j < menuPtr->numEntries; j++) {
	columnEntryPtr = menuPtr->entries[j];
	geometryPtr = (EntryGeometry *) columnEntryPtr->platformEntryData;

	columnEntryPtr->indicatorSpace = maxIndicatorSpace;
	columnEntryPtr->width = maxIndicatorSpace + maxWidth
		+ 2 * activeBorderWidth;
	geometryPtr->accelTextWidth = maxAccelTextWidth;
	columnEntryPtr->x = x;
	columnEntryPtr->entryFlags |= ENTRY_LAST_COLUMN;
	if (maxEntryWithoutAccelWidth > maxEntryWithAccelWidth) {
	    geometryPtr->nonAccelMargin = maxEntryWithoutAccelWidth
		    - maxEntryWithAccelWidth;
	    if (geometryPtr->nonAccelMargin > maxNonAccelMargin) {
		geometryPtr->nonAccelMargin = maxNonAccelMargin;
	    }
	} else {
	    geometryPtr->nonAccelMargin = 0;
	}
    }
    windowWidth = x + maxIndicatorSpace + maxWidth
	    + 2 * activeBorderWidth + borderWidth;
    windowHeight += borderWidth;

    /*
     * The X server doesn't like zero dimensions, so round up to at least
     * 1 (a zero-sized menu should never really occur, anyway).
     */

    if (windowWidth <= 0) {
	windowWidth = 1;
    }
    if (windowHeight <= 0) {
	windowHeight = 1;
    }
    menuPtr->totalWidth = windowWidth;
    menuPtr->totalHeight = windowHeight;
}

/*
 *----------------------------------------------------------------------
 *
 * DrawMenuEntryLabel --
 *
 *	This procedure draws the label part of a menu.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	Commands are output to X to display the menu in its
 *	current mode.
 *
 *----------------------------------------------------------------------
 */

void
DrawMenuEntryLabel(
    TkMenu *menuPtr,		/* The menu we are drawing */
    TkMenuEntry *mePtr,		/* The entry we are drawing */
    Drawable d,			/* What we are drawing into */
    GC gc,			/* The gc we are drawing into */
    Tk_Font tkfont,		/* The precalculated font */
    const Tk_FontMetrics *fmPtr,/* The precalculated font metrics */
    int x,			/* left edge */
    int y,			/* right edge */
    int width,			/* width of entry */
    int height)			/* height of entry */
{
    int imageWidth, imageHeight, textWidth = 0, textHeight = 0;
    int indicatorSpace =  mePtr->indicatorSpace;
    int leftEdge = x + indicatorSpace;
    int haveImage = 0, haveText = 0;
    int imageXOffset = 0, imageYOffset = 0;
    int textXOffset = 0, textYOffset = 0;
    Pixmap bitmap = (Pixmap) NULL;
    Tcl_DString itemTextDString;

    /*
     * Work out what we will need to draw first.
     */

    if (mePtr->image != NULL) {
	Tk_SizeOfImage(mePtr->image, &imageWidth, &imageHeight);
	haveImage = 1;
    } else if (mePtr->bitmapPtr != NULL) {
	bitmap = Tk_GetBitmapFromObj(menuPtr->tkwin, mePtr->bitmapPtr);
	Tk_SizeOfBitmap(menuPtr->display, bitmap, &imageWidth, &imageHeight);
	haveImage = 1;
    }
    if (!haveImage || (mePtr->compound != COMPOUND_NONE)) {
	if (mePtr->labelLength > 0) {
	    GetEntryText(mePtr, &itemTextDString);
	    if (mePtr->compound != COMPOUND_NONE) {
		textWidth = Tk_TextWidth(tkfont,
			Tcl_DStringValue(&itemTextDString),
			Tcl_DStringLength(&itemTextDString)) +
			menuTextLeadingEdgeMargin + menuTextTrailingEdgeMargin;
		textHeight = fmPtr->linespace;
	    }
	    haveText = 1;
	}
    }

    /*
     * Now work out what the relative positions are.
     */

    if (haveImage && haveText && (mePtr->compound != COMPOUND_NONE)) {
	int fullWidth = (imageWidth > textWidth ? imageWidth : textWidth);

	switch ((enum compound) mePtr->compound) {
	    case COMPOUND_TOP:
		textXOffset = (fullWidth - textWidth)/2;
		textYOffset = imageHeight/2 + 2;
		imageXOffset = (fullWidth - imageWidth)/2;
		imageYOffset = -textHeight/2;
		break;
	    case COMPOUND_BOTTOM:
		textXOffset = (fullWidth - textWidth)/2;
		textYOffset = -imageHeight/2;
		imageXOffset = (fullWidth - imageWidth)/2;
		imageYOffset = textHeight/2 + 2;
		break;
	    case COMPOUND_LEFT:
		/*
		 * Position image in the indicator space to the left of the
		 * entries, unless this entry is a radio|check button because
		 * then the indicator space will be used.
		 */

		textXOffset = imageWidth + 2 - menuTextLeadingEdgeMargin;
		if ((mePtr->type != CHECK_BUTTON_ENTRY)
			&& (mePtr->type != RADIO_BUTTON_ENTRY)) {
		    textXOffset -= indicatorSpace;
		    imageXOffset = -indicatorSpace;
		}
		if (textXOffset < 0) {
		    textXOffset = 0;
		}
		break;
	    case COMPOUND_RIGHT:
		imageXOffset = textWidth + 2 - menuTextTrailingEdgeMargin;
		break;
	    case COMPOUND_CENTER:
		textXOffset = (fullWidth - textWidth)/2;
		imageXOffset = (fullWidth - imageWidth)/2;
		break;
	    case COMPOUND_NONE:
	    	/*
	    	 * Never reached.
	    	 */
		break;
	}
    }

    /*
     * Draw label and/or bitmap or image for entry.
     */

    if (mePtr->image != NULL) {
	if ((mePtr->selectImage != NULL)
		&& (mePtr->entryFlags & ENTRY_SELECTED)) {
	    Tk_RedrawImage(mePtr->selectImage, 0, 0, imageWidth, imageHeight,
		    d, leftEdge + imageXOffset,
		    y + (mePtr->height - imageHeight)/2 + imageYOffset);
	} else {
	    Tk_RedrawImage(mePtr->image, 0, 0, imageWidth, imageHeight,
		    d, leftEdge + imageXOffset,
		    y + (mePtr->height - imageHeight)/2 + imageYOffset);
	}
    } else if (mePtr->bitmapPtr != NULL) {
	XCopyPlane(menuPtr->display, bitmap, d, gc, 0, 0, imageWidth,
		imageHeight, leftEdge + imageXOffset,
		y + (mePtr->height - imageHeight)/2  + imageYOffset, 1);
    }
    if (haveText) {
	int baseline = y + (height + fmPtr->ascent - fmPtr->descent)/2;

	Tk_DrawChars(menuPtr->display, d, gc, tkfont,
		Tcl_DStringValue(&itemTextDString),
		Tcl_DStringLength(&itemTextDString),
		leftEdge + menuTextLeadingEdgeMargin + textXOffset,
		baseline + textYOffset);
	Tcl_DStringFree(&itemTextDString);
    }

    if (mePtr->state == ENTRY_DISABLED) {
	if (menuPtr->disabledFgPtr == NULL) {
	    /* XFillRectangle(menuPtr->display, d, menuPtr->disabledGC, x, y,
		    width, height); */
	} else if ((mePtr->image != NULL)
		&& (menuPtr->disabledImageGC != None)) {
	    XFillRectangle(menuPtr->display, d, menuPtr->disabledImageGC,
		    leftEdge + imageXOffset,
		    y + (mePtr->height - imageHeight)/2 + imageYOffset,
		    imageWidth, imageHeight);
	}
    }
}

/*
 *----------------------------------------------------------------------
 *
 * DrawMenuEntryBackground --
 *
 *	This procedure draws the background part of a menu entry.
 *	Under Appearance, we only draw the background if the entry's
 *	border is set, we DO NOT inherit it from the menu...
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	Commands are output to X to display the menu in its
 *	current mode.
 *
 *----------------------------------------------------------------------
 */

void
DrawMenuEntryBackground(
    TkMenu *menuPtr,		/* The menu we are drawing. */
    TkMenuEntry *mePtr,		/* The entry we are drawing. */
    Drawable d,			/* What we are drawing into */
    Tk_3DBorder activeBorder,	/* Border for active items */
    Tk_3DBorder bgBorder,	/* Border for the background */
    int x,			/* left edge */
    int y,			/* top edge */
    int width,			/* width of rectangle to draw */
    int height)			/* height of rectangle to draw */
{
    if ((menuPtr->menuType == TEAROFF_MENU)
	    || ((mePtr->state == ENTRY_ACTIVE)
		    && (mePtr->activeBorderPtr != None))
	    || ((mePtr->state != ENTRY_ACTIVE) && (mePtr->borderPtr != None))) {
	if (mePtr->state == ENTRY_ACTIVE) {
	    bgBorder = activeBorder;
	}
	Tk_Fill3DRectangle(menuPtr->tkwin, d, bgBorder,
		x, y, width, height, 0, TK_RELIEF_FLAT);
    }
}

/*
 *----------------------------------------------------------------------
 *
 * GetMenuLabelGeometry --
 *
 *	Figures out the size of the label portion of a menu item.
 *
 * Results:
 *	widthPtr and heightPtr are filled in with the correct geometry
 *	information.
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */

void
GetMenuLabelGeometry(
    TkMenuEntry *mePtr,		/* The entry we are computing */
    Tk_Font tkfont,		/* The precalculated font */
    const Tk_FontMetrics *fmPtr,/* The precalculated metrics */
    int *widthPtr,		/* The resulting width of the label portion */
    int *heightPtr)		/* The resulting height of the label portion */
{
    TkMenu *menuPtr = mePtr->menuPtr;
    int haveImage = 0, tornOff = (menuPtr->menuType == TEAROFF_MENU);
#ifdef USE_TK_MDEF
    const int useMDEF = ((MacMenu *) menuPtr->platformData)->useMDEF;
#endif

    if (mePtr->image != NULL && (useMDEF || tornOff)) {
	Tk_SizeOfImage(mePtr->image, widthPtr, heightPtr);
	haveImage = 1;
    } else if (mePtr->bitmapPtr != NULL && (useMDEF || tornOff)) {
	Pixmap bitmap = Tk_GetBitmapFromObj(menuPtr->tkwin, mePtr->bitmapPtr);
	Tk_SizeOfBitmap(menuPtr->display, bitmap, widthPtr, heightPtr);
	haveImage = 1;
    }
    if (!haveImage || (mePtr->compound != COMPOUND_NONE)) {
	int textWidth = 0, textHeight = fmPtr->linespace;

	if (mePtr->labelPtr != NULL) {
	    Tcl_DString itemTextDString;

	    GetEntryText(mePtr, &itemTextDString);
	    textWidth = Tk_TextWidth(tkfont,
		    Tcl_DStringValue(&itemTextDString),
		    Tcl_DStringLength(&itemTextDString)) +
		    menuTextLeadingEdgeMargin + menuTextTrailingEdgeMargin;
	    Tcl_DStringFree(&itemTextDString);

	    if (haveImage && (mePtr->compound != COMPOUND_NONE)) {
		switch ((enum compound) mePtr->compound) {
		    int margin;

		    case COMPOUND_TOP:
		    case COMPOUND_BOTTOM:
			if (textWidth > *widthPtr) {
			    *widthPtr = textWidth;
			}
			*heightPtr += textHeight + 2;
			break;
		    case COMPOUND_LEFT:
			margin = *widthPtr + 2;
			if (margin > menuTextLeadingEdgeMargin) {
			    margin = menuTextLeadingEdgeMargin;
			}
			*widthPtr += textWidth + 2 - margin;
			if (textHeight > *heightPtr) {
			    *heightPtr = textHeight;
			}
			break;
		    case COMPOUND_RIGHT:
			margin = menuTextTrailingEdgeMargin;
			*widthPtr += textWidth + 2 - margin;
			if (textHeight > *heightPtr) {
			    *heightPtr = textHeight;
			}
			break;
		    case COMPOUND_CENTER:
			if (textWidth > *widthPtr) {
			    *widthPtr = textWidth;
			}
			if (textHeight > *heightPtr) {
			    *heightPtr = textHeight;
			}
			break;
		    case COMPOUND_NONE:
			/*
			 * Never reached.
			 */
			break;
		}
		goto labelGeomDone;
	    }
	}
	*widthPtr = textWidth;
	*heightPtr = textHeight;
    }

labelGeomDone:
    *heightPtr += menuItemExtraHeight;
    *widthPtr += menuItemExtraWidth;
}

/*
 *----------------------------------------------------------------------
 *
 * TkMacOSXGenerateParentMenuSelectEvent --
 *
 *	Respond to a hierarchical menu being opened.
 *
 * Results:
 *	True if event(s) are generated - false otherwise.
 *
 * Side effects:
 *	Places a virtual event on the event queue.
 *
 *----------------------------------------------------------------------
 */

int
TkMacOSXGenerateParentMenuSelectEvent(
    MenuRef menu)
{
    TkMenu *menuPtr = MenuPtrForMenuRef(menu);

    if (menuPtr) {
	TkMenuEntry *parentEntryPtr = GetParentMenuEntry(menuPtr);

	if (parentEntryPtr && (menuPtr = parentEntryPtr->menuPtr)) {
	    TkActivateMenuEntry(menuPtr, parentEntryPtr->index);
	    MenuSelectEvent(menuPtr);
	    Tcl_ServiceAll();
	    return true;
	}
    }
    return false;
}

/*
 *----------------------------------------------------------------------
 *
 * TkMacOSXGenerateMenuSelectEvent --
 *
 *	Respond to a menu item being selected.
 *
 * Results:
 *	True if event(s) are generated - false otherwise.
 *
 * Side effects:
 *	Places a virtual event on the event queue.
 *
 *----------------------------------------------------------------------
 */

int
TkMacOSXGenerateMenuSelectEvent(
    MenuRef menu,
    MenuItemIndex index)
{
    TkMenu *menuPtr = MenuPtrForMenuRef(menu);
    int item = index - 1;

    if (menuPtr) {
	if (item < 0 || item >= menuPtr->numEntries ||
		(menuPtr->entries[item])->state == ENTRY_DISABLED) {
	    TkActivateMenuEntry(menuPtr, -1);
	} else {
	    TkActivateMenuEntry(menuPtr, item);
	    MenuSelectEvent(menuPtr);
	    Tcl_ServiceAll();
	    return true;
	}
    }
    return false;
}

/*
 *----------------------------------------------------------------------
 *
 * MenuSelectEvent --
 *
 *	Generates a "MenuSelect" virtual event. This can be used to
 *	do context-sensitive menu help.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	Places a virtual event on the event queue.
 *
 *----------------------------------------------------------------------
 */

void
MenuSelectEvent(
    TkMenu *menuPtr)		/* the menu we have selected. */
{
    XVirtualEvent event;

    bzero(&event, sizeof(XVirtualEvent));
    event.type = VirtualEvent;
    event.serial = menuPtr->display->request;
    event.send_event = false;
    event.display = menuPtr->display;
    Tk_MakeWindowExist(menuPtr->tkwin);
    event.event = Tk_WindowId(menuPtr->tkwin);
    event.root = XRootWindow(menuPtr->display, 0);
    event.subwindow = None;
    event.time = TkpGetMS();

    XQueryPointer(NULL, None, NULL, NULL, &event.x_root, &event.y_root, NULL,
	    NULL, &event.state);
    event.same_screen = true;
    event.name = Tk_GetUid("MenuSelect");
    Tk_QueueWindowEvent((XEvent *) &event, TCL_QUEUE_TAIL);
}

/*
 *----------------------------------------------------------------------
 *
 * TkMacOSXClearActiveMenu --
 *
 *	Clears Tk's active entry for the given MenuRef.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	Generates <<MenuSelect>> virtual events.
 *
 *----------------------------------------------------------------------
 */

void
TkMacOSXClearActiveMenu(
    MenuRef menu)
{
    TkMenu *menuPtr = MenuPtrForMenuRef(menu);

    if (menuPtr) {
	RecursivelyClearActiveMenu(menuPtr);
    }
}

/*
 *----------------------------------------------------------------------
 *
 * RecursivelyClearActiveMenu --
 *
 *	Recursively clears the active entry in the menu's cascade hierarchy.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	Generates <<MenuSelect>> virtual events.
 *
 *----------------------------------------------------------------------
 */

void
RecursivelyClearActiveMenu(
    TkMenu *menuPtr)		/* The menu to reset. */
{
    int i;
    TkMenuEntry *mePtr;

    TkActivateMenuEntry(menuPtr, -1);
    for (i = 0; i < menuPtr->numEntries; i++) {
	mePtr = menuPtr->entries[i];
	if (mePtr->type == CASCADE_ENTRY) {
	    if ((mePtr->childMenuRefPtr != NULL)
		    && (mePtr->childMenuRefPtr->menuPtr != NULL)) {
		RecursivelyClearActiveMenu(mePtr->childMenuRefPtr->menuPtr);
	    }
	}
    }
}

/*
 *----------------------------------------------------------------------
 *
 * TkMacOSXClearMenubarActive --
 *
 *	Recursively clears the active entry in the current menubar hierarchy.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	Generates <<MenuSelect>> virtual events.
 *
 *----------------------------------------------------------------------
 */

void
TkMacOSXClearMenubarActive(void)
{
    TkMenuReferences *menuBarRefPtr;

    if (currentMenuBarName != NULL) {
	menuBarRefPtr = TkFindMenuReferences(currentMenuBarInterp,
		currentMenuBarName);
	if ((menuBarRefPtr != NULL) && (menuBarRefPtr->menuPtr != NULL)) {
	    TkMenu *menuPtr;

	    for (menuPtr = menuBarRefPtr->menuPtr->masterMenuPtr;
		    menuPtr != NULL; menuPtr = menuPtr->nextInstancePtr) {
		if (menuPtr->menuType == MENUBAR) {
		    RecursivelyClearActiveMenu(menuPtr);
		}
	    }
	}
    }
}

/*
 *----------------------------------------------------------------------
 *
 * TkpMenuNotifyToplevelCreate --
 *
 *	This routine reconfigures the menu and the clones indicated by
 *	menuName becuase a toplevel has been created and any system
 *	menus need to be created. Only applicable to Windows.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	An idle handler is set up to do the reconfiguration.
 *
 *----------------------------------------------------------------------
 */

void
TkpMenuNotifyToplevelCreate(
    Tcl_Interp *interp,		/* The interp the menu lives in. */
    char *menuName)		/* The name of the menu to reconfigure. */
{
    /*
     * Nothing to do.
     */
}

/*
 *----------------------------------------------------------------------
 *
 * TkpMenuInit --
 *
 *	Initializes Mac-specific menu data.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	Allocates a hash table.
 *
 *----------------------------------------------------------------------
 */

void
TkpMenuInit(void)
{
    MenuSymbol *ms = menuSymbols;
    CFStringRef cfStr;

    lastMenuID = 256;
    Tcl_InitHashTable(&commandTable, TCL_ONE_WORD_KEYS);
    currentMenuBarOwner = NULL;
    currentAppleMenuID = 0;
    currentHelpMenuID = 0;
    currentMenuBarInterp = NULL;
    currentMenuBarName = NULL;
    windowListPtr = NULL;

#ifdef USE_TK_MDEF
    tkThemeMenuItemDrawingUPP
	    = NewMenuItemDrawingUPP(ThemeMenuItemDrawingProc);
    useMDEFVar = Tcl_NewStringObj("::tk::mac::useCustomMDEF", -1);
    macMDEFDrawable.winPtr = NULL;
    macMDEFDrawable.xOff = 0;
    macMDEFDrawable.yOff = 0;
    macMDEFDrawable.visRgn = NULL;
    macMDEFDrawable.aboveVisRgn = NULL;
    macMDEFDrawable.drawRect = CGRectNull;
    macMDEFDrawable.referenceCount = 0;
    macMDEFDrawable.toplevel = NULL;
    macMDEFDrawable.flags = 0;
    macMDEFDrawable.grafPtr = NULL;
    macMDEFDrawable.context = NULL;
    macMDEFDrawable.size = CGSizeZero;
#endif

    ChkErr(GetThemeMetric, kThemeMetricMenuMarkColumnWidth,
	    &menuMarkColumnWidth);
    ChkErr(GetThemeMetric, kThemeMetricMenuMarkIndent, &menuMarkIndent);
    ChkErr(GetThemeMetric, kThemeMetricMenuTextLeadingEdgeMargin,
	    &menuTextLeadingEdgeMargin);
    ChkErr(GetThemeMetric, kThemeMetricMenuTextTrailingEdgeMargin,
	    &menuTextTrailingEdgeMargin);
    ChkErr(GetThemeMenuItemExtra, kThemeMenuItemPlain, &menuItemExtraHeight,
	    &menuItemExtraWidth);
    ChkErr(GetThemeMenuSeparatorHeight, &menuSeparatorHeight);

    while (ms->unicode) {
	ms->utfLen = Tcl_UniCharToUtf(ms->unicode, ms->utf);
	ms->utf[ms->utfLen] = 0;
	cfStr = CFStringCreateWithCharacters(NULL, &ms->unicode, 1);
	if (cfStr) {
	    ms->width = MeasureThemeText(cfStr, kThemeMenuItemCmdKeyFont);
	    CFRelease(cfStr);
	}
	ms++;
    }
}

/*
 *----------------------------------------------------------------------
 *
 * TkpMenuThreadInit --
 *
 *	Does platform-specific initialization of thread-specific
 *	menu state.
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
TkpMenuThreadInit(void)
{
    /*
     * Nothing to do.
     */
}

/*
 *----------------------------------------------------------------------
 *
 * TkpPreprocessMacMenu --
 *
 *    Handle preprocessing of menubar if it exists.
 *
 * Results:
 *    None.
 *
 * Side effects:
 *    All post commands for the current menubar get executed.
 *
 *----------------------------------------------------------------------
 */

void
TkMacOSXPreprocessMenu(void)
{
    if ((currentMenuBarName != NULL) && (currentMenuBarInterp != NULL)) {
	TkMenuReferences *mbRefPtr =
		TkFindMenuReferences(currentMenuBarInterp,currentMenuBarName);

	if ((mbRefPtr != NULL) && (mbRefPtr->menuPtr != NULL)) {
	    int code;

	    Tcl_Preserve((ClientData) currentMenuBarInterp);
	    code = TkPreprocessMenu(mbRefPtr->menuPtr->masterMenuPtr);
	    if ((code != TCL_OK) && (code != TCL_CONTINUE)
		    && (code != TCL_BREAK)) {
		Tcl_AddErrorInfo(currentMenuBarInterp,
			"\n    (menu preprocess)");
		Tcl_BackgroundError(currentMenuBarInterp);
	    }
	    Tcl_Release((ClientData) currentMenuBarInterp);
	}
    }
}

#ifdef USE_TK_MDEF
#pragma mark MDEF
/*
 *----------------------------------------------------------------------
 *
 * MenuDefProc --
 *
 *	This routine is the MDEF handler for Tk. It receives all messages
 *	for the menu and dispatches them.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	This routine causes menus to be drawn and will certainly allocate
 *	memory as a result. Also, the menu can scroll up and down, and
 *	various other interface actions can take place.
 *
 *----------------------------------------------------------------------
 */

void
MenuDefProc(
    SInt16 message,		/* What action are we taking? */
    MenuRef menu,		/* The menu we are working with */
    Rect *menuRectPtr,		/* A pointer to the rect for the
				 * whole menu. */
    Point hitPt,		/* Where the mouse was clicked for
				 * the appropriate messages. */
    SInt16 *whichItem)		/* Output result. Which item was
				 * hit by the user? */
{
    TkMenu *menuPtr;
    Tcl_HashEntry *commandEntryPtr;
    MenuID menuID;

    menuID = GetMenuID(menu);
    commandEntryPtr = Tcl_FindHashEntry(&commandTable, (char*)(intptr_t)menuID);

    if (commandEntryPtr) {
	menuPtr = (TkMenu *) Tcl_GetHashValue(commandEntryPtr);
    } else {
	menuPtr = NULL;
    }

    switch (message) {
	case kMenuInitMsg:
	    *whichItem = noErr;
	    break;
	case kMenuDisposeMsg:
	    break;
	case kMenuHiliteItemMsg:
	    HandleMenuHiliteMsg(menu, menuRectPtr, hitPt, whichItem, menuPtr);
	    break;
	case kMenuCalcItemMsg:
	    HandleMenuCalcItemMsg(menu, menuRectPtr, hitPt, whichItem,
		    menuPtr);
	    break;
	case kMenuDrawItemsMsg:
#ifdef TK_MAC_DEBUG_MENUS
	    TkMacOSXDbgMsg("MDEF: DrawItemsMsg");
#endif
	    /*
	     * We do nothing  here, because we don't support the Menu Managers
	     * dynamic item groups
	     */
	    break;
	case kMenuThemeSavvyMsg:
	    *whichItem = kThemeSavvyMenuResponse;
	    break;
	case kMenuSizeMsg:
#ifdef TK_MAC_DEBUG_MENUS
	    TkMacOSXDbgMsg("MDEF: SizeMsg %d, %d", hitPt.h, hitPt.v);
#endif
	    SetMenuWidth(menu, hitPt.h < menuPtr->totalWidth ?	hitPt.h :
		    menuPtr->totalWidth);
	    SetMenuHeight(menu, hitPt.v < menuPtr->totalHeight ? hitPt.v :
		    menuPtr->totalHeight);
	    break;
	case kMenuDrawMsg:
	    HandleMenuDrawMsg(menu, menuRectPtr, hitPt, whichItem, menuPtr);
	    break;
	case kMenuFindItemMsg:
	    HandleMenuFindItemMsg(menu, menuRectPtr, hitPt, whichItem,
		    menuPtr);
	    break;
	case kMenuPopUpMsg:
	    HandleMenuPopUpMsg(menu, menuRectPtr, hitPt, whichItem, menuPtr);
	    break;
    }
}

/*
 *----------------------------------------------------------------------
 *
 * HandleMenuHiliteMsg --
 *
 *	Handles the MenuDefProc's hilite message.
 *
 * Results:
 *	A menu entry is drawn
 *
 * Side effects:
 *	None
 *
 *----------------------------------------------------------------------
 */

void
HandleMenuHiliteMsg(
    MenuRef menu,
    Rect *menuRectPtr,
    Point hitPt,
    SInt16 *whichItem,
    TkMenu *menuPtr)
{
    OSStatus err;
    Tk_Font tkfont;
    Tk_FontMetrics fontMetrics;
    MDEFHiliteItemData *hidPtr = (MDEFHiliteItemData *)whichItem;
    int oldItem = hidPtr->previousItem - 1;
    int newItem = hidPtr->newItem - 1;
    MenuTrackingData mtd, *mtdPtr = &mtd;

#ifdef TK_MAC_DEBUG_MENUS
    TkMacOSXDbgMsg("MDEF: HiliteMsg %d -> %d", hidPtr->previousItem,
	    hidPtr->newItem);
#endif
    GetPort(&macMDEFDrawable.grafPtr);
    macMDEFDrawable.context = (CGContextRef) hidPtr->context;

    err = ChkErr(GetMenuTrackingData, menu, mtdPtr);
    if (err != noErr) {
	return;
    }

    tkfont = Tk_GetFontFromObj(menuPtr->tkwin, menuPtr->fontPtr);
    Tk_GetFontMetrics(tkfont, &fontMetrics);
    if (oldItem >= 0) {
	AppearanceEntryDrawWrapper(menuPtr->entries[oldItem], menuRectPtr,
		mtdPtr, (Drawable) &macMDEFDrawable, &fontMetrics, tkfont, 1);
    }
    if (newItem >= 0) {
	AppearanceEntryDrawWrapper(menuPtr->entries[newItem], menuRectPtr,
		mtdPtr, (Drawable) &macMDEFDrawable, &fontMetrics, tkfont, 0);
    }
}

/*
 *----------------------------------------------------------------------
 *
 * HandleMenuDrawMsg --
 *
 *	Handles the MenuDefProc's draw message.
 *
 * Results:
 *	A menu entry is drawn
 *
 * Side effects:
 *	None
 *
 *----------------------------------------------------------------------
 */

void
HandleMenuDrawMsg(
    MenuRef menu,
    Rect *menuRectPtr,
    Point hitPt,
    SInt16 *whichItem,
    TkMenu *menuPtr)
{
    Tk_Font menuFont;
    Tk_FontMetrics fontMetrics;
    TkMenuEntry *mePtr;
    int i;
    Rect menuClipRect, bounds;
    MDEFDrawData *ddPtr = (MDEFDrawData*)whichItem;
    MenuTrackingData *mtdPtr = &(ddPtr->trackingData);
    TkWindow *winPtr = (TkWindow*)menuPtr->tkwin;

    GetPort(&macMDEFDrawable.grafPtr);
    GetPortBounds(macMDEFDrawable.grafPtr, &bounds);
    macMDEFDrawable.context = (CGContextRef) ddPtr->context;
#ifdef TK_MAC_DEBUG_MENUS
    TkMacOSXDbgMsg("MDEF: DrawMsg %d - %d; %d - %d", menuRectPtr->top,
	    menuRectPtr->bottom, bounds.top, bounds.bottom);
#endif
    winPtr->changes.x = menuRectPtr->left;
    winPtr->changes.y = menuRectPtr->top;
    winPtr->changes.width = menuRectPtr->right - menuRectPtr->left;
    winPtr->changes.height = menuRectPtr->bottom - menuRectPtr->top;
    TkpClipDrawableToRect(menuPtr->display, (Drawable) &macMDEFDrawable,
	    0, 0, -1, -1);
#if 0
    if (menuPtr->menuRefPtr->topLevelListPtr != NULL) {
	menuType = kThemeMenuTypePullDown;
    } else if (menuPtr->menuRefPtr->parentEntryPtr != NULL) {
	menuType = kThemeMenuTypeHierarchical;
    } else {
	menuType = kThemeMenuTypePopUp;
    }
#endif
    DrawMenuBackground(menuPtr, menuRectPtr, (Drawable) &macMDEFDrawable);
    menuFont = Tk_GetFontFromObj(menuPtr->tkwin, menuPtr->fontPtr);
    Tk_GetFontMetrics(menuFont, &fontMetrics);
    menuClipRect = *menuRectPtr;
    mtdPtr->virtualMenuBottom = mtdPtr->virtualMenuTop + menuPtr->totalHeight;

    /*
     * Next, figure out scrolling information.
     */

    if ((menuRectPtr->bottom - menuRectPtr->top) < menuPtr->totalHeight) {
	short arrowHeight = fontMetrics.linespace + 1;
	Rect arrowRect, eraseRect;
	ThemeMenuState menuState = IsMenuItemEnabled(menu, 0) ?
		kThemeMenuActive : kThemeMenuDisabled;

	if (mtdPtr->virtualMenuTop < menuRectPtr->top) {
	    arrowRect = bounds;
	    /*arrowRect.top += 1;*/
	    arrowRect.bottom = arrowRect.top + arrowHeight;
	    eraseRect = arrowRect;
	    eraseRect.top = menuRectPtr->top;
	    menuClipRect.top = arrowRect.bottom;
	    ChkErr(EraseMenuBackground, menu, &eraseRect,
		    macMDEFDrawable.context);
	    ChkErr(DrawThemeMenuItem, menuRectPtr, &arrowRect,
		    mtdPtr->virtualMenuTop, mtdPtr->virtualMenuBottom,
		    menuState, kThemeMenuItemScrollUpArrow, NULL, 0);
#ifdef TK_MAC_DEBUG_MENUS
	    TkMacOSXDbgMsg("upArrow:   %d - %d, %d - %d", arrowRect.top,
		    arrowRect.bottom, arrowRect.left, arrowRect.right);
#endif
	}
	if (mtdPtr->virtualMenuBottom > menuRectPtr->bottom) {
	    arrowRect = bounds;
	    arrowRect.bottom -= 1;
	    arrowRect.top = arrowRect.bottom - arrowHeight;
	    eraseRect = arrowRect;
	    eraseRect.bottom = menuRectPtr->bottom;
	    menuClipRect.bottom = arrowRect.top;
	    ChkErr(EraseMenuBackground, menu, &eraseRect,
		    macMDEFDrawable.context);
	    ChkErr(DrawThemeMenuItem, menuRectPtr, &arrowRect,
		    mtdPtr->virtualMenuTop, mtdPtr->virtualMenuBottom,
		    menuState, kThemeMenuItemScrollDownArrow, NULL, 0);
#ifdef TK_MAC_DEBUG_MENUS
	    TkMacOSXDbgMsg("downArrow: %d - %d, %d - %d", arrowRect.top,
		    arrowRect.bottom, arrowRect.left, arrowRect.right);
#endif
	}
	TkpClipDrawableToRect(menuPtr->display, (Drawable) &macMDEFDrawable,
		menuClipRect.left, menuClipRect.top, menuClipRect.right -
		menuClipRect.left, menuClipRect.bottom - menuClipRect.top);
    }

    /*
     * Now, actually draw the menu. Don't draw entries that
     * are higher than the top arrow, and don't draw entries
     * that are lower than the bottom.
     */

    for (i = 0; i < menuPtr->numEntries; i++) {
	mePtr = menuPtr->entries[i];
	if (mtdPtr->virtualMenuTop + mePtr->y + mePtr->height <
		menuClipRect.top || mtdPtr->virtualMenuTop + mePtr->y >
		menuClipRect.bottom) {
	    continue;
	}
	AppearanceEntryDrawWrapper(mePtr, menuRectPtr, mtdPtr,
		(Drawable) &macMDEFDrawable, &fontMetrics, menuFont, 0);
    }
    MDEFScrollFlag = 1;
}

/*
 *----------------------------------------------------------------------
 *
 * HandleMenuFindItemMsg --
 *
 *	Handles the MenuDefProc's FindItems message. We have to
 *	respond by filling in the itemSelected, itemUnderMouse and
 *	itemRect fields. This is also the time to scroll the menu if
 *	it is too long to fit on the screen.
 *
 * Results:
 *	The Menu system is informed of the selected item & the item
 *	under the mouse.
 *
 * Side effects:
 *	The menu might get scrolled.
 *
 *----------------------------------------------------------------------
 */
void
HandleMenuFindItemMsg(
    MenuRef menu,
    Rect *menuRectPtr,
    Point hitPt,
    SInt16 *whichItem,
    TkMenu *menuPtr)
{
    Tk_Font menuFont;
    Tk_FontMetrics fontMetrics;
    TkMenuEntry *mePtr;
    int i, newItem = -1, itemUnderMouse = -1;
    Rect itemRect = {0, 0, 0, 0}, menuClipRect, bounds;
    int hasTopScroll, hasBottomScroll;
    MDEFFindItemData *fiPtr = (MDEFFindItemData *)whichItem;
    MenuTrackingData *mtdPtr = &(fiPtr->trackingData), topMtd;
    enum {
	DONT_SCROLL, DOWN_SCROLL, UP_SCROLL
    } scrollDirection;
    short arrowHeight;

#ifdef TK_MAC_DEBUG_MENUS
    static Point lastHitPt = {0, 0};
    if (hitPt.h != lastHitPt.h || hitPt.v != lastHitPt.v) {
	lastHitPt = hitPt;
	TkMacOSXDbgMsg("MDEF: FindItemMsg: %d, %d", hitPt.h, hitPt.v);
    }
#endif

    GetPort(&macMDEFDrawable.grafPtr);
    GetPortBounds(macMDEFDrawable.grafPtr, &bounds);
    macMDEFDrawable.context = (CGContextRef) fiPtr->context;

    /*
     * Now we need to take care of scrolling the menu.
     */

    menuFont = Tk_GetFontFromObj(menuPtr->tkwin, menuPtr->fontPtr);
    Tk_GetFontMetrics(menuFont, &fontMetrics);
    arrowHeight = fontMetrics.linespace + 1;
    menuClipRect = *menuRectPtr;
    hasTopScroll = mtdPtr->virtualMenuTop < menuRectPtr->top;
    hasBottomScroll = mtdPtr->virtualMenuBottom > menuRectPtr->bottom;
    scrollDirection = DONT_SCROLL;
    if (hasTopScroll) {
	menuClipRect.top = bounds.top + arrowHeight;
	if (hitPt.v < menuClipRect.top) {
	    newItem = -1;
	    scrollDirection = DOWN_SCROLL;
	}
    }
    if (hasBottomScroll) {
	menuClipRect.bottom = bounds.bottom - 1 - arrowHeight;
	if (hitPt.v > menuClipRect.bottom) {
	    newItem = -1;
	    scrollDirection = UP_SCROLL;
	}
    }
    if (MDEFScrollFlag) {
	scrollDirection = DONT_SCROLL;
	MDEFScrollFlag = 0;
    }
    /*
     * Don't scroll if there are other menus open above us
     */
    ChkErr(GetMenuTrackingData, NULL, &topMtd);
    if (menu != topMtd.menu) {
	scrollDirection = DONT_SCROLL;
    }
    if (scrollDirection == DONT_SCROLL) {
	/*
	 * Find out which item was hit. If it is the same as the old item,
	 * we don't need to do anything.
	 */

	if (PtInRect(hitPt, menuRectPtr)) {
	    for (i = 0; i < menuPtr->numEntries; i++) {
		mePtr = menuPtr->entries[i];
		itemRect.left = menuRectPtr->left + mePtr->x;
		itemRect.top = mtdPtr->virtualMenuTop + mePtr->y;
		itemRect.right = mePtr->entryFlags & ENTRY_LAST_COLUMN ?
			menuRectPtr->right : itemRect.left + mePtr->width;
		itemRect.bottom = itemRect.top + mePtr->height;
		if (PtInRect(hitPt, &itemRect)) {
		    if ((mePtr->type == SEPARATOR_ENTRY)
			    || (mePtr->state == ENTRY_DISABLED)) {
			newItem = -1;
			itemUnderMouse = i;
		    } else {
			TkMenuEntry *parentEntryPtr =
				GetParentMenuEntry(menuPtr);

			if (parentEntryPtr &&
				parentEntryPtr->state == ENTRY_DISABLED) {
			    newItem = -1;
			    itemUnderMouse = i;
			} else {
			    newItem = i;
			    itemUnderMouse = i;
			}
		    }
		    break;
		}
	    }
	}
    } else {
	short scrollAmt;
	unsigned long scrollDelay;
	Rect arrowRect, eraseRect, scrolledMenuClipRect;
	ThemeMenuState menuState = IsMenuItemEnabled(menu, 0) ?
		kThemeMenuActive : kThemeMenuDisabled;
	int oldItem = mtdPtr->itemSelected - 1;
	short d;

	TkpClipDrawableToRect(menuPtr->display, (Drawable) &macMDEFDrawable,
		0, 0, -1, -1);
	scrollAmt = fontMetrics.linespace + menuItemExtraHeight;
	if (scrollDirection == UP_SCROLL) {
	    scrollAmt = -scrollAmt;
	    d = hitPt.v - bounds.bottom;
	} else {
	    d = bounds.top - hitPt.v;
	}
	scrollDelay = (d >= scrollAmt/2) ? 1 : 10;
	menuClipRect = *menuRectPtr;
	if (mtdPtr->virtualMenuTop + scrollAmt < menuRectPtr->top) {
	    arrowRect = bounds;
	    /*arrowRect.top += 1;*/
	    arrowRect.bottom = arrowRect.top + arrowHeight;
	    eraseRect = arrowRect;
	    eraseRect.top = menuRectPtr->top;
	    menuClipRect.top = arrowRect.bottom;
	    if (!hasTopScroll) {
		ChkErr(EraseMenuBackground, menu, &eraseRect,
			macMDEFDrawable.context);
		ChkErr(DrawThemeMenuItem, menuRectPtr, &arrowRect,
			mtdPtr->virtualMenuTop + scrollAmt,
			mtdPtr->virtualMenuBottom + scrollAmt,
			menuState, kThemeMenuItemScrollUpArrow, NULL, 0);
#ifdef TK_MAC_DEBUG_MENUS
		TkMacOSXDbgMsg("upArrow:   %d - %d, %d - %d", arrowRect.top,
			arrowRect.bottom, arrowRect.left, arrowRect.right);
#endif
	    }
	}
	if (mtdPtr->virtualMenuBottom + scrollAmt > menuRectPtr->bottom) {
	    arrowRect = bounds;
	    arrowRect.bottom -= 1;
	    arrowRect.top = arrowRect.bottom - arrowHeight;
	    eraseRect = arrowRect;
	    eraseRect.bottom = menuRectPtr->bottom;
	    menuClipRect.bottom = arrowRect.top;
	    if (!hasBottomScroll) {
		ChkErr(EraseMenuBackground, menu, &eraseRect,
			macMDEFDrawable.context);
		ChkErr(DrawThemeMenuItem, menuRectPtr, &arrowRect,
			mtdPtr->virtualMenuTop + scrollAmt,
			mtdPtr->virtualMenuBottom + scrollAmt,
			menuState, kThemeMenuItemScrollDownArrow, NULL, 0);
#ifdef TK_MAC_DEBUG_MENUS
		TkMacOSXDbgMsg("downArrow: %d - %d, %d - %d", arrowRect.top,
			arrowRect.bottom, arrowRect.left, arrowRect.right);
#endif
	    }
	}
	TkpClipDrawableToRect(menuPtr->display, (Drawable) &macMDEFDrawable,
		menuClipRect.left, menuClipRect.top, menuClipRect.right -
		menuClipRect.left, menuClipRect.bottom - menuClipRect.top);
	TkActivateMenuEntry(menuPtr, -1);
	if (oldItem >= 0) {
	    AppearanceEntryDrawWrapper(menuPtr->entries[oldItem], menuRectPtr,
		    mtdPtr, (Drawable) &macMDEFDrawable, &fontMetrics,
		    menuFont, 1);
	}
	ChkErr(ScrollMenuImage, menu, &menuClipRect, 0, scrollAmt,
		macMDEFDrawable.context);
	mtdPtr->virtualMenuTop += scrollAmt;
	mtdPtr->virtualMenuBottom += scrollAmt;
	scrolledMenuClipRect = menuClipRect;
	OffsetRect(&scrolledMenuClipRect, 0, scrollAmt);
	menuClipRect = bounds;
	if (mtdPtr->virtualMenuTop < menuRectPtr->top) {
	    menuClipRect.top += arrowHeight;
	}
	if (mtdPtr->virtualMenuBottom > menuRectPtr->bottom) {
	    menuClipRect.bottom -= arrowHeight;
	}
	TkpClipDrawableToRect(menuPtr->display, (Drawable) &macMDEFDrawable,
		menuClipRect.left, menuClipRect.top, menuClipRect.right -
		menuClipRect.left, menuClipRect.bottom - menuClipRect.top);
	if (scrolledMenuClipRect.bottom < menuClipRect.bottom) {
	    menuClipRect.top = scrolledMenuClipRect.bottom;
	} else if (scrolledMenuClipRect.top < menuClipRect.top) {
	    menuClipRect.bottom = scrolledMenuClipRect.top;
	}
	for (i = 0; i < menuPtr->numEntries; i++) {
	    mePtr = menuPtr->entries[i];
	    if (mtdPtr->virtualMenuTop + mePtr->y + mePtr->height <
		    menuClipRect.top || mtdPtr->virtualMenuTop + mePtr->y >
		    menuClipRect.bottom) {
		continue;
	    }
#ifdef TK_MAC_DEBUG_MENUS
	    TkMacOSXDbgMsg("Drawing item %i", i);
#endif
	    AppearanceEntryDrawWrapper(mePtr, menuRectPtr, mtdPtr,
		    (Drawable) &macMDEFDrawable, &fontMetrics, menuFont, 1);
	}
	Delay(scrollDelay, NULL);
    }
    mtdPtr->itemSelected = newItem + 1;
    mtdPtr->itemUnderMouse = itemUnderMouse + 1;
    mtdPtr->itemRect = itemRect;
}

/*
 *----------------------------------------------------------------------
 *
 * HandleMenuPopUpMsg --
 *
 *	Handles the MenuDefProc's PopUp message. The menu is
 *	posted with the selected item at the point given in hitPt.
 *
 * Results:
 *	A menu is posted.
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */
void
HandleMenuPopUpMsg(
    MenuRef menu,
    Rect *menuRectPtr,
    Point hitPt,
    SInt16 *whichItem,
    TkMenu *menuPtr)
{
    int maxMenuHeight;
    int oldItem;
    Rect portRect;
    BitMap screenBits;
    static SInt16 menuBarHeight = 0;

#ifdef TK_MAC_DEBUG_MENUS
    TkMacOSXDbgMsg("MDEF: PopUpMsg");
#endif

    if (!menuBarHeight) {
	ChkErr(GetThemeMenuBarHeight, &menuBarHeight);
    }
    GetQDGlobalsScreenBits(&screenBits);

    /*
     * Note that for some oddball reason, h and v are reversed in the
     * point given to us by the MDEF.
     */

    oldItem = *whichItem;
    if (oldItem >= menuPtr->numEntries) {
	oldItem = -1;
    }
    portRect.top = 0;
    portRect.bottom = 1280;
    maxMenuHeight = screenBits.bounds.bottom - screenBits.bounds.top
	    - menuBarHeight - SCREEN_MARGIN;
    if (menuPtr->totalHeight > maxMenuHeight) {
	menuRectPtr->top = menuBarHeight;
    } else {
	int delta;

	menuRectPtr->top = hitPt.h;
	if (oldItem >= 0) {
	    menuRectPtr->top -= menuPtr->entries[oldItem]->y;
	}

	if (menuRectPtr->top < menuBarHeight) {
	    /*
	     * Displace downward if the menu would stick off the top of the
	     * screen.
	     */

	    menuRectPtr->top = menuBarHeight + SCREEN_MARGIN;
	} else {
	    /*
	     * Or upward if the menu sticks off the bottom end...
	     */

	    delta = menuRectPtr->top + menuPtr->totalHeight - maxMenuHeight;
	    if (delta > 0) {
		menuRectPtr->top -= delta;
	    }
	}
    }
    menuRectPtr->left = hitPt.v;
    menuRectPtr->right = menuRectPtr->left + menuPtr->totalWidth;
    menuRectPtr->bottom = menuRectPtr->top +
	    ((maxMenuHeight < menuPtr->totalHeight)
	    ? maxMenuHeight : menuPtr->totalHeight);
    if (menuRectPtr->top == menuBarHeight) {
	*whichItem = hitPt.h;
    } else {
	*whichItem = menuRectPtr->top;
    }
}

/*
 *----------------------------------------------------------------------
 *
 * HandleMenuCalcItemMsg --
 *
 *	Handles the MenuDefProc's CalcItem message. It is supposed
 *	to calculate the Rect of the menu entry in whichItem in the
 *	menu, and put that in menuRectPtr. I assume this works, but I
 *	have never seen the MenuManager send this message.
 *
 * Results:
 *	The Menu Manager is informed of the bounding rect of a
 *	menu rect.
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */

void
HandleMenuCalcItemMsg(
    MenuRef menu,
    Rect *menuRectPtr,
    Point hitPt,
    SInt16 *whichItem,
    TkMenu *menuPtr)
{
    TkMenuEntry *mePtr;
    MenuTrackingData mtd, *mtdPtr = &mtd;
    OSStatus err;
    int virtualTop, item = *whichItem-1;

    err = ChkErr(GetMenuTrackingData, menu, mtdPtr);
    if (err == noErr) {
	virtualTop = mtdPtr->virtualMenuTop;
    } else {
	virtualTop = 0;
    }

    if (item >= 0 && item < menuPtr->numEntries) {
	mePtr = menuPtr->entries[item];
	menuRectPtr->left = mePtr->x;
	menuRectPtr->top = mePtr->y + virtualTop;
	if (mePtr->entryFlags & ENTRY_LAST_COLUMN) {
	    menuRectPtr->right = menuPtr->totalWidth;
	} else {
	    menuRectPtr->right = mePtr->x + mePtr->width;
	}
	menuRectPtr->bottom = menuRectPtr->top + mePtr->height;
    }
#ifdef TK_MAC_DEBUG_MENUS
    TkMacOSXDbgMsg("MDEF: CalcItemMsg %d: %d, %d", *whichItem,
	    menuRectPtr->left, menuRectPtr->top);
#endif
}
#endif /* USE_TK_MDEF */
