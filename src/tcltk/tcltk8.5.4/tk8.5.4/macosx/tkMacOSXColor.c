/*
 * tkMacOSXColor.c --
 *
 *	This file maintains a database of color values for the Tk
 *	toolkit, in order to avoid round-trips to the server to
 *	map color names to pixel values.
 *
 * Copyright (c) 1990-1994 The Regents of the University of California.
 * Copyright (c) 1994-1996 Sun Microsystems, Inc.
 * Copyright 2001, Apple Computer, Inc.
 * Copyright (c) 2006-2007 Daniel A. Steffen <das@users.sourceforge.net>
 *
 * See the file "license.terms" for information on usage and redistribution
 * of this file, and for a DISCLAIMER OF ALL WARRANTIES.
 *
 * RCS: @(#) $Id: tkMacOSXColor.c,v 1.15 2007/12/13 15:27:08 dgp Exp $
 */

#include "tkMacOSXPrivate.h"
#include "tkColor.h"

#if MAC_OS_X_VERSION_MIN_REQUIRED < 1040
/* Undocumented CG API for creating CGPattern from CGImage */
extern CGPatternRef CGPatternCreateWithImage(CGImageRef img, int i) WEAK_IMPORT_ATTRIBUTE;
#endif

struct SystemColorMapEntry {
    const char *name;
    ThemeBrush brush;
    ThemeTextColor textColor;
    ThemeBackgroundKind background;
};  /* unsigned char pixelCode; */

/*
 * Array of system color definitions: the array index is required to equal the
 * color's (pixelCode - MIN_PIXELCODE), i.e. the array order needs to be kept
 * in sync with the public pixel code values in tkMacOSXPort.h !
 */

#define MIN_PIXELCODE  30
static const struct SystemColorMapEntry systemColorMap[] = {
    { "Transparent",			    0, 0, 0 },							/*  30: TRANSPARENT_PIXEL */
    { "Highlight",			    kThemeBrushPrimaryHighlightColor, 0, 0 },			/*  31: HIGHLIGHT_PIXEL */
    { "HighlightSecondary",		    kThemeBrushSecondaryHighlightColor, 0, 0 },			/*  32: HIGHLIGHT_SECONDARY_PIXEL */
    { "HighlightText",			    kThemeBrushBlack, 0, 0 },					/*  33: HIGHLIGHT_TEXT_PIXEL */
    { "HighlightAlternate",		    kThemeBrushAlternatePrimaryHighlightColor, 0, 0 },		/*  34: HIGHLIGHT_ALTERNATE_PIXEL */
    { "ButtonText",			    0, kThemeTextColorPushButtonActive, 0 },			/*  35: CONTROL_TEXT_PIXEL */
    { "PrimaryHighlightColor",		    kThemeBrushPrimaryHighlightColor, 0, 0 },			/*  36 */
    { "ButtonFace",			    kThemeBrushButtonFaceActive, 0, 0 },			/*  37: CONTROL_BODY_PIXEL */
    { "SecondaryHighlightColor",	    kThemeBrushSecondaryHighlightColor, 0, 0 },			/*  38 */
    { "ButtonFrame",			    kThemeBrushButtonFrameActive, 0, 0 },			/*  39: CONTROL_FRAME_PIXEL */
    { "AlternatePrimaryHighlightColor",	    kThemeBrushAlternatePrimaryHighlightColor, 0, 0 },		/*  40 */
    { "WindowBody",			    kThemeBrushDocumentWindowBackground, 0, 0 },		/*  41: WINDOW_BODY_PIXEL */
    { "SheetBackground",		    kThemeBrushSheetBackground, 0, 0 },				/*  42 */
    { "MenuActive",			    kThemeBrushMenuBackgroundSelected, 0, 0 },			/*  43: MENU_ACTIVE_PIXEL */
    { "Black",				    kThemeBrushBlack, 0, 0 },					/*  44 */
    { "MenuActiveText",			    0, kThemeTextColorMenuItemSelected, 0 },			/*  45: MENU_ACTIVE_TEXT_PIXEL */
    { "White",				    kThemeBrushWhite, 0, 0 },					/*  46 */
    { "Menu",				    kThemeBrushMenuBackground, 0, 0 },				/*  47: MENU_BACKGROUND_PIXEL */
    { "DialogBackgroundActive",		    kThemeBrushDialogBackgroundActive, 0, 0 },			/*  48 */
    { "MenuDisabled",			    0, kThemeTextColorMenuItemDisabled, 0 },			/*  49: MENU_DISABLED_PIXEL */
    { "DialogBackgroundInactive",	    kThemeBrushDialogBackgroundInactive, 0, 0 },		/*  50 */
    { "MenuText",			    0, kThemeTextColorMenuItemActive, 0 },			/*  51: MENU_TEXT_PIXEL */
    { "AppearanceColor",		    0, 0, 0 },							/*  52: APPEARANCE_PIXEL */
    { "AlertBackgroundActive",		    kThemeBrushAlertBackgroundActive, 0, 0 },			/*  53 */
    { "AlertBackgroundInactive",	    kThemeBrushAlertBackgroundInactive, 0, 0 },			/*  54 */
    { "ModelessDialogBackgroundActive",	    kThemeBrushModelessDialogBackgroundActive, 0, 0 },		/*  55 */
    { "ModelessDialogBackgroundInactive",   kThemeBrushModelessDialogBackgroundInactive, 0, 0 },	/*  56 */
    { "UtilityWindowBackgroundActive",	    kThemeBrushUtilityWindowBackgroundActive, 0, 0 },		/*  57 */
    { "UtilityWindowBackgroundInactive",    kThemeBrushUtilityWindowBackgroundInactive, 0, 0 },		/*  58 */
    { "ListViewSortColumnBackground",	    kThemeBrushListViewSortColumnBackground, 0, 0 },		/*  59 */
    { "ListViewBackground",		    kThemeBrushListViewBackground, 0, 0 },			/*  60 */
    { "IconLabelBackground",		    kThemeBrushIconLabelBackground, 0, 0 },			/*  61 */
    { "ListViewSeparator",		    kThemeBrushListViewSeparator, 0, 0 },			/*  62 */
    { "ChasingArrows",			    kThemeBrushChasingArrows, 0, 0 },				/*  63 */
    { "DragHilite",			    kThemeBrushDragHilite, 0, 0 },				/*  64 */
    { "DocumentWindowBackground",	    kThemeBrushDocumentWindowBackground, 0, 0 },		/*  65 */
    { "FinderWindowBackground",		    kThemeBrushFinderWindowBackground, 0, 0 },			/*  66 */
    { "ScrollBarDelimiterActive",	    kThemeBrushScrollBarDelimiterActive, 0, 0 },		/*  67 */
    { "ScrollBarDelimiterInactive",	    kThemeBrushScrollBarDelimiterInactive, 0, 0 },		/*  68 */
    { "FocusHighlight",			    kThemeBrushFocusHighlight, 0, 0 },				/*  69 */
    { "PopupArrowActive",		    kThemeBrushPopupArrowActive, 0, 0 },			/*  70 */
    { "PopupArrowPressed",		    kThemeBrushPopupArrowPressed, 0, 0 },			/*  71 */
    { "PopupArrowInactive",		    kThemeBrushPopupArrowInactive, 0, 0 },			/*  72 */
    { "AppleGuideCoachmark",		    kThemeBrushAppleGuideCoachmark, 0, 0 },			/*  73 */
    { "IconLabelBackgroundSelected",	    kThemeBrushIconLabelBackgroundSelected, 0, 0 },		/*  74 */
    { "StaticAreaFill",			    kThemeBrushStaticAreaFill, 0, 0 },				/*  75 */
    { "ActiveAreaFill",			    kThemeBrushActiveAreaFill, 0, 0 },				/*  76 */
    { "ButtonFrameActive",		    kThemeBrushButtonFrameActive, 0, 0 },			/*  77 */
    { "ButtonFrameInactive",		    kThemeBrushButtonFrameInactive, 0, 0 },			/*  78 */
    { "ButtonFaceActive",		    kThemeBrushButtonFaceActive, 0, 0 },			/*  79 */
    { "ButtonFaceInactive",		    kThemeBrushButtonFaceInactive, 0, 0 },			/*  80 */
    { "ButtonFacePressed",		    kThemeBrushButtonFacePressed, 0, 0 },			/*  81 */
    { "ButtonActiveDarkShadow",		    kThemeBrushButtonActiveDarkShadow, 0, 0 },			/*  82 */
    { "ButtonActiveDarkHighlight",	    kThemeBrushButtonActiveDarkHighlight, 0, 0 },		/*  83 */
    { "ButtonActiveLightShadow",	    kThemeBrushButtonActiveLightShadow, 0, 0 },			/*  84 */
    { "ButtonActiveLightHighlight",	    kThemeBrushButtonActiveLightHighlight, 0, 0 },		/*  85 */
    { "ButtonInactiveDarkShadow",	    kThemeBrushButtonInactiveDarkShadow, 0, 0 },		/*  86 */
    { "ButtonInactiveDarkHighlight",	    kThemeBrushButtonInactiveDarkHighlight, 0, 0 },		/*  87 */
    { "ButtonInactiveLightShadow",	    kThemeBrushButtonInactiveLightShadow, 0, 0 },		/*  88 */
    { "ButtonInactiveLightHighlight",	    kThemeBrushButtonInactiveLightHighlight, 0, 0 },		/*  89 */
    { "ButtonPressedDarkShadow",	    kThemeBrushButtonPressedDarkShadow, 0, 0 },			/*  90 */
    { "ButtonPressedDarkHighlight",	    kThemeBrushButtonPressedDarkHighlight, 0, 0 },		/*  91 */
    { "ButtonPressedLightShadow",	    kThemeBrushButtonPressedLightShadow, 0, 0 },		/*  92 */
    { "ButtonPressedLightHighlight",	    kThemeBrushButtonPressedLightHighlight, 0, 0 },		/*  93 */
    { "BevelActiveLight",		    kThemeBrushBevelActiveLight, 0, 0 },			/*  94 */
    { "BevelActiveDark",		    kThemeBrushBevelActiveDark, 0, 0 },				/*  95 */
    { "BevelInactiveLight",		    kThemeBrushBevelInactiveLight, 0, 0 },			/*  96 */
    { "BevelInactiveDark",		    kThemeBrushBevelInactiveDark, 0, 0 },			/*  97 */
    { "NotificationWindowBackground",	    kThemeBrushNotificationWindowBackground, 0, 0 },		/*  98 */
    { "MovableModalBackground",		    kThemeBrushMovableModalBackground, 0, 0 },			/*  99 */
    { "SheetBackgroundOpaque",		    kThemeBrushSheetBackgroundOpaque, 0, 0 },			/* 100 */
    { "DrawerBackground",		    kThemeBrushDrawerBackground, 0, 0 },			/* 101 */
    { "ToolbarBackground",		    kThemeBrushToolbarBackground, 0, 0 },			/* 102 */
    { "SheetBackgroundTransparent",	    kThemeBrushSheetBackgroundTransparent, 0, 0 },		/* 103 */
    { "MenuBackground",			    kThemeBrushMenuBackground, 0, 0 },				/* 104 */
    { "Pixel",				    0, 0, 0 },							/* 105: PIXEL_MAGIC */
    { "MenuBackgroundSelected",		    kThemeBrushMenuBackgroundSelected, 0, 0 },			/* 106 */
    { "ListViewOddRowBackground",	    kThemeBrushListViewOddRowBackground, 0, 0 },		/* 107 */
    { "ListViewEvenRowBackground",	    kThemeBrushListViewEvenRowBackground, 0, 0 },		/* 108 */
    { "ListViewColumnDivider",		    kThemeBrushListViewColumnDivider, 0, 0 },			/* 109 */
    { "BlackText",			    0, kThemeTextColorBlack, 0 },				/* 110 */
    { "DialogActiveText",		    0, kThemeTextColorDialogActive, 0 },			/* 111 */
    { "DialogInactiveText",		    0, kThemeTextColorDialogInactive, 0 },			/* 112 */
    { "AlertActiveText",		    0, kThemeTextColorAlertActive, 0 },				/* 113 */
    { "AlertInactiveText",		    0, kThemeTextColorAlertInactive, 0 },			/* 114 */
    { "ModelessDialogActiveText",	    0, kThemeTextColorModelessDialogActive, 0 },		/* 115 */
    { "ModelessDialogInactiveText",	    0, kThemeTextColorModelessDialogInactive, 0 },		/* 116 */
    { "WindowHeaderActiveText",		    0, kThemeTextColorWindowHeaderActive, 0 },			/* 117 */
    { "WindowHeaderInactiveText",	    0, kThemeTextColorWindowHeaderInactive, 0 },		/* 118 */
    { "PlacardActiveText",		    0, kThemeTextColorPlacardActive, 0 },			/* 119 */
    { "PlacardInactiveText",		    0, kThemeTextColorPlacardInactive, 0 },			/* 120 */
    { "PlacardPressedText",		    0, kThemeTextColorPlacardPressed, 0 },			/* 121 */
    { "PushButtonActiveText",		    0, kThemeTextColorPushButtonActive, 0 },			/* 122 */
    { "PushButtonInactiveText",		    0, kThemeTextColorPushButtonInactive, 0 },			/* 123 */
    { "PushButtonPressedText",		    0, kThemeTextColorPushButtonPressed, 0 },			/* 124 */
    { "BevelButtonActiveText",		    0, kThemeTextColorBevelButtonActive, 0 },			/* 125 */
    { "BevelButtonInactiveText",	    0, kThemeTextColorBevelButtonInactive, 0 },			/* 126 */
    { "BevelButtonPressedText",		    0, kThemeTextColorBevelButtonPressed, 0 },			/* 127 */
    { "PopupButtonActiveText",		    0, kThemeTextColorPopupButtonActive, 0 },			/* 128 */
    { "PopupButtonInactiveText",	    0, kThemeTextColorPopupButtonInactive, 0 },			/* 129 */
    { "PopupButtonPressedText",		    0, kThemeTextColorPopupButtonPressed, 0 },			/* 130 */
    { "IconLabelText",			    0, kThemeTextColorIconLabel, 0 },				/* 131 */
    { "ListViewText",			    0, kThemeTextColorListView, 0 },				/* 132 */
    { "DocumentWindowTitleActiveText",	    0, kThemeTextColorDocumentWindowTitleActive, 0 },		/* 133 */
    { "DocumentWindowTitleInactiveText",    0, kThemeTextColorDocumentWindowTitleInactive, 0 },		/* 134 */
    { "MovableModalWindowTitleActiveText",  0, kThemeTextColorMovableModalWindowTitleActive, 0 },	/* 135 */
    { "MovableModalWindowTitleInactiveText",0, kThemeTextColorMovableModalWindowTitleInactive, 0 },	/* 136 */
    { "UtilityWindowTitleActiveText",	    0, kThemeTextColorUtilityWindowTitleActive, 0 },		/* 137 */
    { "UtilityWindowTitleInactiveText",	    0, kThemeTextColorUtilityWindowTitleInactive, 0 },		/* 138 */
    { "PopupWindowTitleActiveText",	    0, kThemeTextColorPopupWindowTitleActive, 0 },		/* 139 */
    { "PopupWindowTitleInactiveText",	    0, kThemeTextColorPopupWindowTitleInactive, 0 },		/* 140 */
    { "RootMenuActiveText",		    0, kThemeTextColorRootMenuActive, 0 },			/* 141 */
    { "RootMenuSelectedText",		    0, kThemeTextColorRootMenuSelected, 0 },			/* 142 */
    { "RootMenuDisabledText",		    0, kThemeTextColorRootMenuDisabled, 0 },			/* 143 */
    { "MenuItemActiveText",		    0, kThemeTextColorMenuItemActive, 0 },			/* 144 */
    { "MenuItemSelectedText",		    0, kThemeTextColorMenuItemSelected, 0 },			/* 145 */
    { "MenuItemDisabledText",		    0, kThemeTextColorMenuItemDisabled, 0 },			/* 146 */
    { "PopupLabelActiveText",		    0, kThemeTextColorPopupLabelActive, 0 },			/* 147 */
    { "PopupLabelInactiveText",		    0, kThemeTextColorPopupLabelInactive, 0 },			/* 148 */
    { "TabFrontActiveText",		    0, kThemeTextColorTabFrontActive, 0 },			/* 149 */
    { "TabNonFrontActiveText",		    0, kThemeTextColorTabNonFrontActive, 0 },			/* 150 */
    { "TabNonFrontPressedText",		    0, kThemeTextColorTabNonFrontPressed, 0 },			/* 151 */
    { "TabFrontInactiveText",		    0, kThemeTextColorTabFrontInactive, 0 },			/* 152 */
    { "TabNonFrontInactiveText",	    0, kThemeTextColorTabNonFrontInactive, 0 },			/* 153 */
    { "IconLabelSelectedText",		    0, kThemeTextColorIconLabelSelected, 0 },			/* 154 */
    { "BevelButtonStickyActiveText",	    0, kThemeTextColorBevelButtonStickyActive, 0 },		/* 155 */
    { "BevelButtonStickyInactiveText",	    0, kThemeTextColorBevelButtonStickyInactive, 0 },		/* 156 */
    { "NotificationText",		    0, kThemeTextColorNotification, 0 },			/* 157 */
    { "SystemDetailText",		    0, kThemeTextColorSystemDetail, 0 },			/* 158 */
    { "WhiteText",			    0, kThemeTextColorWhite, 0 },				/* 159 */
    { "TabPaneBackground",		    0, 0, kThemeBackgroundTabPane },				/* 160 */
    { "PlacardBackground",		    0, 0, kThemeBackgroundPlacard },				/* 161 */
    { "WindowHeaderBackground",		    0, 0, kThemeBackgroundWindowHeader },			/* 162 */
    { "ListViewWindowHeaderBackground",	    0, 0, kThemeBackgroundListViewWindowHeader },		/* 163 */
    { "SecondaryGroupBoxBackground",	    0, 0, kThemeBackgroundSecondaryGroupBox },			/* 164 */
    { "MetalBackground",		    0, 0, kThemeBackgroundMetal },				/* 165 */
    { NULL,				    0, 0, 0 }
};
#define MAX_PIXELCODE 165

/*
 *----------------------------------------------------------------------
 *
 * GetThemeFromPixelCode --
 *
 *	When given a pixel code corresponding to a theme system color,
 *	set one of brush, textColor or background to the corresponding
 *	Appearance Mgr theme constant.
 *
 * Results:
 *	Returns false if not a real pixel, true otherwise.
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */

static int
GetThemeFromPixelCode(
    unsigned char code,
    ThemeBrush *brush,
    ThemeTextColor *textColor,
    ThemeBackgroundKind *background)
{
    if (code >= MIN_PIXELCODE && code <= MAX_PIXELCODE && code != PIXEL_MAGIC) {
	*brush = systemColorMap[code - MIN_PIXELCODE].brush;
	*textColor = systemColorMap[code - MIN_PIXELCODE].textColor;
	*background = systemColorMap[code - MIN_PIXELCODE].background;
    } else {
	*brush = 0;
	*textColor = 0;
	*background = 0;
    }
    if (!*brush && !*textColor && !*background && code != PIXEL_MAGIC) {
	return false;
    } else {
	return true;
    }
}

/*
 *----------------------------------------------------------------------
 *
 * GetThemeColor --
 *
 *	Get RGB color for a given system color or pixel value.
 *
 * Results:
 *	OSStatus
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */

static OSStatus
GetThemeColor(
    unsigned long pixel,
    ThemeBrush brush,
    ThemeTextColor textColor,
    ThemeBackgroundKind background,
    RGBColor *c)
{
    OSStatus err = noErr;

    if (brush) {
	err = ChkErr(GetThemeBrushAsColor,
		brush == kThemeBrushMenuBackgroundSelected ?
		kThemeBrushFocusHighlight : brush, 32, true, c);
    } else if (textColor) {
	err = ChkErr(GetThemeTextColor, textColor, 32, true, c);
    } else {
	c->red	  = (pixel >> 16) & 0xff;
	c->green  = (pixel >>  8) & 0xff;
	c->blue	  = (pixel	) & 0xff;
	c->red	 |= c->red   << 8;
	c->green |= c->green << 8;
	c->blue	 |= c->blue  << 8;
    }
    return err;
}

/*
 *----------------------------------------------------------------------
 *
 * TkSetMacColor --
 *
 *	Populates a Macintosh RGBColor structure from a X style
 *	pixel value.
 *
 * Results:
 *	Returns false if not a real pixel, true otherwise.
 *
 * Side effects:
 *	The variable macColor is updated to the pixels value.
 *
 *----------------------------------------------------------------------
 */

int
TkSetMacColor(
    unsigned long pixel,		/* Pixel value to convert. */
    RGBColor *macColor)			/* Mac color struct to modify. */
{
    OSStatus err = -1;
    ThemeBrush brush;
    ThemeTextColor textColor;
    ThemeBackgroundKind background;

    if (GetThemeFromPixelCode((pixel >> 24) & 0xff, &brush, &textColor,
	    &background)) {
	err = ChkErr(GetThemeColor, pixel, brush, textColor, background,
		macColor);
    }
    return (err == noErr);
}

/*
 *----------------------------------------------------------------------
 *
 * TkMacOSXSetColorInPort --
 *
 *	Sets fore or back color in the given QD port from an X pixel
 *	value, and if the pixel code indicates a system color, sets
 *	the corresponding brush, textColor or background via
 *	Appearance mgr APIs.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	If penPat is non-NULL it is set to the forground color/pattern.
 *
 *----------------------------------------------------------------------
 */

void
TkMacOSXSetColorInPort(
    unsigned long pixel,
    int fg,
    PixPatHandle penPat,
    CGrafPtr port)
{
    OSStatus err;
    RGBColor c;
    ThemeBrush brush;
    ThemeTextColor textColor;
    ThemeBackgroundKind background;
    int setPenPat = 0;

    if (GetThemeFromPixelCode((pixel >> 24) & 0xff, &brush, &textColor,
	    &background)) {
	CGrafPtr savePort;
	Boolean portChanged;

	portChanged = QDSwapPort(port, &savePort);
	err = ChkErr(GetThemeColor, pixel, brush, textColor, background, &c);
	if (err == noErr) {
	    if (fg) {
		RGBForeColor(&c);
		if (penPat) {
		    MakeRGBPat(penPat, &c);
		    setPenPat = 1;
		}
	    } else {
		RGBBackColor(&c);
	    }
	}
	err = -1;
	if (brush) {
	    err = ChkErr(SetThemeBackground,
		    brush == kThemeBrushMenuBackgroundSelected ?
		    kThemeBrushFocusHighlight : brush, 32, true);
	} else if (textColor && fg) {
	    err = ChkErr(SetThemeTextColor, textColor, 32, true);
	} else if (background) {
	    Rect bounds;

	    GetPortBounds(port, &bounds);
	    err = ChkErr(ApplyThemeBackground, background, &bounds,
		    kThemeStateActive, 32, true);
	}
	if (penPat && err == noErr && (brush || background)) {
	    GetPortBackPixPat(port, penPat);
	    setPenPat = 1;
	}
	if (portChanged) {
	    QDSwapPort(savePort, NULL);
	}
    } else {
	TkMacOSXDbgMsg("Ignored unknown pixel value 0x%lx", pixel);
    }
    if (penPat && !setPenPat) {
	GetPortBackPixPat(port, penPat);
    }
}

/*
 *----------------------------------------------------------------------
 *
 * TkMacOSXSetColorInContext --
 *
 *	Sets fill and stroke color in the given CG context from an X
 *	pixel value, or if the pixel code indicates a system color,
 *	sets the corresponding brush, textColor or background via
 *	HITheme APIs if available or Appearance mgr APIs.
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
TkMacOSXSetColorInContext(
    unsigned long pixel,
    CGContextRef context)
{
    OSStatus err = -1;
    RGBColor c;
    ThemeBrush brush;
    ThemeTextColor textColor;
    ThemeBackgroundKind background;

    if (GetThemeFromPixelCode((pixel >> 24) & 0xff, &brush, &textColor,
	    &background)) {
	if (brush) {
	    TK_IF_MAC_OS_X_API (4, HIThemeSetFill,
		err = ChkErr(HIThemeSetFill, brush, NULL, context,
			kHIThemeOrientationNormal);
		TK_IF_MAC_OS_X_API_COND (4, HIThemeSetFill, err == noErr,
		    err = ChkErr(HIThemeSetStroke, brush, NULL, context,
			    kHIThemeOrientationNormal);
		) TK_ENDIF
	    ) TK_ENDIF
	} else if (textColor) {
	    TK_IF_MAC_OS_X_API (4, HIThemeSetTextFill,
		err = ChkErr(HIThemeSetTextFill, textColor, NULL, context,
			kHIThemeOrientationNormal);
	    ) TK_ENDIF
	} else if (background) {
	    TK_IF_MAC_OS_X_API (3, CGContextGetClipBoundingBox,
		CGRect rect = CGContextGetClipBoundingBox(context);
		HIThemeBackgroundDrawInfo info = { 0, kThemeStateActive,
			background };

		TK_IF_MAC_OS_X_API (3, HIThemeApplyBackground,
		    TK_IF_HI_TOOLBOX (3, /* c.f. QA1377 */
			err = ChkErr(HIThemeApplyBackground, &rect, &info,
				context, kHIThemeOrientationNormal);
		    ) TK_ENDIF
		) TK_ENDIF
	    ) TK_ENDIF
	}
	if (err == noErr) {
	    return;
	}
#if MAC_OS_X_VERSION_MIN_REQUIRED < 1040
	/*
	 * Convert Appearance theme pattern to CGPattern:
	 */
	if ((brush || background) && CGPatternCreateWithImage != NULL) {
	    static PixPatHandle pixpat = NULL;
	    static GWorldPtr patGWorld = NULL;
	    static uint32_t bitmapInfo = 0;
	    const short patDim = 16;
	    const Rect bounds = {0, 0, patDim, patDim};
	    CGrafPtr savePort;
	    Boolean portChanged;
	    PixMapHandle pixmap;
	    long rowbytes;
	    CGImageRef img;
	    CGColorSpaceRef rgbCspace;
	    CGDataProviderRef provider;

	    if (!pixpat) {
		pixpat = NewPixPat();
		err = ChkErr(NewGWorld, &patGWorld, 32, &bounds, NULL, NULL, 0
#ifdef __LITTLE_ENDIAN__
			| kNativeEndianPixMap
#endif
			);
		if (!pixpat || err != noErr || !patGWorld) {
		    Tcl_Panic("TkMacOSXSetColorInContext(): "
			"pattern initialization failed !");
		}
		TK_IF_HI_TOOLBOX (4,
		    bitmapInfo = kCGBitmapByteOrder32Host;
		) TK_ENDIF
	    }
	    portChanged = QDSwapPort(patGWorld, &savePort);
	    TkMacOSXSetColorInPort(pixel, 1, pixpat, patGWorld);
#ifdef TK_MAC_DEBUG
	    Rect patBounds;
	    GetPixBounds((**pixpat).patMap, &patBounds);
	    if (patBounds.right > patDim || patBounds.bottom > patDim) {
		Tcl_Panic("TkMacOSXSetColorInContext(): "
		    "pattern larger than expected !");
	    }
#endif /* TK_MAC_DEBUG */
	    FillCRect(&bounds, pixpat);
	    if (portChanged) {
		QDSwapPort(savePort, NULL);
	    }
	    pixmap = GetPortPixMap(patGWorld);
	    rowbytes = GetPixRowBytes(pixmap);
	    provider = CGDataProviderCreateWithData(&patGWorld,
		    GetPixBaseAddr(pixmap), rowbytes * patDim, NULL);
	    rgbCspace = CGColorSpaceCreateDeviceRGB();
	    img = CGImageCreate(patDim, patDim, 8, 32,
		    rowbytes, rgbCspace, kCGImageAlphaFirst | bitmapInfo,
		    provider, NULL, 0, kCGRenderingIntentDefault);
	    CGColorSpaceRelease(rgbCspace);
	    CGDataProviderRelease(provider);
	    if (img) {
		CGPatternRef pat = CGPatternCreateWithImage(img, 2);
		CGColorSpaceRef patCSpace = CGColorSpaceCreatePattern(NULL);
		const float alpha = 1;

		CGContextSetFillColorSpace(context, patCSpace);
		CGContextSetFillPattern(context, pat, &alpha);
		CGContextSetStrokeColorSpace(context, patCSpace);
		CGContextSetStrokePattern(context, pat, &alpha);
		CGColorSpaceRelease(patCSpace);
		CGPatternRelease(pat);
		CGImageRelease(img);
		return;
	    }
	}
#endif /* MAC_OS_X_VERSION_MIN_REQUIRED < 1040 */
	err = ChkErr(GetThemeColor, pixel, brush, textColor, background, &c);
	if (err == noErr) {
	    double r = c.red   / 65535.0;
	    double g = c.green / 65535.0;
	    double b = c.blue  / 65535.0;

	    CGContextSetRGBFillColor(context, r, g, b, 1.0);
	    CGContextSetRGBStrokeColor(context, r, g, b, 1.0);
	}
    } else if (((pixel >> 24) & 0xff) == TRANSPARENT_PIXEL) {
	CGContextSetRGBFillColor(context, 0.0, 0.0, 0.0, 0.0);
	CGContextSetRGBStrokeColor(context, 0.0, 0.0, 0.0, 0.0);
    } else {
	TkMacOSXDbgMsg("Ignored unknown pixel value 0x%lx", pixel);
    }
}

/*
 *----------------------------------------------------------------------
 *
 * TkpGetColor --
 *
 *	Allocate a new TkColor for the color with the given name.
 *
 * Results:
 *	Returns a newly allocated TkColor, or NULL on failure.
 *
 * Side effects:
 *	May invalidate the colormap cache associated with tkwin upon
 *	allocating a new colormap entry. Allocates a new TkColor
 *	structure.
 *
 *----------------------------------------------------------------------
 */

TkColor *
TkpGetColor(
    Tk_Window tkwin,		/* Window in which color will be used. */
    Tk_Uid name)		/* Name of color to allocated (in form
				 * suitable for passing to XParseColor). */
{
    Display *display = Tk_Display(tkwin);
    Colormap colormap = Tk_Colormap(tkwin);
    TkColor *tkColPtr;
    XColor color;

    /*
     * Check to see if this is a system color. Otherwise, XParseColor
     * will do all the work.
     */
    if (strncasecmp(name, "system", 6) == 0) {
	Tcl_Obj *strPtr = Tcl_NewStringObj(name+6, -1);
	int idx, result;

	result = Tcl_GetIndexFromObjStruct(NULL, strPtr, systemColorMap,
		    sizeof(struct SystemColorMapEntry), NULL, TCL_EXACT, &idx);
	Tcl_DecrRefCount(strPtr);
	if (result == TCL_OK) {
	    OSStatus err;
	    RGBColor c;
	    unsigned char pixelCode = idx + MIN_PIXELCODE;
	    ThemeBrush brush = systemColorMap[idx].brush;
	    ThemeTextColor textColor = systemColorMap[idx].textColor;
	    ThemeBackgroundKind background = systemColorMap[idx].background;

	    err = ChkErr(GetThemeColor, 0, brush, textColor, background, &c);
	    if (err == noErr) {
		color.red   = c.red;
		color.green = c.green;
		color.blue  = c.blue;
		color.pixel = ((((((pixelCode << 8)
		    | ((color.red   >> 8) & 0xff)) << 8)
		    | ((color.green >> 8) & 0xff)) << 8)
		    | ((color.blue  >> 8) & 0xff));
		goto validXColor;
	    }
	}
    }

    if (XParseColor(display, colormap, name, &color) == 0) {
	return (TkColor *) NULL;
    }

validXColor:
    tkColPtr = (TkColor *) ckalloc(sizeof(TkColor));
    tkColPtr->color = color;

    return tkColPtr;
}

/*
 *----------------------------------------------------------------------
 *
 * TkpGetColorByValue --
 *
 *	Given a desired set of red-green-blue intensities for a color,
 *	locate a pixel value to use to draw that color in a given
 *	window.
 *
 * Results:
 *	The return value is a pointer to an TkColor structure that
 *	indicates the closest red, blue, and green intensities available
 *	to those specified in colorPtr, and also specifies a pixel
 *	value to use to draw in that color.
 *
 * Side effects:
 *	May invalidate the colormap cache for the specified window.
 *	Allocates a new TkColor structure.
 *
 *----------------------------------------------------------------------
 */

TkColor *
TkpGetColorByValue(
    Tk_Window tkwin,		/* Window in which color will be used. */
    XColor *colorPtr)		/* Red, green, and blue fields indicate
				 * desired color. */
{
    TkColor *tkColPtr = (TkColor *) ckalloc(sizeof(TkColor));

    tkColPtr->color.red = colorPtr->red;
    tkColPtr->color.green = colorPtr->green;
    tkColPtr->color.blue = colorPtr->blue;
    tkColPtr->color.pixel = TkpGetPixel(&tkColPtr->color);
    return tkColPtr;
}

#if !TK_DRAW_IN_CONTEXT
/*
 *----------------------------------------------------------------------
 *
 * TkMacOSXCompareColors --
 *
 *	On Mac, color codes may specify symbolic values like "highlight
 *	foreground", but we really need the actual values to compare.
 *	Maybe see also: "TIP #154: Add Named Colors to Tk".
 *
 * Results:
 *	Returns true if both colors are the same, false otherwise.
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */

int
TkMacOSXCompareColors(
    unsigned long c1,
    unsigned long c2)
{
    RGBColor col1, col2;
    return  TkSetMacColor(c1,&col1) &&
	    TkSetMacColor(c1,&col2) &&
	    !memcmp(&col1,&col2,sizeof(col1));
}
#endif /* !TK_DRAW_IN_CONTEXT */

/*
 *----------------------------------------------------------------------
 *
 * Stub functions --
 *
 *	These functions are just stubs for functions that either
 *	don't make sense on the Mac or have yet to be implemented.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	These calls do nothing - which may not be expected.
 *
 *----------------------------------------------------------------------
 */

Status
XAllocColor(
    Display *display,		/* Display. */
    Colormap map,		/* Not used. */
    XColor *colorPtr)		/* XColor struct to modify. */
{
    display->request++;
    colorPtr->pixel = TkpGetPixel(colorPtr);
    return 1;
}

Colormap
XCreateColormap(
    Display *display,		/* Display. */
    Window window,		/* X window. */
    Visual *visual,		/* Not used. */
    int alloc)			/* Not used. */
{
    static Colormap index = 1;

    /*
     * Just return a new value each time.
     */
    return index++;
}

void
XFreeColormap(
    Display* display,		/* Display. */
    Colormap colormap)		/* Colormap. */
{
}

void
XFreeColors(
    Display* display,		/* Display. */
    Colormap colormap,		/* Colormap. */
    unsigned long* pixels,	/* Array of pixels. */
    int npixels,		/* Number of pixels. */
    unsigned long planes)	/* Number of pixel planes. */
{
    /*
     * The Macintosh version of Tk uses TrueColor. Nothing
     * needs to be done to release colors as there really is
     * no colormap in the Tk sense.
     */
}
