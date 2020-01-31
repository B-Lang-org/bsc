/*
 * tkMacOSXPrivate.h --
 *
 *	Macros and declarations that are purely internal & private to TkAqua.
 *
 * Copyright (c) 2005-2007 Daniel A. Steffen <das@users.sourceforge.net>
 *
 * See the file "license.terms" for information on usage and redistribution
 * of this file, and for a DISCLAIMER OF ALL WARRANTIES.
 *
 * RCS: @(#) $Id: tkMacOSXPrivate.h,v 1.6.2.1 2008/06/19 00:13:10 das Exp $
 */

#ifndef _TKMACPRIV
#define _TKMACPRIV

#ifndef _TKMACINT
#include "tkMacOSXInt.h"
#endif

/* Define constants only available on Mac OS X 10.3 or later */
#if MAC_OS_X_VERSION_MAX_ALLOWED < 1030
    #define kEventAppAvailableWindowBoundsChanged 110
    #define kEventParamTransactionID 'trns'
    #define kEventParamWindowPartCode 'wpar'
    #define typeWindowPartCode 'wpar'
    #define kMenuAttrDoNotUseUserCommandKeys (1 << 7)
    #define kSimpleWindowClass 18
    #define kWindowDoesNotCycleAttribute (1L << 15)
    #define kWindowAsyncDragAttribute (1L << 23)
    #define kThemeBrushAlternatePrimaryHighlightColor -5
    #define kThemeResizeUpCursor 19
    #define kThemeResizeDownCursor 19
    #define kThemeResizeUpDownCursor 19
    #define kThemePoofCursor 19
    #define kThemeBackgroundMetal 6
    #define kThemeIncDecButtonSmall 21
    #define kThemeIncDecButtonMini 22
    #define kThemeComboBox 16
    #define kThemeMiniSystemFont 109
    #define kAppearancePartUpButton 20
    #define kAppearancePartDownButton 21
    #define kAppearancePartPageUpArea 22
    #define kAppearancePartPageDownArea 23
    #define kAppearancePartIndicator 129
    #define kUIModeAllSuppressed 4
    #define FixedToInt(a) ((short)(((Fixed)(a) + fixed1/2) >> 16))
    #define IntToFixed(a) ((Fixed)(a) << 16)
#endif
/* Define constants only available on Mac OS X 10.4 or later */
#if MAC_OS_X_VERSION_MAX_ALLOWED < 1040
    #define kWindowNoTitleBarAttribute (1L << 9)
    #define kWindowMetalNoContentSeparatorAttribute (1L << 11)
    #define kThemeDisclosureTriangle 6
    #define kThemeBrushListViewOddRowBackground 56
    #define kThemeBrushListViewEvenRowBackground 57
    #define kThemeBrushListViewColumnDivider 58
    #define kThemeMetricScrollBarMinThumbHeight 132
    #define kThemeMetricSmallScrollBarMinThumbHeight 134
    #define kThemeScrollBarMedium kThemeMediumScrollBar
    #define kThemeScrollBarSmall kThemeSmallScrollBar
    #ifdef __BIG_ENDIAN__
    #define kCGBitmapByteOrder32Host (4 << 12)
    #else
    #define kCGBitmapByteOrder32Host (2 << 12)
    #endif
    #endif
/* Define constants only available on Mac OS X 10.5 or later */
#if MAC_OS_X_VERSION_MAX_ALLOWED < 1050
    #define kWindowUnifiedTitleAndToolbarAttribute (1L << 7)
    #define kWindowTexturedSquareCornersAttribute (1L << 10)
#endif
/* HIToolbox version constants */
#ifndef kHIToolboxVersionNumber10_3
    #define kHIToolboxVersionNumber10_3 (145)
#endif
#ifndef kHIToolboxVersionNumber10_4
    #define kHIToolboxVersionNumber10_4 (219)
#endif
#ifndef kHIToolboxVersionNumber10_5
    #define kHIToolboxVersionNumber10_5 (343)
#endif
/* Macros for HIToolbox runtime version checking */
MODULE_SCOPE float tkMacOSXToolboxVersionNumber;
#define TK_IF_HI_TOOLBOX(vers, ...) \
	tk_if_mac_os_x_min_10_##vers(tkMacOSXToolboxVersionNumber >= \
	kHIToolboxVersionNumber10_##vers, 1, __VA_ARGS__)
#define TK_ELSE_HI_TOOLBOX(vers, ...) \
	tk_else_mac_os_x_min_10_##vers(__VA_ARGS__)
/* Macros for Mac OS X API availability checking */
#define TK_IF_MAC_OS_X_API(vers, symbol, ...) \
	tk_if_mac_os_x_10_##vers(symbol != NULL, 1, __VA_ARGS__)
#define TK_ELSE_MAC_OS_X(vers, ...) \
	tk_else_mac_os_x_10_##vers(__VA_ARGS__)
#define TK_IF_MAC_OS_X_API_COND(vers, symbol, cond, ...) \
	tk_if_mac_os_x_10_##vers(symbol != NULL, cond, __VA_ARGS__)
#define TK_ELSE(...) \
	} else { __VA_ARGS__
#define TK_ENDIF \
	}
/* Private macros that implement the checking macros above */
#define tk_if_mac_os_x_yes(chk, cond, ...) \
	if (cond) { __VA_ARGS__
#define tk_else_mac_os_x_yes(...) \
	} else {
#define tk_if_mac_os_x_chk(chk, cond, ...) \
	if ((chk) && (cond)) { __VA_ARGS__
#define tk_else_mac_os_x_chk(...) \
	} else { __VA_ARGS__
#define tk_if_mac_os_x_no(chk, cond, ...) \
	if (0) {
#define tk_else_mac_os_x_no(...) \
	} else { __VA_ARGS__
/* Private mapping macros defined according to Mac OS X version requirements */
/* 10.3 Panther */
#if MAC_OS_X_VERSION_MIN_REQUIRED >= 1030
#define tk_if_mac_os_x_min_10_3		tk_if_mac_os_x_yes
#define tk_else_mac_os_x_min_10_3	tk_else_mac_os_x_yes
#if MAC_OS_X_VERSION_MAX_ALLOWED >= 1030
#define tk_if_mac_os_x_10_3		tk_if_mac_os_x_yes
#define tk_else_mac_os_x_10_3		tk_else_mac_os_x_yes
#endif /* MAC_OS_X_VERSION_MAX_ALLOWED */
#else /* MAC_OS_X_VERSION_MIN_REQUIRED */
#define tk_if_mac_os_x_min_10_3		tk_if_mac_os_x_chk
#define tk_else_mac_os_x_min_10_3	tk_else_mac_os_x_chk
#if MAC_OS_X_VERSION_MAX_ALLOWED >= 1030
#define tk_if_mac_os_x_10_3		tk_if_mac_os_x_chk
#define tk_else_mac_os_x_10_3		tk_else_mac_os_x_chk
#endif /* MAC_OS_X_VERSION_MAX_ALLOWED */
#endif /* MAC_OS_X_VERSION_MIN_REQUIRED */
#if MAC_OS_X_VERSION_MAX_ALLOWED < 1030
#define tk_if_mac_os_x_10_3		tk_if_mac_os_x_no
#define tk_else_mac_os_x_10_3		tk_else_mac_os_x_no
#endif /* MAC_OS_X_VERSION_MAX_ALLOWED */
/* 10.4 Tiger */
#if MAC_OS_X_VERSION_MIN_REQUIRED >= 1040
#define tk_if_mac_os_x_min_10_4		tk_if_mac_os_x_yes
#define tk_else_mac_os_x_min_10_4	tk_else_mac_os_x_yes
#if MAC_OS_X_VERSION_MAX_ALLOWED >= 1040
#define tk_if_mac_os_x_10_4		tk_if_mac_os_x_yes
#define tk_else_mac_os_x_10_4		tk_else_mac_os_x_yes
#endif /* MAC_OS_X_VERSION_MAX_ALLOWED */
#else /* MAC_OS_X_VERSION_MIN_REQUIRED */
#define tk_if_mac_os_x_min_10_4		tk_if_mac_os_x_chk
#define tk_else_mac_os_x_min_10_4	tk_else_mac_os_x_chk
#if MAC_OS_X_VERSION_MAX_ALLOWED >= 1040
#define tk_if_mac_os_x_10_4		tk_if_mac_os_x_chk
#define tk_else_mac_os_x_10_4		tk_else_mac_os_x_chk
#endif /* MAC_OS_X_VERSION_MAX_ALLOWED */
#endif /* MAC_OS_X_VERSION_MIN_REQUIRED */
#if MAC_OS_X_VERSION_MAX_ALLOWED < 1040
#define tk_if_mac_os_x_10_4		tk_if_mac_os_x_no
#define tk_else_mac_os_x_10_4		tk_else_mac_os_x_no
#endif /* MAC_OS_X_VERSION_MAX_ALLOWED */
/* 10.5 Leopard */
#if MAC_OS_X_VERSION_MIN_REQUIRED >= 1050
#define tk_if_mac_os_x_min_10_5		tk_if_mac_os_x_yes
#define tk_else_mac_os_x_min_10_5	tk_else_mac_os_x_yes
#if MAC_OS_X_VERSION_MAX_ALLOWED >= 1050
#define tk_if_mac_os_x_10_5		tk_if_mac_os_x_yes
#define tk_else_mac_os_x_10_5		tk_else_mac_os_x_yes
#endif /* MAC_OS_X_VERSION_MAX_ALLOWED */
#else /* MAC_OS_X_VERSION_MIN_REQUIRED */
#define tk_if_mac_os_x_min_10_5		tk_if_mac_os_x_chk
#define tk_else_mac_os_x_min_10_5	tk_else_mac_os_x_chk
#if MAC_OS_X_VERSION_MAX_ALLOWED >= 1050
#define tk_if_mac_os_x_10_5		tk_if_mac_os_x_chk
#define tk_else_mac_os_x_10_5		tk_else_mac_os_x_chk
#endif /* MAC_OS_X_VERSION_MAX_ALLOWED */
#endif /* MAC_OS_X_VERSION_MIN_REQUIRED */
#if MAC_OS_X_VERSION_MAX_ALLOWED < 1050
#define tk_if_mac_os_x_10_5		tk_if_mac_os_x_no
#define tk_else_mac_os_x_10_5		tk_else_mac_os_x_no
#endif /* MAC_OS_X_VERSION_MAX_ALLOWED */

/*
 * Macros for DEBUG_ASSERT_MESSAGE et al from Debugging.h.
 */

#undef kComponentSignatureString
#undef COMPONENT_SIGNATURE
#define kComponentSignatureString "TkMacOSX"
#define COMPONENT_SIGNATURE 'Tk  '

/*
 * Macros abstracting checks only active in a debug build.
 */

#ifdef TK_MAC_DEBUG
/*
 * Macro to do debug message output.
 */
#define TkMacOSXDbgMsg(m, ...) do { \
	    fprintf(stderr, "%s:%d: %s(): " m "\n", strrchr(__FILE__, '/')+1, \
	    __LINE__, __func__, ##__VA_ARGS__); \
	} while (0)
/*
 * Macro to do debug API failure message output.
 */
#if !defined(DEBUGLEVEL) || !DEBUGLEVEL
#define TkMacOSXDbgOSErr(f, err) do { \
	    TkMacOSXDbgMsg("%s failed: %ld", #f, err); \
	} while (0)
#else
#define TkMacOSXDbgOSErr(f, err) do { \
	    DEBUG_ASSERT_MESSAGE(kComponentSignatureString, #f " failed:", \
	    __func__, 0, strrchr(__FILE__, '/')+1, __LINE__, err); \
	} while (0)
#endif
/*
 * Macro to do very common check for noErr return from given API and output
 * debug message in case of failure.
 */
#define ChkErr(f, ...) ({ \
	OSStatus err = f(__VA_ARGS__); \
	if (err != noErr) { \
	    TkMacOSXDbgOSErr(f, err); \
	} \
	err;})
/*
 * Macro to check emptyness of shared QD tmp region before use in debug builds.
 */
#define TkMacOSXCheckTmpQdRgnEmpty() do { \
	    if (!EmptyRgn(tkMacOSXtmpQdRgn)) { \
		Tcl_Panic("tkMacOSXtmpQdRgn nonempty"); \
	    } \
	} while(0)
#else /* TK_MAC_DEBUG */
#define TkMacOSXDbgMsg(m, ...)
#define TkMacOSXDbgOSErr(f, err)
#define ChkErr(f, ...) ({f(__VA_ARGS__);})
#define TkMacOSXCheckTmpQdRgnEmpty()
#endif /* TK_MAC_DEBUG */

/*
 * Macro abstracting use of TkMacOSXGetNamedSymbol to init named symbols.
 */

#define TkMacOSXInitNamedSymbol(module, ret, symbol, ...) \
    static ret (* symbol)(__VA_ARGS__) = (void*)(-1L); \
    if (symbol == (void*)(-1L)) { \
	symbol = TkMacOSXGetNamedSymbol(STRINGIFY(module), \
		STRINGIFY(_##symbol)); \
    }
MODULE_SCOPE void* TkMacOSXGetNamedSymbol(const char* module,
	const char* symbol);

/*
 * Structure encapsulating current drawing environment.
 */

typedef struct TkMacOSXDrawingContext {
    CGContextRef context;
    CGrafPtr port, savePort;
    ThemeDrawingState saveState;
    RgnHandle saveClip;
    HIShapeRef clipRgn;
    PixPatHandle penPat;
    Rect portBounds;
    Boolean portChanged;
} TkMacOSXDrawingContext;

/*
 * Variables internal to TkAqua.
 */

MODULE_SCOPE RgnHandle tkMacOSXtmpQdRgn;
MODULE_SCOPE int tkMacOSXUseCGDrawing;

/*
 * Prototypes for TkMacOSXRegion.c.
 */

#if 0
MODULE_SCOPE void TkMacOSXEmtpyRegion(TkRegion r);
MODULE_SCOPE int TkMacOSXIsEmptyRegion(TkRegion r);
#endif
MODULE_SCOPE HIShapeRef TkMacOSXGetNativeRegion(TkRegion r);
MODULE_SCOPE void TkMacOSXSetWithNativeRegion(TkRegion r, HIShapeRef rgn);
MODULE_SCOPE void TkMacOSXOffsetRegion(TkRegion r, short dx, short dy);
MODULE_SCOPE HIShapeRef TkMacOSXHIShapeCreateEmpty(void);
MODULE_SCOPE HIMutableShapeRef TkMacOSXHIShapeCreateMutableWithRect(
	const CGRect *inRect);
MODULE_SCOPE OSStatus  TkMacOSXHIShapeSetWithShape(
	HIMutableShapeRef inDestShape, HIShapeRef inSrcShape);
#if 0
MODULE_SCOPE OSStatus TkMacOSXHIShapeSetWithRect(HIMutableShapeRef inShape,
	const CGRect *inRect);
#endif
MODULE_SCOPE OSStatus TkMacOSHIShapeDifferenceWithRect(
	HIMutableShapeRef inShape, const CGRect *inRect);
MODULE_SCOPE OSStatus TkMacOSHIShapeUnionWithRect(HIMutableShapeRef inShape,
	const CGRect *inRect);
MODULE_SCOPE OSStatus TkMacOSHIShapeUnion(HIShapeRef inShape1,
	HIShapeRef inShape2, HIMutableShapeRef outResult);

/*
 * Prototypes of TkAqua internal procs.
 */

MODULE_SCOPE void TkMacOSXDisplayChanged(Display *display);
MODULE_SCOPE void TkMacOSXInitScrollbarMetrics(void);
MODULE_SCOPE int TkMacOSXUseAntialiasedText(Tcl_Interp *interp, int enable);
MODULE_SCOPE void TkMacOSXInitCarbonEvents(Tcl_Interp *interp);
MODULE_SCOPE int TkMacOSXInitCGDrawing(Tcl_Interp *interp, int enable,
	int antiAlias);
MODULE_SCOPE void TkMacOSXInitKeyboard(Tcl_Interp *interp);
MODULE_SCOPE int TkMacOSXGenerateFocusEvent(Window window, int activeFlag);
MODULE_SCOPE int TkMacOSXGenerateParentMenuSelectEvent(MenuRef menu);
MODULE_SCOPE int TkMacOSXGenerateMenuSelectEvent(MenuRef menu,
	MenuItemIndex index);
MODULE_SCOPE void TkMacOSXClearActiveMenu(MenuRef menu);
MODULE_SCOPE WindowClass TkMacOSXWindowClass(TkWindow *winPtr);
MODULE_SCOPE int TkMacOSXIsWindowZoomed(TkWindow *winPtr);
MODULE_SCOPE int TkGenerateButtonEventForXPointer(Window window);
MODULE_SCOPE EventModifiers TkMacOSXModifierState(void);
MODULE_SCOPE int TkMacOSXSetupDrawingContext(Drawable d, GC gc, int useCG,
    TkMacOSXDrawingContext *dcPtr);
MODULE_SCOPE void TkMacOSXRestoreDrawingContext(TkMacOSXDrawingContext *dcPtr);
MODULE_SCOPE void TkMacOSXSetColorInPort(unsigned long pixel, int fg,
	PixPatHandle penPat, CGrafPtr port);
MODULE_SCOPE void TkMacOSXSetColorInContext(unsigned long pixel,
	CGContextRef context);
MODULE_SCOPE int TkMacOSXRunTclEventLoop(void);
MODULE_SCOPE OSStatus TkMacOSXStartTclEventLoopCarbonTimer(void);
MODULE_SCOPE OSStatus TkMacOSXStopTclEventLoopCarbonTimer(void);
MODULE_SCOPE void TkMacOSXTrackingLoop(int tracking);
MODULE_SCOPE OSStatus TkMacOSXReceiveAndDispatchEvent(void);
MODULE_SCOPE void TkMacOSXInstallWindowCarbonEventHandler(Tcl_Interp *interp,
	WindowRef window);
MODULE_SCOPE int TkMacOSXMakeFullscreen(TkWindow *winPtr, WindowRef window,
	int fullscreen, Tcl_Interp *interp);
MODULE_SCOPE void TkMacOSXEnterExitFullscreen(TkWindow *winPtr, int active);
MODULE_SCOPE void TkMacOSXBringWindowForward(WindowRef wRef);
MODULE_SCOPE WindowRef TkMacOSXDrawableWindow(Drawable drawable);
MODULE_SCOPE void TkMacOSXWinCGBounds(TkWindow *winPtr, CGRect *bounds);
MODULE_SCOPE HIShapeRef TkMacOSXGetClipRgn(Drawable drawable);
MODULE_SCOPE Tcl_Obj* TkMacOSXGetStringObjFromCFString(CFStringRef str);

#endif /* _TKMACPRIV */
