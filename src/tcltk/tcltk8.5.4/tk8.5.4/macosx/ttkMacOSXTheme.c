/*
 * ttkMacOSXTheme.c --
 *
 *	Tk theme engine for Mac OSX, using the Appearance Manager API.
 *
 * Copyright (c) 2004 Joe English
 * Copyright (c) 2005 Neil Madden
 * Copyright (c) 2006-2007 Daniel A. Steffen <das@users.sourceforge.net>
 *
 * See the file "license.terms" for information on usage and redistribution
 * of this file, and for a DISCLAIMER OF ALL WARRANTIES.
 *
 * See also:
 *
 * <URL: http://developer.apple.com/documentation/Carbon/Reference/
 *	Appearance_Manager/appearance_manager/APIIndex.html >
 *
 * Notes:
 *	"Active" means different things in Mac and Tk terminology --
 *	On Aqua, widgets are "Active" if they belong to the foreground window,
 *	"Inactive" if they are in a background window.
 *	Tk uses the term "active" to mean that the mouse cursor
 *	is over a widget; aka "hover", "prelight", or "hot-tracked".
 *	Aqua doesn't use this kind of feedback.
 *
 *	The QuickDraw/Carbon coordinate system is relative to the
 *	top-level window, not to the Tk_Window.  BoxToRect()
 *	accounts for this.
 *
 * RCS: @(#) $Id: ttkMacOSXTheme.c,v 1.21.2.1 2008/05/04 17:16:51 jenglish Exp $
 */

#include "tkMacOSXPrivate.h"
#include "ttk/ttkTheme.h"

#if !defined(BUILD_tile)
/*
 * Use this version in the core:
 */
#define BEGIN_DRAWING(d) { \
	TkMacOSXDrawingContext dc; \
	if (!TkMacOSXSetupDrawingContext((d), NULL, 0, &dc)) {return;}
#define END_DRAWING \
	TkMacOSXRestoreDrawingContext(&dc); }
#else /* BUILD_tile */
/*
 * TkMacOSXSetupDrawingContext is not available to extensions,
 * need to do this the hard way in Tile:
 */
#define BEGIN_DRAWING(d) { \
	CGrafPtr saveWorld; GDHandle saveDevice; \
	GetGWorld(&saveWorld, &saveDevice); \
	SetGWorld(TkMacOSXGetDrawablePort(d), 0); \
	TkMacOSXSetUpClippingRgn(d);
#define END_DRAWING \
	SetGWorld(saveWorld,saveDevice); }
#endif /* defined(BUILD_TILE) */

/*----------------------------------------------------------------------
 * +++ Utilities.
 */

/*
 * BoxToRect --
 *	Convert a Ttk_Box in Tk coordinates relative to the given Drawable
 *	to a native Rect relative to the containing port.
 */
static inline Rect BoxToRect(Drawable d, Ttk_Box b)
{
    MacDrawable *md = (MacDrawable*)d;
    Rect rect;

    rect.top	= b.y + md->yOff;
    rect.left	= b.x + md->xOff;
    rect.bottom	= rect.top + b.height;
    rect.right	= rect.left + b.width;

    return rect;
}

/*
 * PatternOrigin --
 *	Compute brush pattern origin for a Drawable relative to a Tk_Window.
 *
 * Notes: This will only be nonzero if the Drawable is an off-screen pixmap.
 * See also SF bug #1157739.
 */
static Point PatternOrigin(Tk_Window tkwin, Drawable d)
{
    MacDrawable *md = (MacDrawable*)d;
    Rect bounds;
    Point origin;

    TkMacOSXWinBounds((TkWindow *) tkwin, &bounds);
    origin.h = md->xOff - bounds.left;
    origin.v = md->yOff - bounds.top;

    return origin;
}

/*
 * DontErase --
 *	No-op ThemeEraseProc, can be passed to DrawThemeButton &c.
 */
static void DontErase(
    const Rect *bounds, UInt32 eraseData, SInt16 depth, Boolean isColorDev)
{  }

/*
 * Table mapping Tk states to Appearance manager ThemeStates
 */

static Ttk_StateTable ThemeStateTable[] = {
    {kThemeStateUnavailable, TTK_STATE_DISABLED, 0},
    {kThemeStatePressed, TTK_STATE_PRESSED, 0},
    {kThemeStateInactive, TTK_STATE_BACKGROUND, 0},
    {kThemeStateActive, 0, 0}
/* Others: Not sure what these are supposed to mean.
   Up/Down have something to do with "little arrow" increment controls...
   Dunno what a "Rollover" is.
   NEM: Rollover is TTK_STATE_ACTIVE... but we don't handle that yet, by the
   looks of things
    {kThemeStateRollover, 0, 0},
    {kThemeStateUnavailableInactive, 0, 0}
    {kThemeStatePressedUp, 0, 0},
    {kThemeStatePressedDown, 0, 0}
*/
};

/*----------------------------------------------------------------------
 * +++ Button element: Used for elements drawn with DrawThemeButton.
 */

/*
 * Extra margins to account for drop shadow.
 */
static Ttk_Padding ButtonMargins = {2,2,2,2};

#define NoThemeMetric 0xFFFFFFFF

typedef struct {
    ThemeButtonKind kind;
    ThemeMetric heightMetric;
} ThemeButtonParms;

static ThemeButtonParms
    PushButtonParms = { kThemePushButton, kThemeMetricPushButtonHeight },
    CheckBoxParms = { kThemeCheckBox, kThemeMetricCheckBoxHeight },
    RadioButtonParms = { kThemeRadioButton, kThemeMetricRadioButtonHeight },
    BevelButtonParms = { kThemeBevelButton, NoThemeMetric },
    PopupButtonParms = { kThemePopupButton, kThemeMetricPopupButtonHeight },
    DisclosureParms = { kThemeDisclosureButton, kThemeMetricDisclosureTriangleHeight },
    ListHeaderParms = { kThemeListHeaderButton, kThemeMetricListHeaderHeight };

static Ttk_StateTable ButtonValueTable[] = {
    { kThemeButtonMixed, TTK_STATE_ALTERNATE, 0 },
    { kThemeButtonOn, TTK_STATE_SELECTED, 0 },
    { kThemeButtonOff, 0, 0 }
/* Others: kThemeDisclosureRight, kThemeDisclosureDown, kThemeDisclosureLeft */
};

static Ttk_StateTable ButtonAdornmentTable[] = {
    { kThemeAdornmentDefault| kThemeAdornmentFocus,
	TTK_STATE_ALTERNATE| TTK_STATE_FOCUS, 0 },
    { kThemeAdornmentDefault, TTK_STATE_ALTERNATE, 0 },
    { kThemeAdornmentFocus, TTK_STATE_FOCUS, 0 },
    { kThemeAdornmentNone, 0, 0 }
};

/*
 * computeButtonDrawInfo --
 *	Fill in an appearance manager ThemeButtonDrawInfo record.
 */
static ThemeButtonDrawInfo computeButtonDrawInfo(
	ThemeButtonParms *parms, Ttk_State state)
{
    ThemeButtonDrawInfo info;

    info.state = Ttk_StateTableLookup(ThemeStateTable, state);
    info.value = Ttk_StateTableLookup(ButtonValueTable, state);
    info.adornment = Ttk_StateTableLookup(ButtonAdornmentTable, state);
    return info;
}

static void ButtonElementSizeNoPadding(
    void *clientData, void *elementRecord, Tk_Window tkwin,
    int *widthPtr, int *heightPtr, Ttk_Padding *paddingPtr)
{
    ThemeButtonParms *parms = clientData;

    if (parms->heightMetric != NoThemeMetric) {
	SInt32 height;

	ChkErr(GetThemeMetric, parms->heightMetric, &height);
	*heightPtr = height;
    }
}

static void ButtonElementSize(
    void *clientData, void *elementRecord, Tk_Window tkwin,
    int *widthPtr, int *heightPtr, Ttk_Padding *paddingPtr)
{
    ThemeButtonParms *parms = clientData;
    ThemeButtonDrawInfo info = computeButtonDrawInfo(parms, 0);
    static const Rect scratchBounds = {0, 0, 100, 100};
    Rect contentBounds;

    ButtonElementSizeNoPadding(
	clientData, elementRecord, tkwin,
	widthPtr, heightPtr, paddingPtr);

    /*
     * To compute internal padding, query the appearance manager
     * for the content bounds of a dummy rectangle, then use
     * the difference as the padding.
     */
    ChkErr(GetThemeButtonContentBounds,
	&scratchBounds, parms->kind, &info, &contentBounds);

    paddingPtr->left = contentBounds.left;
    paddingPtr->top = contentBounds.top;
    paddingPtr->right = scratchBounds.right - contentBounds.right + 1;
    paddingPtr->bottom = scratchBounds.bottom - contentBounds.bottom;

    /*
     * Now add a little extra padding to account for drop shadows.
     * @@@ SHOULD: call GetThemeButtonBackgroundBounds() instead.
     */

    *paddingPtr = Ttk_AddPadding(*paddingPtr, ButtonMargins);
    *widthPtr += Ttk_PaddingWidth(ButtonMargins);
    *heightPtr += Ttk_PaddingHeight(ButtonMargins);
}

static void ButtonElementDraw(
    void *clientData, void *elementRecord, Tk_Window tkwin,
    Drawable d, Ttk_Box b, Ttk_State state)
{
    ThemeButtonParms *parms = clientData;
    ThemeButtonDrawInfo info = computeButtonDrawInfo(parms, state);
    Rect bounds = BoxToRect(d, Ttk_PadBox(b, ButtonMargins));

    BEGIN_DRAWING(d)
    ChkErr(DrawThemeButton, &bounds, parms->kind, &info, NULL, NULL, NULL, 0);
    END_DRAWING
}

static Ttk_ElementSpec ButtonElementSpec = {
    TK_STYLE_VERSION_2,
    sizeof(NullElement),
    TtkNullElementOptions,
    ButtonElementSize,
    ButtonElementDraw
};

/*----------------------------------------------------------------------
 * +++ Notebook elements.
 */

static Ttk_StateTable TabStyleTable[] = {
    { kThemeTabFrontInactive, TTK_STATE_SELECTED|TTK_STATE_BACKGROUND, 0 },
    { kThemeTabNonFrontInactive, TTK_STATE_BACKGROUND, 0 },
    { kThemeTabFrontUnavailable, TTK_STATE_DISABLED|TTK_STATE_SELECTED, 0 },
    { kThemeTabNonFrontUnavailable, TTK_STATE_DISABLED, 0 },
    { kThemeTabFront, TTK_STATE_SELECTED, 0 },
    { kThemeTabNonFrontPressed, TTK_STATE_PRESSED, 0 },
    { kThemeTabNonFront, 0,0 }
};

/*
 * Quoth DrawThemeTab() reference manual:
 * "Small tabs have a height of 16 pixels large tabs have a height of
 * 21 pixels. (The widths of tabs are variable.) Additionally, the
 * distance that the tab overlaps the pane must be included in the tab
 * rectangle this overlap distance is always 3 pixels, although the
 * 3-pixel overlap is only drawn for the front tab."
 */
static const int TAB_HEIGHT = 21;
static const int TAB_OVERLAP = 3;

static void TabElementSize(
    void *clientData, void *elementRecord, Tk_Window tkwin,
    int *widthPtr, int *heightPtr, Ttk_Padding *paddingPtr)
{
    *heightPtr = TAB_HEIGHT + TAB_OVERLAP - 1;
}

static void TabElementDraw(
    void *clientData, void *elementRecord, Tk_Window tkwin,
    Drawable d, Ttk_Box b, Ttk_State state)
{
    Rect bounds = BoxToRect(d, b);
    ThemeTabStyle tabStyle = Ttk_StateTableLookup(TabStyleTable, state);

    bounds.bottom += TAB_OVERLAP;
    BEGIN_DRAWING(d)
    ChkErr(DrawThemeTab, &bounds, tabStyle, kThemeTabNorth, 0, 0);
    END_DRAWING
}

static Ttk_ElementSpec TabElementSpec = {
    TK_STYLE_VERSION_2,
    sizeof(NullElement),
    TtkNullElementOptions,
    TabElementSize,
    TabElementDraw
};

/*
 * Notebook panes:
 */
static void PaneElementSize(
    void *clientData, void *elementRecord, Tk_Window tkwin,
    int *widthPtr, int *heightPtr, Ttk_Padding *paddingPtr)
{
    /* Padding determined by trial-and-error */
    *paddingPtr = Ttk_MakePadding(2, 8, 2, 2);
}

static void PaneElementDraw(
    void *clientData, void *elementRecord, Tk_Window tkwin,
    Drawable d, Ttk_Box b, Ttk_State state)
{
    Rect bounds = BoxToRect(d, b);
    ThemeDrawState drawState = Ttk_StateTableLookup(ThemeStateTable, state);

    BEGIN_DRAWING(d)
    ChkErr(DrawThemeTabPane, &bounds, drawState);
    END_DRAWING
}

static Ttk_ElementSpec PaneElementSpec = {
    TK_STYLE_VERSION_2,
    sizeof(NullElement),
    TtkNullElementOptions,
    PaneElementSize,
    PaneElementDraw
};

/*
 * Labelframe borders:
 * Use "primary group box ..."
 * Quoth DrawThemePrimaryGroup reference:
 * "The primary group box frame is drawn inside the specified
 * rectangle and is a maximum of 2 pixels thick."
 *
 * "Maximum of 2 pixels thick" is apparently a lie;
 * looks more like 4 to me with shading.
 */
static void GroupElementSize(
    void *clientData, void *elementRecord, Tk_Window tkwin,
    int *widthPtr, int *heightPtr, Ttk_Padding *paddingPtr)
{
    *paddingPtr = Ttk_UniformPadding(4);
}

static void GroupElementDraw(
    void *clientData, void *elementRecord, Tk_Window tkwin,
    Drawable d, Ttk_Box b, Ttk_State state)
{
    Rect bounds = BoxToRect(d, b);
    ThemeDrawState drawState = Ttk_StateTableLookup(ThemeStateTable, state);

    BEGIN_DRAWING(d)
    ChkErr(DrawThemePrimaryGroup, &bounds, drawState);
    END_DRAWING
}

static Ttk_ElementSpec GroupElementSpec = {
    TK_STYLE_VERSION_2,
    sizeof(NullElement),
    TtkNullElementOptions,
    GroupElementSize,
    GroupElementDraw
};

/*----------------------------------------------------------------------
 * +++ Entry element --
 *	3 pixels padding for focus rectangle
 *	2 pixels padding for EditTextFrame
 */

typedef struct {
    Tcl_Obj	*backgroundObj;
} EntryElement;

static Ttk_ElementOptionSpec EntryElementOptions[] = {
    { "-background", TK_OPTION_BORDER,
	    Tk_Offset(EntryElement,backgroundObj), "white" },
    {0}
};

static void EntryElementSize(
    void *clientData, void *elementRecord, Tk_Window tkwin,
    int *widthPtr, int *heightPtr, Ttk_Padding *paddingPtr)
{
    *paddingPtr = Ttk_UniformPadding(5);
}

static void EntryElementDraw(
    void *clientData, void *elementRecord, Tk_Window tkwin,
    Drawable d, Ttk_Box b, Ttk_State state)
{
    EntryElement *e = elementRecord;
    Tk_3DBorder backgroundPtr = Tk_Get3DBorderFromObj(tkwin,e->backgroundObj);
    Ttk_Box inner = Ttk_PadBox(b, Ttk_UniformPadding(3));
    Rect bounds = BoxToRect(d, inner);
    ThemeDrawState drawState = Ttk_StateTableLookup(ThemeStateTable, state);

    /*
     * Erase w/background color:
     */
    XFillRectangle(Tk_Display(tkwin), d,
	    Tk_3DBorderGC(tkwin, backgroundPtr, TK_3D_FLAT_GC),
	    inner.x,inner.y, inner.width, inner.height);

    BEGIN_DRAWING(d)
    ChkErr(DrawThemeEditTextFrame, &bounds, drawState);
    if (state & TTK_STATE_FOCUS) {
	ChkErr(DrawThemeFocusRect, &bounds, 1);
    }
    END_DRAWING
}

static Ttk_ElementSpec EntryElementSpec = {
    TK_STYLE_VERSION_2,
    sizeof(EntryElement),
    EntryElementOptions,
    EntryElementSize,
    EntryElementDraw
};

/*----------------------------------------------------------------------
 * +++ Combobox:
 *
 * NOTES:
 *	kThemeMetricComboBoxLargeDisclosureWidth -> 17
 *	Padding and margins guesstimated by trial-and-error.
 */

static Ttk_Padding ComboboxPadding = { 2, 3, 17, 1 };
static Ttk_Padding ComboboxMargins = { 3, 3, 4, 4 };

static void ComboboxElementSize(
    void *clientData, void *elementRecord, Tk_Window tkwin,
    int *widthPtr, int *heightPtr, Ttk_Padding *paddingPtr)
{
    *widthPtr = 0;
    *heightPtr = 0;
    *paddingPtr = Ttk_AddPadding(ComboboxMargins, ComboboxPadding);
}

static void ComboboxElementDraw(
    void *clientData, void *elementRecord, Tk_Window tkwin,
    Drawable d, Ttk_Box b, Ttk_State state)
{
    ThemeButtonParms *parms = clientData;
    ThemeButtonDrawInfo info = computeButtonDrawInfo(parms, state);
    Rect bounds = BoxToRect(d, Ttk_PadBox(b, ComboboxMargins));

    BEGIN_DRAWING(d)
    ChkErr(DrawThemeButton,
	&bounds, kThemeComboBox, &info, NULL, NULL, NULL, 0);
    END_DRAWING
}

static Ttk_ElementSpec ComboboxElementSpec = {
    TK_STYLE_VERSION_2,
    sizeof(NullElement),
    TtkNullElementOptions,
    ComboboxElementSize,
    ComboboxElementDraw
};

/*----------------------------------------------------------------------
 * +++ DrawThemeTrack-based elements --
 * Progress bars and scales. (See also: <<NOTE-TRACKS>>)
 */

static Ttk_StateTable ThemeTrackEnableTable[] = {
    { kThemeTrackDisabled, TTK_STATE_DISABLED, 0 },
    { kThemeTrackInactive, TTK_STATE_BACKGROUND, 0 },
    { kThemeTrackActive, 0, 0 }
    /* { kThemeTrackNothingToScroll, ?, ? }, */
};

typedef struct {	/* TrackElement client data */
    ThemeTrackKind	kind;
    SInt32		thicknessMetric;
} TrackElementData;

static TrackElementData ScaleData = {
    kThemeSlider, kThemeMetricHSliderHeight
};

typedef struct {
    Tcl_Obj *fromObj;		/* minimum value */
    Tcl_Obj *toObj;		/* maximum value */
    Tcl_Obj *valueObj;		/* current value */
    Tcl_Obj *orientObj;		/* horizontal / vertical */
} TrackElement;

static Ttk_ElementOptionSpec TrackElementOptions[] = {
    { "-from", TK_OPTION_DOUBLE, Tk_Offset(TrackElement,fromObj) },
    { "-to", TK_OPTION_DOUBLE, Tk_Offset(TrackElement,toObj) },
    { "-value", TK_OPTION_DOUBLE, Tk_Offset(TrackElement,valueObj) },
    { "-orient", TK_OPTION_STRING, Tk_Offset(TrackElement,orientObj) },
    {0,0,0}
};

static void TrackElementSize(
    void *clientData, void *elementRecord, Tk_Window tkwin,
    int *widthPtr, int *heightPtr, Ttk_Padding *paddingPtr)
{
    TrackElementData *data = clientData;
    SInt32 size = 24;	/* reasonable default ... */

    ChkErr(GetThemeMetric, data->thicknessMetric, &size);
    *widthPtr = *heightPtr = size;
}

static void TrackElementDraw(
    void *clientData, void *elementRecord, Tk_Window tkwin,
    Drawable d, Ttk_Box b, Ttk_State state)
{
    TrackElementData *data = clientData;
    TrackElement *elem = elementRecord;
    double from = 0, to = 100, value = 0;
    int orientation = TTK_ORIENT_HORIZONTAL;
    ThemeTrackDrawInfo info;

    Tcl_GetDoubleFromObj(NULL, elem->fromObj, &from);
    Tcl_GetDoubleFromObj(NULL, elem->toObj, &to);
    Tcl_GetDoubleFromObj(NULL, elem->valueObj, &value);
    Ttk_GetOrientFromObj(NULL, elem->orientObj, &orientation);

    /* @@@ BUG: min, max, and value should account for resolution:
     * @@@ if finer than 1.0, conversion to int breaks.
     */
    info.kind = data->kind;
    info.bounds = BoxToRect(d, b);
    info.min = (int) from;		/* @@@ */
    info.max = (int) to;		/* @@@ */
    info.value = (int) value;		/* @@@ */

    info.attributes = orientation == TTK_ORIENT_HORIZONTAL
	    ? kThemeTrackHorizontal : 0;
    info.attributes |= kThemeTrackShowThumb;
    info.enableState = Ttk_StateTableLookup(ThemeTrackEnableTable, state);

    switch (data->kind) {
	case kThemeProgressBar:
	    info.trackInfo.progress.phase = 0; /* 1-4: animation phase */
	    break;
	case kThemeSlider:
	    info.trackInfo.slider.pressState = 0; /* @@@ fill this in */
	    info.trackInfo.slider.thumbDir =  kThemeThumbPlain;
		/* kThemeThumbUpward, kThemeThumbDownward, kThemeThumbPlain  */
	    break;
    }

    BEGIN_DRAWING(d)
    ChkErr(DrawThemeTrack, &info, NULL, NULL, 0);
    END_DRAWING
}

static Ttk_ElementSpec TrackElementSpec = {
    TK_STYLE_VERSION_2,
    sizeof(TrackElement),
    TrackElementOptions,
    TrackElementSize,
    TrackElementDraw
};

/*
 * Slider element -- <<NOTE-TRACKS>>
 * Has geometry only. The Scale widget adjusts the position of this element,
 * and uses it for hit detection. In the Aqua theme, the slider is actually
 * drawn as part of the trough element.
 *
 * Also buggy: The geometry here is a Wild-Assed-Guess; I can't
 * figure out how to get the Appearance Manager to tell me the
 * slider size.
 */
static void SliderElementSize(
    void *clientData, void *elementRecord, Tk_Window tkwin,
    int *widthPtr, int *heightPtr, Ttk_Padding *paddingPtr)
{
    *widthPtr = *heightPtr = 24;
}

static Ttk_ElementSpec SliderElementSpec = {
    TK_STYLE_VERSION_2,
    sizeof(NullElement),
    TtkNullElementOptions,
    SliderElementSize,
    TtkNullElementDraw
};

/*----------------------------------------------------------------------
 * +++ Progress bar element (new):
 *
 * @@@ NOTE: According to an older revision of the Aqua reference docs,
 * @@@ the 'phase' field is between 0 and 4. Newer revisions say
 * @@@ that it can be any UInt8 value.
 */

typedef struct {
    Tcl_Obj *orientObj;		/* horizontal / vertical */
    Tcl_Obj *valueObj;		/* current value */
    Tcl_Obj *maximumObj;	/* maximum value */
    Tcl_Obj *phaseObj;		/* animation phase */
    Tcl_Obj *modeObj;		/* progress bar mode */
} PbarElement;

static Ttk_ElementOptionSpec PbarElementOptions[] = {
    { "-orient", TK_OPTION_STRING,
	Tk_Offset(PbarElement,orientObj), "horizontal" },
    { "-value", TK_OPTION_DOUBLE,
	Tk_Offset(PbarElement,valueObj), "0" },
    { "-maximum", TK_OPTION_DOUBLE,
	Tk_Offset(PbarElement,maximumObj), "100" },
    { "-phase", TK_OPTION_INT,
	Tk_Offset(PbarElement,phaseObj), "0" },
    { "-mode", TK_OPTION_STRING,
	Tk_Offset(PbarElement,modeObj), "determinate" },
    {0,0,0,0}
};

static void PbarElementSize(
    void *clientData, void *elementRecord, Tk_Window tkwin,
    int *widthPtr, int *heightPtr, Ttk_Padding *paddingPtr)
{
    SInt32 size = 24;	/* @@@ Check HIG for correct default */

    ChkErr(GetThemeMetric, kThemeMetricLargeProgressBarThickness, &size);
    *widthPtr = *heightPtr = size;
}

static void PbarElementDraw(
    void *clientData, void *elementRecord, Tk_Window tkwin,
    Drawable d, Ttk_Box b, Ttk_State state)
{
    PbarElement *pbar = elementRecord;
    int orientation = TTK_ORIENT_HORIZONTAL;
    double value = 0, maximum = 100;
    int phase = 0;
    ThemeTrackDrawInfo info;

    Ttk_GetOrientFromObj(NULL, pbar->orientObj, &orientation);
    Tcl_GetDoubleFromObj(NULL, pbar->valueObj, &value);
    Tcl_GetDoubleFromObj(NULL, pbar->maximumObj, &maximum);
    Tcl_GetIntFromObj(NULL, pbar->phaseObj, &phase);

    if (!strcmp("indeterminate", Tcl_GetString(pbar->modeObj)) && value) {
	info.kind = kThemeIndeterminateBar;
    } else {
	info.kind = kThemeProgressBar;
    }
    info.bounds = BoxToRect(d, b);
    info.min = 0;
    info.max = (int) maximum;	/* @@@ See note above */
    info.value = (int) value;
    info.attributes = orientation == TTK_ORIENT_HORIZONTAL
	    ? kThemeTrackHorizontal : 0;
    info.attributes |= kThemeTrackShowThumb;
    info.enableState = Ttk_StateTableLookup(ThemeTrackEnableTable, state);
    info.trackInfo.progress.phase = phase;

    BEGIN_DRAWING(d)
    ChkErr(DrawThemeTrack, &info, NULL, NULL, 0);
    END_DRAWING
}

static Ttk_ElementSpec PbarElementSpec = {
    TK_STYLE_VERSION_2,
    sizeof(PbarElement),
    PbarElementOptions,
    PbarElementSize,
    PbarElementDraw
};

/*----------------------------------------------------------------------
 * +++ Separator element.
 *
 * DrawThemeSeparator() guesses the orientation of the line from
 * the width and height of the rectangle, so the same element can
 * can be used for horizontal, vertical, and general separators.
 */

static void SeparatorElementSize(
    void *clientData, void *elementRecord, Tk_Window tkwin,
    int *widthPtr, int *heightPtr, Ttk_Padding *paddingPtr)
{
    *widthPtr = *heightPtr = 1;
}

static void SeparatorElementDraw(
    void *clientData, void *elementRecord, Tk_Window tkwin,
    Drawable d, Ttk_Box b, unsigned int state)
{
    Rect bounds = BoxToRect(d, b);
    ThemeDrawState drawState = Ttk_StateTableLookup(ThemeStateTable, state);

    /*
     * DrawThemeSeparator only supports kThemeStateActive / kThemeStateInactive
    */
    state &= TTK_STATE_BACKGROUND;
    BEGIN_DRAWING(d)
    ChkErr(DrawThemeSeparator, &bounds, drawState);
    END_DRAWING
}

static Ttk_ElementSpec SeparatorElementSpec = {
    TK_STYLE_VERSION_2,
    sizeof(NullElement),
    TtkNullElementOptions,
    SeparatorElementSize,
    SeparatorElementDraw
};

/*----------------------------------------------------------------------
 * +++ Size grip element.
 */
static const ThemeGrowDirection sizegripGrowDirection
	= kThemeGrowRight|kThemeGrowDown;

static void SizegripElementSize(
    void *clientData, void *elementRecord, Tk_Window tkwin,
    int *widthPtr, int *heightPtr, Ttk_Padding *paddingPtr)
{
    Point origin = {0, 0};
    Rect bounds;

    ChkErr(GetThemeStandaloneGrowBoxBounds,
	origin, sizegripGrowDirection, false, &bounds);
    *widthPtr = bounds.right - bounds.left;
    *heightPtr = bounds.bottom - bounds.top;
}

static void SizegripElementDraw(
    void *clientData, void *elementRecord, Tk_Window tkwin,
    Drawable d, Ttk_Box b, unsigned int state)
{
    Rect bounds = BoxToRect(d, b);
    Point origin = {bounds.top, bounds.left};

    /* Grow box only supports kThemeStateActive, kThemeStateInactive */
    state &= TTK_STATE_BACKGROUND;

    BEGIN_DRAWING(d)
    ChkErr(DrawThemeStandaloneGrowBox,
	origin, sizegripGrowDirection, false,
	Ttk_StateTableLookup(ThemeStateTable, state));
    END_DRAWING
}

static Ttk_ElementSpec SizegripElementSpec = {
    TK_STYLE_VERSION_2,
    sizeof(NullElement),
    TtkNullElementOptions,
    SizegripElementSize,
    SizegripElementDraw
};

/*----------------------------------------------------------------------
 * +++ Background and fill elements.
 *
 *	This isn't quite right: In Aqua, the correct background for
 *	a control depends on what kind of container it belongs to,
 *	and the type of the top-level window.
 *
 *	Also: patterned backgrounds should be aligned with the coordinate
 *	system of the top-level window.  If we're drawing into an
 *	off-screen graphics port this leads to alignment glitches.
 */

static void FillElementDraw(
    void *clientData, void *elementRecord, Tk_Window tkwin,
    Drawable d, Ttk_Box b, Ttk_State state)
{
    Rect bounds = BoxToRect(d, b);
    ThemeBrush brush = (state & TTK_STATE_BACKGROUND)
	    ? kThemeBrushModelessDialogBackgroundInactive
	    : kThemeBrushModelessDialogBackgroundActive;

    BEGIN_DRAWING(d)
    ChkErr(SetThemeBackground, brush, 32, true);
    QDSetPatternOrigin(PatternOrigin(tkwin, d));
    EraseRect(&bounds);
    END_DRAWING
}

static void BackgroundElementDraw(
    void *clientData, void *elementRecord, Tk_Window tkwin,
    Drawable d, Ttk_Box b, unsigned int state)
{
    FillElementDraw(
	clientData, elementRecord, tkwin,
	d, Ttk_WinBox(tkwin), state);
}

static Ttk_ElementSpec FillElementSpec = {
    TK_STYLE_VERSION_2,
    sizeof(NullElement),
    TtkNullElementOptions,
    TtkNullElementSize,
    FillElementDraw
};

static Ttk_ElementSpec BackgroundElementSpec = {
    TK_STYLE_VERSION_2,
    sizeof(NullElement),
    TtkNullElementOptions,
    TtkNullElementSize,
    BackgroundElementDraw
};

/*----------------------------------------------------------------------
 * +++ ToolbarBackground element -- toolbar style for frames.
 *
 *	This is very similar to the normal background element, but uses a
 *	different ThemeBrush in order to get the lighter pinstripe effect
 *	used in toolbars. We use SetThemeBackground() rather than
 *	ApplyThemeBackground() in order to get the right style.
 *
 * <URL: http://developer.apple.com/documentation/Carbon/Reference/
 *	Appearance_Manager/appearance_manager/constant_7.html#/
 *	/apple_ref/doc/uid/TP30000243/C005321>
 *
 */
static void ToolbarBackgroundElementDraw(
    void *clientData, void *elementRecord, Tk_Window tkwin,
    Drawable d, Ttk_Box b, Ttk_State state)
{
    ThemeBrush brush = kThemeBrushToolbarBackground;
    Rect bounds = BoxToRect(d, Ttk_WinBox(tkwin));

    BEGIN_DRAWING(d)
    ChkErr(SetThemeBackground, brush, 32, true);
    QDSetPatternOrigin(PatternOrigin(tkwin, d));
    EraseRect(&bounds);
    END_DRAWING
}

static Ttk_ElementSpec ToolbarBackgroundElementSpec = {
    TK_STYLE_VERSION_2,
    sizeof(NullElement),
    TtkNullElementOptions,
    TtkNullElementSize,
    ToolbarBackgroundElementDraw
};

/*----------------------------------------------------------------------
 * +++ Treeview header
 *	Redefine the header to use a kThemeListHeaderButton.
 */

static Ttk_StateTable TreeHeaderAdornmentTable[] = {
    { kThemeAdornmentHeaderButtonSortUp, TTK_STATE_ALTERNATE, 0 },
    { kThemeAdornmentFocus, TTK_STATE_FOCUS, 0 },
    { kThemeAdornmentNone, 0, 0 }
};

static void TreeHeaderElementDraw(
    void *clientData, void *elementRecord, Tk_Window tkwin,
    Drawable d, Ttk_Box b, Ttk_State state)
{
    ThemeButtonParms *parms = clientData;
    Rect bounds = BoxToRect(d, b);
    ThemeButtonDrawInfo info;

    info.state = Ttk_StateTableLookup(ThemeStateTable, state);
    info.value = Ttk_StateTableLookup(ButtonValueTable, state);
    info.adornment = Ttk_StateTableLookup(TreeHeaderAdornmentTable, state);

    BEGIN_DRAWING(d)
    ChkErr(DrawThemeButton, &bounds, parms->kind, &info, NULL, NULL, NULL, 0);
    END_DRAWING
}

static Ttk_ElementSpec TreeHeaderElementSpec = {
    TK_STYLE_VERSION_2,
    sizeof(NullElement),
    TtkNullElementOptions,
    ButtonElementSizeNoPadding,
    TreeHeaderElementDraw
};

/*
 * Disclosure triangle:
 */
#define TTK_TREEVIEW_STATE_OPEN TTK_STATE_USER1
#define TTK_TREEVIEW_STATE_LEAF TTK_STATE_USER2
static Ttk_StateTable DisclosureValueTable[] = {
    { kThemeDisclosureDown, TTK_TREEVIEW_STATE_OPEN, 0 },
    { kThemeDisclosureRight, 0, 0 },
};

static void DisclosureElementSize(
    void *clientData, void *elementRecord, Tk_Window tkwin,
    int *widthPtr, int *heightPtr, Ttk_Padding *paddingPtr)
{
    SInt32 s;
    GetThemeMetric(kThemeMetricDisclosureTriangleWidth, &s); *widthPtr = s;
    GetThemeMetric(kThemeMetricDisclosureTriangleHeight, &s); *heightPtr = s;
}

static void DisclosureElementDraw(
    void *clientData, void *elementRecord, Tk_Window tkwin,
    Drawable d, Ttk_Box b, Ttk_State state)
{
    Rect bounds = BoxToRect(d, b);
    ThemeButtonDrawInfo info;

    if (state & TTK_TREEVIEW_STATE_LEAF) {
	return;
    }

    info.state = Ttk_StateTableLookup(ThemeStateTable, state);
    info.value = Ttk_StateTableLookup(DisclosureValueTable, state);
    info.adornment = kThemeAdornmentDrawIndicatorOnly;

    BEGIN_DRAWING(d)
    ChkErr(DrawThemeButton,
	&bounds, kThemeDisclosureTriangle, &info, NULL, DontErase, NULL, 0);
    END_DRAWING
}

static Ttk_ElementSpec DisclosureElementSpec = {
    TK_STYLE_VERSION_2,
    sizeof(NullElement),
    TtkNullElementOptions,
    DisclosureElementSize,
    DisclosureElementDraw
};

/*----------------------------------------------------------------------
 * +++ Widget layouts.
 */

TTK_BEGIN_LAYOUT_TABLE(LayoutTable)

TTK_LAYOUT("Toolbar",
    TTK_NODE("Toolbar.background", TTK_FILL_BOTH))

TTK_LAYOUT("TButton",
    TTK_GROUP("Button.button", TTK_FILL_BOTH,
	TTK_GROUP("Button.padding", TTK_FILL_BOTH,
	    TTK_NODE("Button.label", TTK_FILL_BOTH))))

TTK_LAYOUT("TRadiobutton",
    TTK_GROUP("Radiobutton.button", TTK_FILL_BOTH,
	TTK_GROUP("Radiobutton.padding", TTK_FILL_BOTH,
	    TTK_NODE("Radiobutton.label", TTK_PACK_LEFT))))

TTK_LAYOUT("TCheckbutton",
    TTK_GROUP("Checkbutton.button", TTK_FILL_BOTH,
	TTK_GROUP("Checkbutton.padding", TTK_FILL_BOTH,
	    TTK_NODE("Checkbutton.label", TTK_PACK_LEFT))))

TTK_LAYOUT("TMenubutton",
    TTK_GROUP("Menubutton.button", TTK_FILL_BOTH,
	TTK_GROUP("Menubutton.padding", TTK_FILL_BOTH,
	    TTK_NODE("Menubutton.label", TTK_PACK_LEFT))))

TTK_LAYOUT("TCombobox",
    TTK_GROUP("Combobox.button", TTK_PACK_TOP|TTK_FILL_X,
	TTK_GROUP("Combobox.padding", TTK_FILL_BOTH,
	    TTK_NODE("Combobox.textarea", TTK_FILL_X))))

/* Notebook tabs -- no focus ring */
TTK_LAYOUT("Tab",
    TTK_GROUP("Notebook.tab", TTK_FILL_BOTH,
	TTK_GROUP("Notebook.padding", TTK_EXPAND|TTK_FILL_BOTH,
	    TTK_NODE("Notebook.label", TTK_EXPAND|TTK_FILL_BOTH))))

/* Progress bars -- track only */
TTK_LAYOUT("TProgressbar",
    TTK_NODE("Progressbar.track", TTK_EXPAND|TTK_FILL_BOTH))

/* Tree heading -- no border, fixed height */
TTK_LAYOUT("Heading",
    TTK_NODE("Treeheading.cell", TTK_FILL_X)
    TTK_NODE("Treeheading.image", TTK_PACK_RIGHT)
    TTK_NODE("Treeheading.text", 0))

/* Tree items -- omit focus ring */ 
TTK_LAYOUT("Item",
    TTK_GROUP("Treeitem.padding", TTK_FILL_BOTH,
	TTK_NODE("Treeitem.indicator", TTK_PACK_LEFT)
	TTK_NODE("Treeitem.image", TTK_PACK_LEFT)
	TTK_NODE("Treeitem.text", TTK_PACK_LEFT)))

TTK_END_LAYOUT_TABLE

/*----------------------------------------------------------------------
 * +++ Initialization.
 */

static int AquaTheme_Init(Tcl_Interp *interp)
{
    Ttk_Theme themePtr = Ttk_CreateTheme(interp, "aqua", NULL);

    if (!themePtr) {
	return TCL_ERROR;
    }

    /*
     * Elements:
     */
    Ttk_RegisterElementSpec(themePtr, "background", &BackgroundElementSpec, 0);
    Ttk_RegisterElementSpec(themePtr, "fill", &FillElementSpec, 0);
    Ttk_RegisterElementSpec(themePtr, "Toolbar.background",
	&ToolbarBackgroundElementSpec, 0);

    Ttk_RegisterElementSpec(themePtr, "Button.button",
	&ButtonElementSpec, &PushButtonParms);
    Ttk_RegisterElementSpec(themePtr, "Checkbutton.button",
	&ButtonElementSpec, &CheckBoxParms);
    Ttk_RegisterElementSpec(themePtr, "Radiobutton.button",
	&ButtonElementSpec, &RadioButtonParms);
    Ttk_RegisterElementSpec(themePtr, "Toolbutton.border",
	&ButtonElementSpec, &BevelButtonParms);
    Ttk_RegisterElementSpec(themePtr, "Menubutton.button",
	&ButtonElementSpec, &PopupButtonParms);
    Ttk_RegisterElementSpec(themePtr, "Combobox.button",
	&ComboboxElementSpec, 0);
    Ttk_RegisterElementSpec(themePtr, "Treeitem.indicator",
	&DisclosureElementSpec, &DisclosureParms);
    Ttk_RegisterElementSpec(themePtr, "Treeheading.cell",
	&TreeHeaderElementSpec, &ListHeaderParms);

    Ttk_RegisterElementSpec(themePtr, "Notebook.tab", &TabElementSpec, 0);
    Ttk_RegisterElementSpec(themePtr, "Notebook.client", &PaneElementSpec, 0);

    Ttk_RegisterElementSpec(themePtr, "Labelframe.border",&GroupElementSpec,0);
    Ttk_RegisterElementSpec(themePtr, "Entry.field",&EntryElementSpec,0);

    Ttk_RegisterElementSpec(themePtr, "separator",&SeparatorElementSpec,0);
    Ttk_RegisterElementSpec(themePtr, "hseparator",&SeparatorElementSpec,0);
    Ttk_RegisterElementSpec(themePtr, "vseparator",&SeparatorElementSpec,0);

    Ttk_RegisterElementSpec(themePtr, "sizegrip",&SizegripElementSpec,0);

    /*
     * <<NOTE-TRACKS>>
     * The Progressbar widget adjusts the size of the pbar element.
     * In the Aqua theme, the appearance manager computes the bar geometry;
     * we do all the drawing in the ".track" element and leave the .pbar out.
     */
    Ttk_RegisterElementSpec(themePtr,"Scale.trough",
	&TrackElementSpec, &ScaleData);
    Ttk_RegisterElementSpec(themePtr,"Scale.slider",&SliderElementSpec,0);
    Ttk_RegisterElementSpec(themePtr,"Progressbar.track", &PbarElementSpec, 0);

    /*
     * Layouts:
     */
    Ttk_RegisterLayouts(themePtr, LayoutTable);

    Tcl_PkgProvide(interp, "ttk::theme::aqua", TTK_VERSION);
    return TCL_OK;
}

MODULE_SCOPE
int Ttk_MacOSXPlatformInit(Tcl_Interp *interp)
{
    return AquaTheme_Init(interp);
}

