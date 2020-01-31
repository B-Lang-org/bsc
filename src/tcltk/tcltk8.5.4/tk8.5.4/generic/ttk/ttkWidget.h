/* $Id: ttkWidget.h,v 1.9 2008/01/06 22:33:14 jenglish Exp $
 * Copyright (c) 2003, Joe English
 * Helper routines for widget implementations.
 */

#ifndef _TTKWIDGET
#define _TTKWIDGET

/*
 * State flags for 'flags' field.
 */
#define WIDGET_DESTROYED	0x0001
#define REDISPLAY_PENDING 	0x0002	/* scheduled call to RedisplayWidget */
#define CURSOR_ON 		0x0020	/* See TtkBlinkCursor() */
#define WIDGET_USER_FLAG        0x0100  /* 0x0100 - 0x8000 for user flags */

/*
 * Bit fields for OptionSpec 'mask' field:
 */
#define READONLY_OPTION 	0x1
#define STYLE_CHANGED   	0x2
#define GEOMETRY_CHANGED	0x4

/*
 * Core widget elements
 */
typedef struct WidgetSpec_ WidgetSpec;	/* Forward */

typedef struct
{
    Tk_Window tkwin;		/* Window associated with widget */
    Tcl_Interp *interp;		/* Interpreter associated with widget. */
    WidgetSpec *widgetSpec;	/* Widget class hooks */
    Tcl_Command widgetCmd;	/* Token for widget command. */
    Tk_OptionTable optionTable;	/* Option table */
    Ttk_Layout layout;  	/* Widget layout */

    /*
     * Storage for resources:
     */
    Tcl_Obj *takeFocusPtr;	/* Storage for -takefocus option */
    Tcl_Obj *cursorObj;		/* Storage for -cursor option */
    Tcl_Obj *styleObj;		/* Name of currently-applied style */
    Tcl_Obj *classObj;		/* Class name (readonly option) */

    Ttk_State state;		/* Current widget state */
    unsigned int flags;		/* internal flags, see above */

} WidgetCore;

/*
 * Subcommand specifications:
 */
typedef int (*WidgetSubcommandProc)(
    Tcl_Interp *interp, int objc, Tcl_Obj *const objv[], void *recordPtr);
typedef struct {
    const char *name;
    WidgetSubcommandProc command;
} WidgetCommandSpec;

MODULE_SCOPE int TtkWidgetEnsembleCommand(	/* Run an ensemble command */
    const WidgetCommandSpec *commands, int cmdIndex,
    Tcl_Interp *interp, int objc, Tcl_Obj *const objv[], void *recordPtr);

/*
 * Widget specifications:
 */
struct WidgetSpec_
{
    const char 		*className;	/* Widget class name */
    size_t 		recordSize;	/* #bytes in widget record */
    const Tk_OptionSpec	*optionSpecs;	/* Option specifications */
    const WidgetCommandSpec *commands;	/* Widget instance subcommands */

    /*
     * Hooks:
     */
    int  	(*initializeProc)(Tcl_Interp *, void *recordPtr);
    void	(*cleanupProc)(void *recordPtr);
    int 	(*configureProc)(Tcl_Interp *, void *recordPtr, int flags);
    int 	(*postConfigureProc)(Tcl_Interp *, void *recordPtr, int flags);
    Ttk_Layout	(*getLayoutProc)(Tcl_Interp *,Ttk_Theme, void *recordPtr);
    int 	(*sizeProc)(void *recordPtr, int *widthPtr, int *heightPtr);
    void	(*layoutProc)(void *recordPtr);
    void	(*displayProc)(void *recordPtr, Drawable d);
};

/*
 * Common factors for widget implementations:
 */
MODULE_SCOPE int  TtkNullInitialize(Tcl_Interp *, void *);
MODULE_SCOPE int  TtkNullPostConfigure(Tcl_Interp *, void *, int);
MODULE_SCOPE void TtkNullCleanup(void *recordPtr);
MODULE_SCOPE Ttk_Layout TtkWidgetGetLayout(
	Tcl_Interp *, Ttk_Theme, void *recordPtr);
MODULE_SCOPE Ttk_Layout TtkWidgetGetOrientedLayout(
	Tcl_Interp *, Ttk_Theme, void *recordPtr, Tcl_Obj *orientObj);
MODULE_SCOPE int  TtkWidgetSize(void *recordPtr, int *w, int *h);
MODULE_SCOPE void TtkWidgetDoLayout(void *recordPtr);
MODULE_SCOPE void TtkWidgetDisplay(void *recordPtr, Drawable);

MODULE_SCOPE int TtkCoreConfigure(Tcl_Interp*, void *, int mask);

/* Common widget commands:
 */
MODULE_SCOPE int TtkWidgetConfigureCommand(
	Tcl_Interp *, int, Tcl_Obj*const[], void *);
MODULE_SCOPE int TtkWidgetCgetCommand(
	Tcl_Interp *, int, Tcl_Obj*const[], void *);
MODULE_SCOPE int TtkWidgetInstateCommand(
	Tcl_Interp *, int, Tcl_Obj*const[], void *);
MODULE_SCOPE int TtkWidgetStateCommand(
	Tcl_Interp *, int, Tcl_Obj*const[], void *);
MODULE_SCOPE int TtkWidgetIdentifyCommand(
	Tcl_Interp *, int, Tcl_Obj*const[], void *);

/* Widget constructor:
 */
MODULE_SCOPE int TtkWidgetConstructorObjCmd(
	ClientData, Tcl_Interp*, int, Tcl_Obj*const[]);

#define RegisterWidget(interp, name, specPtr) \
    Tcl_CreateObjCommand(interp, name, \
	TtkWidgetConstructorObjCmd, (ClientData)specPtr,NULL)

/* WIDGET_TAKES_FOCUS --
 * Add this to the OptionSpecs table of widgets that
 * take keyboard focus during traversal to override
 * CoreOptionSpec's -takefocus default value:
 */
#define WIDGET_TAKES_FOCUS \
    {TK_OPTION_STRING, "-takefocus", "takeFocus", "TakeFocus", \
	"ttk::takefocus", Tk_Offset(WidgetCore, takeFocusPtr), -1, 0,0,0 }

/* WIDGET_INHERIT_OPTIONS(baseOptionSpecs) --
 * Add this at the end of an OptionSpecs table to inherit
 * the options from 'baseOptionSpecs'.
 */
#define WIDGET_INHERIT_OPTIONS(baseOptionSpecs) \
    {TK_OPTION_END, 0,0,0, NULL, -1,-1, 0, (ClientData)baseOptionSpecs, 0}

/*
 * Useful routines for use inside widget implementations:
 */
/* extern int WidgetDestroyed(WidgetCore *); */
#define WidgetDestroyed(corePtr) ((corePtr)->flags & WIDGET_DESTROYED)

MODULE_SCOPE void TtkWidgetChangeState(WidgetCore *,
	unsigned int setBits, unsigned int clearBits);

MODULE_SCOPE void TtkRedisplayWidget(WidgetCore *);
MODULE_SCOPE void TtkResizeWidget(WidgetCore *);

MODULE_SCOPE void TtkTrackElementState(WidgetCore *);
MODULE_SCOPE void TtkBlinkCursor(WidgetCore *);

/*
 * -state option values (compatibility)
 */
MODULE_SCOPE void TtkCheckStateOption(WidgetCore *, Tcl_Obj *);

/*
 * Variable traces:
 */
typedef void (*Ttk_TraceProc)(void *recordPtr, const char *value);
typedef struct TtkTraceHandle_ Ttk_TraceHandle;

MODULE_SCOPE Ttk_TraceHandle *Ttk_TraceVariable(
    Tcl_Interp*, Tcl_Obj *varnameObj, Ttk_TraceProc callback, void *clientData);
MODULE_SCOPE void Ttk_UntraceVariable(Ttk_TraceHandle *);
MODULE_SCOPE int Ttk_FireTrace(Ttk_TraceHandle *);

/*
 * Virtual events:
 */
MODULE_SCOPE void TtkSendVirtualEvent(Tk_Window tgtWin, const char *eventName);

/*
 * Helper routines for data accessor commands:
 */
MODULE_SCOPE int TtkEnumerateOptions(
    Tcl_Interp *, void *, const Tk_OptionSpec *, Tk_OptionTable, Tk_Window);
MODULE_SCOPE int TtkGetOptionValue(
    Tcl_Interp *, void *, Tcl_Obj *optName, Tk_OptionTable, Tk_Window);

/*
 * Helper routines for scrolling widgets (see scroll.c).
 */
typedef struct {
    int 	first;		/* First visible item */
    int 	last;		/* Last visible item */
    int 	total;		/* Total #items */
    char 	*scrollCmd;	/* Widget option */
} Scrollable;

typedef struct ScrollHandleRec *ScrollHandle;

MODULE_SCOPE ScrollHandle TtkCreateScrollHandle(WidgetCore *, Scrollable *);
MODULE_SCOPE void TtkFreeScrollHandle(ScrollHandle);

MODULE_SCOPE int TtkScrollviewCommand(
    Tcl_Interp *interp, int objc, Tcl_Obj *const objv[], ScrollHandle);

MODULE_SCOPE void TtkScrollTo(ScrollHandle, int newFirst);
MODULE_SCOPE void TtkScrolled(ScrollHandle, int first, int last, int total);
MODULE_SCOPE void TtkScrollbarUpdateRequired(ScrollHandle);

/*
 * Tag sets (work in progress, half-baked)
 */

typedef struct TtkTag *Ttk_Tag;
typedef struct TtkTagTable *Ttk_TagTable;

MODULE_SCOPE Ttk_TagTable Ttk_CreateTagTable(Tk_OptionTable, int tagRecSize);
MODULE_SCOPE void Ttk_DeleteTagTable(Ttk_TagTable);

MODULE_SCOPE Ttk_Tag Ttk_GetTag(Ttk_TagTable, const char *tagName);
MODULE_SCOPE Ttk_Tag Ttk_GetTagFromObj(Ttk_TagTable, Tcl_Obj *);

MODULE_SCOPE Tcl_Obj **Ttk_TagRecord(Ttk_Tag);

MODULE_SCOPE int Ttk_GetTagListFromObj(
    Tcl_Interp *interp, Ttk_TagTable, Tcl_Obj *objPtr,
    int *nTags_rtn, void **taglist_rtn);

MODULE_SCOPE void Ttk_FreeTagList(void **taglist);

/*
 * Useful widget base classes:
 */
MODULE_SCOPE Tk_OptionSpec ttkCoreOptionSpecs[];

/*
 * String tables for widget resource specifications:
 */

MODULE_SCOPE const char *ttkOrientStrings[];
MODULE_SCOPE const char *ttkCompoundStrings[];
MODULE_SCOPE const char *ttkDefaultStrings[];

/*
 * ... other option types...
 */
MODULE_SCOPE int TtkGetLabelAnchorFromObj(
	Tcl_Interp*, Tcl_Obj*, Ttk_PositionSpec *);

/*
 * Platform-specific initialization.
 */

#if defined(__WIN32__)
#define Ttk_PlatformInit Ttk_WinPlatformInit
MODULE_SCOPE int Ttk_PlatformInit(Tcl_Interp *);
#elif defined(MAC_OSX_TK)
#define Ttk_PlatformInit Ttk_MacOSXPlatformInit
MODULE_SCOPE int Ttk_PlatformInit(Tcl_Interp *);
#else
#define Ttk_PlatformInit(interp) /* TTK_X11PlatformInit() */
#endif

#endif /* _TTKWIDGET */
