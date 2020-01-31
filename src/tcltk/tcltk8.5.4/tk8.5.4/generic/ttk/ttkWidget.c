/* $Id: ttkWidget.c,v 1.11 2008/01/06 22:35:41 jenglish Exp $
 * Copyright (c) 2003, Joe English
 *
 * Core widget utilities.
 */

#include <string.h>
#include <tk.h>
#include "ttkTheme.h"
#include "ttkWidget.h"

#ifdef MAC_OSX_TK
#define TK_NO_DOUBLE_BUFFERING 1
#endif

/*------------------------------------------------------------------------
 * +++ Internal helper routines.
 */

/* UpdateLayout --
 * 	Call the widget's get-layout hook to recompute corePtr->layout.
 * 	Returns TCL_OK if successful, returns TCL_ERROR and leaves
 * 	the layout unchanged otherwise.
 */
static int UpdateLayout(Tcl_Interp *interp, WidgetCore *corePtr)
{
    Ttk_Theme themePtr = Ttk_GetCurrentTheme(interp);
    Ttk_Layout newLayout =
    	corePtr->widgetSpec->getLayoutProc(interp, themePtr,corePtr);

    if (newLayout) {
	if (corePtr->layout) {
	    Ttk_FreeLayout(corePtr->layout);
	}
	corePtr->layout = newLayout;
	return TCL_OK;
    }
    return TCL_ERROR;
}

/* SizeChanged --
 * 	Call the widget's sizeProc to compute new requested size
 * 	and pass it to the geometry manager.
 */
static void SizeChanged(WidgetCore *corePtr)
{
    int reqWidth = 1, reqHeight = 1;

    if (corePtr->widgetSpec->sizeProc(corePtr,&reqWidth,&reqHeight)) {
	Tk_GeometryRequest(corePtr->tkwin, reqWidth, reqHeight);
    }
}

#ifndef TK_NO_DOUBLE_BUFFERING

/* BeginDrawing --
 * 	Returns a Drawable for drawing the widget contents.
 *	This is normally an off-screen Pixmap, copied to
 *	the window by EndDrawing().
 */
static Drawable BeginDrawing(Tk_Window tkwin)
{
    return Tk_GetPixmap(Tk_Display(tkwin), Tk_WindowId(tkwin),
	    Tk_Width(tkwin), Tk_Height(tkwin),
	    DefaultDepthOfScreen(Tk_Screen(tkwin)));
}

/* EndDrawing --
 *	Copy the drawable contents to the screen and release resources.
 */
static void EndDrawing(Tk_Window tkwin, Drawable d)
{
    XGCValues gcValues;
    GC gc;

    gcValues.function = GXcopy;
    gcValues.graphics_exposures = False;
    gc = Tk_GetGC(tkwin, GCFunction|GCGraphicsExposures, &gcValues);

    XCopyArea(Tk_Display(tkwin), d, Tk_WindowId(tkwin), gc,
	    0, 0, (unsigned) Tk_Width(tkwin), (unsigned) Tk_Height(tkwin),
	    0, 0);

    Tk_FreePixmap(Tk_Display(tkwin), d);
    Tk_FreeGC(Tk_Display(tkwin), gc);
}
#else
/* No double-buffering: draw directly into the window. */
static Drawable BeginDrawing(Tk_Window tkwin) { return Tk_WindowId(tkwin); }
static void EndDrawing(Tk_Window tkwin, Drawable d) { }
#endif

/* DrawWidget --
 *	Redraw a widget.  Called as an idle handler.
 */
static void DrawWidget(ClientData recordPtr)
{
    WidgetCore *corePtr = recordPtr;

    corePtr->flags &= ~REDISPLAY_PENDING;
    if (Tk_IsMapped(corePtr->tkwin)) {
	Drawable d = BeginDrawing(corePtr->tkwin);
	corePtr->widgetSpec->layoutProc(recordPtr);
	corePtr->widgetSpec->displayProc(recordPtr, d);
	EndDrawing(corePtr->tkwin, d);
    }
}

/* TtkRedisplayWidget --
 * 	Schedule redisplay as an idle handler.
 */
void TtkRedisplayWidget(WidgetCore *corePtr)
{
    if (corePtr->flags & WIDGET_DESTROYED) {
	return;
    }

    if (!(corePtr->flags & REDISPLAY_PENDING)) {
	Tcl_DoWhenIdle(DrawWidget, (ClientData) corePtr);
	corePtr->flags |= REDISPLAY_PENDING;
    }
}

/* TtkResizeWidget --
 * 	Recompute widget size, schedule geometry propagation and redisplay.
 */
void TtkResizeWidget(WidgetCore *corePtr)
{
    if (corePtr->flags & WIDGET_DESTROYED) {
	return;
    }

    SizeChanged(corePtr);
    TtkRedisplayWidget(corePtr);
}

/* TtkWidgetChangeState --
 * 	Set / clear the specified bits in the 'state' flag,
 */
void TtkWidgetChangeState(WidgetCore *corePtr,
    unsigned int setBits, unsigned int clearBits)
{
    Ttk_State oldState = corePtr->state;
    corePtr->state = (oldState & ~clearBits) | setBits;
    if (corePtr->state ^ oldState) {
	TtkRedisplayWidget(corePtr);
    }
}

/* TtkWidgetEnsembleCommand --
 * 	Invoke an ensemble defined by a WidgetCommandSpec.
 */
int TtkWidgetEnsembleCommand(
    const WidgetCommandSpec *commands,	/* Ensemble definition */
    int cmdIndex,			/* Index of command word */
    Tcl_Interp *interp,			/* Interpreter to use */
    int objc, Tcl_Obj *const objv[],	/* Argument vector */
    void *clientData)			/* User data (widget record pointer) */
{
    int index;

    if (objc <= cmdIndex) {
	Tcl_WrongNumArgs(interp, cmdIndex, objv, "option ?arg arg...?");
	return TCL_ERROR;
    }
    if (Tcl_GetIndexFromObjStruct(interp, objv[cmdIndex], commands,
		sizeof(commands[0]), "command", 0, &index) != TCL_OK)
    {
	return TCL_ERROR;
    }
    return commands[index].command(interp, objc, objv, clientData);
}

/*
 * WidgetInstanceObjCmd --
 *	Widget instance command implementation.
 */
static int
WidgetInstanceObjCmd(
    ClientData clientData,		/* Widget record pointer */
    Tcl_Interp *interp,			/* Current interpreter. */
    int objc,				/* Number of arguments. */
    Tcl_Obj * const objv[])		/* Argument objects. */
{
    WidgetCore *corePtr = (WidgetCore *)clientData;
    const WidgetCommandSpec *commands = corePtr->widgetSpec->commands;
    int status = TCL_OK;

    Tcl_Preserve(clientData);
    status = TtkWidgetEnsembleCommand(commands,1, interp,objc,objv,clientData);
    Tcl_Release(clientData);

    return status;
}

/*
 * Command deletion callback for widget instance commands.
 */
static void
WidgetInstanceObjCmdDeleted(ClientData clientData)
{
    WidgetCore *corePtr = (WidgetCore *) clientData;
    corePtr->widgetCmd = NULL;
    if (corePtr->tkwin != NULL)
	Tk_DestroyWindow(corePtr->tkwin);
}

/*
 * WidgetCleanup --
 *	 Final cleanup for widget.
 *
 * @@@ TODO: check all code paths leading to widget destruction,
 * @@@ describe here.
 * @@@ Call widget-specific cleanup routine at an appropriate point.
 */
static void
WidgetCleanup(char *memPtr)
{
    ckfree(memPtr);
}

/*
 * CoreEventProc --
 *	Event handler for basic events.
 *	Processes Expose, Configure, FocusIn/Out, and Destroy events.
 *	Also handles <<ThemeChanged>> virtual events.
 *
 *	For Expose and Configure, simply schedule the widget for redisplay.
 *	For Destroy events, handle the cleanup process.
 *
 *	For Focus events, set/clear the focus bit in the state field.
 *	It turns out this is impossible to do correctly in a binding script,
 *	because Tk filters out focus events with detail == NotifyInferior.
 *
 *	For Deactivate/Activate pseudo-events, set/clear the background state
 *	flag.
 */

static const unsigned CoreEventMask
    = ExposureMask
    | StructureNotifyMask
    | FocusChangeMask
    | VirtualEventMask
    | ActivateMask
    ;

static void CoreEventProc(ClientData clientData, XEvent *eventPtr)
{
    WidgetCore *corePtr = (WidgetCore *) clientData;

    switch (eventPtr->type)
    {
	case ConfigureNotify :
	    TtkRedisplayWidget(corePtr);
	    break;
	case Expose :
	    if (eventPtr->xexpose.count == 0) {
		TtkRedisplayWidget(corePtr);
	    }
	    break;
	case DestroyNotify :
	    corePtr->flags |= WIDGET_DESTROYED;

	    Tk_DeleteEventHandler(corePtr->tkwin,
		    CoreEventMask,CoreEventProc,clientData);

	    if (corePtr->flags & REDISPLAY_PENDING) {
		Tcl_CancelIdleCall(DrawWidget, clientData);
	    }

	    corePtr->widgetSpec->cleanupProc(corePtr);

	    Tk_FreeConfigOptions(
		clientData, corePtr->optionTable, corePtr->tkwin);
	    corePtr->tkwin = NULL;

	    if (corePtr->layout) {
		Ttk_FreeLayout(corePtr->layout);
	    }

	    /* NB: this can reenter the interpreter via a command traces */
	    if (corePtr->widgetCmd) {
		Tcl_Command cmd = corePtr->widgetCmd;
		corePtr->widgetCmd = 0;
		Tcl_DeleteCommandFromToken(corePtr->interp, cmd);
	    }
	    Tcl_EventuallyFree(clientData, WidgetCleanup);
	    break;

	case FocusIn:
	case FocusOut:
	    /* Don't process "virtual crossing" events */
	    if (   eventPtr->xfocus.detail == NotifyInferior
		|| eventPtr->xfocus.detail == NotifyAncestor
		|| eventPtr->xfocus.detail == NotifyNonlinear)
	    {
		if (eventPtr->type == FocusIn)
		    corePtr->state |= TTK_STATE_FOCUS;
		else
		    corePtr->state &= ~TTK_STATE_FOCUS;
		TtkRedisplayWidget(corePtr);
	    }
	    break;
	case ActivateNotify:
	    corePtr->state &= ~TTK_STATE_BACKGROUND;
	    TtkRedisplayWidget(corePtr);
	    break;
	case DeactivateNotify:
	    corePtr->state |= TTK_STATE_BACKGROUND;
	    TtkRedisplayWidget(corePtr);
	    break;
	case VirtualEvent:
	    if (!strcmp("ThemeChanged", ((XVirtualEvent *)(eventPtr))->name)) {
		(void)UpdateLayout(corePtr->interp, corePtr);
		SizeChanged(corePtr);
		TtkRedisplayWidget(corePtr);
	    }
	default:
	    /* can't happen... */
	    break;
    }
}

/*
 * WidgetWorldChanged --
 * 	Default Tk_ClassWorldChangedProc() for widgets.
 * 	Invoked whenever fonts or other system resources are changed;
 * 	recomputes geometry.
 */
static void WidgetWorldChanged(ClientData clientData)
{
    WidgetCore *corePtr = (WidgetCore*)clientData;
    SizeChanged(corePtr);
    TtkRedisplayWidget(corePtr);
}

static struct Tk_ClassProcs widgetClassProcs = {
    sizeof(Tk_ClassProcs),
    WidgetWorldChanged
};

/*
 * TtkWidgetConstructorObjCmd --
 *	General-purpose widget constructor command implementation.
 *	ClientData is a WidgetSpec *.
 */
int TtkWidgetConstructorObjCmd(
    ClientData clientData, Tcl_Interp *interp, int objc, Tcl_Obj *CONST objv[])
{
    WidgetSpec *widgetSpec = (WidgetSpec *)clientData;
    const char *className = widgetSpec->className;
    WidgetCore *corePtr;
    ClientData recordPtr;
    Tk_Window tkwin;
    Tk_OptionTable optionTable;
    int i;

    if (objc < 2 || objc % 1 == 1) {
	Tcl_WrongNumArgs(interp, 1, objv, "pathName ?options?");
	return TCL_ERROR;
    }

    tkwin = Tk_CreateWindowFromPath(interp, Tk_MainWindow(interp),
	    Tcl_GetStringFromObj(objv[1], NULL), (char *) NULL);
    if (tkwin == NULL)
	return TCL_ERROR;

    /*
     * Check if a -class resource has been specified:
     * We have to do this before the InitOptions() call,
     * since InitOptions() is affected by the widget class.
     */
    for (i = 2; i < objc; i += 2) {
	const char *resourceName = Tcl_GetString(objv[i]);
	if (!strcmp(resourceName, "-class")) {
	    className = Tcl_GetString(objv[i+1]);
	    break;
	}
    }

    Tk_SetClass(tkwin, className);

    /*
     * Set the BackgroundPixmap to ParentRelative here, so
     * subclasses don't need to worry about setting the background.
     */
    Tk_SetWindowBackgroundPixmap(tkwin, ParentRelative);

    optionTable = Tk_CreateOptionTable(interp, widgetSpec->optionSpecs);

    /*
     * Allocate and initialize the widget record.
     */
    recordPtr = ckalloc(widgetSpec->recordSize);
    memset(recordPtr, 0, widgetSpec->recordSize);
    corePtr = (WidgetCore *)recordPtr;

    corePtr->tkwin	= tkwin;
    corePtr->interp 	= interp;
    corePtr->widgetSpec	= widgetSpec;
    corePtr->widgetCmd	= Tcl_CreateObjCommand(interp, Tk_PathName(tkwin),
	WidgetInstanceObjCmd, recordPtr, WidgetInstanceObjCmdDeleted);
    corePtr->optionTable = optionTable;

    Tk_SetClassProcs(tkwin, &widgetClassProcs, recordPtr);

    if (Tk_InitOptions(interp, recordPtr, optionTable, tkwin) != TCL_OK)
    	goto error_nocleanup;

    if (widgetSpec->initializeProc(interp, recordPtr) != TCL_OK)
	goto error_nocleanup;

    if (Tk_SetOptions(interp, recordPtr, optionTable, objc - 2,
	    objv + 2, tkwin, NULL/*savePtr*/, (int *)NULL/*maskPtr*/) != TCL_OK)
	goto error;

    if (widgetSpec->configureProc(interp, recordPtr, ~0) != TCL_OK)
	goto error;

    if (widgetSpec->postConfigureProc(interp, recordPtr, ~0) != TCL_OK)
	goto error;

    if (WidgetDestroyed(corePtr))
	goto error;

    if (UpdateLayout(interp, corePtr) != TCL_OK)
	goto error;

    SizeChanged(corePtr);
    Tk_CreateEventHandler(tkwin, CoreEventMask, CoreEventProc, recordPtr);

    Tk_MakeWindowExist(tkwin);

    Tcl_SetObjResult(interp, Tcl_NewStringObj(Tk_PathName(tkwin), -1));

    return TCL_OK;

error:
    widgetSpec->cleanupProc(recordPtr);
error_nocleanup:
    if (corePtr->layout) {
	Ttk_FreeLayout(corePtr->layout);
	corePtr->layout = 0;
    }
    Tk_FreeConfigOptions(recordPtr, optionTable, tkwin);
    Tk_DestroyWindow(tkwin);
    corePtr->tkwin = 0;
    Tcl_DeleteCommandFromToken(interp, corePtr->widgetCmd);
    ckfree(recordPtr);
    return TCL_ERROR;
}

/*------------------------------------------------------------------------
 * +++ Default implementations for widget hook procedures.
 */

/* TtkWidgetGetLayout --
 * 	Default getLayoutProc.
 *	Looks up the layout based on the -style resource (if specified),
 *	otherwise use the widget class.
 */
Ttk_Layout TtkWidgetGetLayout(
    Tcl_Interp *interp, Ttk_Theme themePtr, void *recordPtr)
{
    WidgetCore *corePtr = recordPtr;
    const char *styleName = 0;

    if (corePtr->styleObj)
    	styleName = Tcl_GetString(corePtr->styleObj);

    if (!styleName || *styleName == '\0')
    	styleName = corePtr->widgetSpec->className;

    return Ttk_CreateLayout(interp, themePtr, styleName,
	recordPtr, corePtr->optionTable, corePtr->tkwin);
}

/*
 * TtkWidgetGetOrientedLayout --
 * 	Helper routine.  Same as TtkWidgetGetLayout, but prefixes
 * 	"Horizontal." or "Vertical." to the style name, depending
 * 	on the value of the 'orient' option.
 */
Ttk_Layout TtkWidgetGetOrientedLayout(
    Tcl_Interp *interp, Ttk_Theme themePtr, void *recordPtr, Tcl_Obj *orientObj)
{
    WidgetCore *corePtr = recordPtr;
    const char *baseStyleName = 0;
    Tcl_DString styleName;
    int orient = TTK_ORIENT_HORIZONTAL;
    Ttk_Layout layout;

    Tcl_DStringInit(&styleName);

    /* Prefix:
     */
    Ttk_GetOrientFromObj(NULL, orientObj, &orient);
    if (orient == TTK_ORIENT_HORIZONTAL)
	Tcl_DStringAppend(&styleName, "Horizontal.", -1);
    else
	Tcl_DStringAppend(&styleName, "Vertical.", -1);

    /* Add base style name:
     */
    if (corePtr->styleObj)
    	baseStyleName = Tcl_GetString(corePtr->styleObj);
    if (!baseStyleName || *baseStyleName == '\0')
    	baseStyleName = corePtr->widgetSpec->className;

    Tcl_DStringAppend(&styleName, baseStyleName, -1);

    /* Create layout:
     */
    layout= Ttk_CreateLayout(interp, themePtr, Tcl_DStringValue(&styleName),
	recordPtr, corePtr->optionTable, corePtr->tkwin);

    Tcl_DStringFree(&styleName);

    return layout;
}

/* TtkNullInitialize --
 * 	Default widget initializeProc (no-op)
 */
int TtkNullInitialize(Tcl_Interp *interp, void *recordPtr)
{
    return TCL_OK;
}

/* TtkNullPostConfigure --
 * 	Default widget postConfigureProc (no-op)
 */
int TtkNullPostConfigure(Tcl_Interp *interp, void *clientData, int mask)
{
    return TCL_OK;
}

/* TtkCoreConfigure --
 * 	Default widget configureProc.
 * 	Handles -style option.
 */
int TtkCoreConfigure(Tcl_Interp *interp, void *clientData, int mask)
{
    WidgetCore *corePtr = clientData;
    int status = TCL_OK;

    if (mask & STYLE_CHANGED) {
	status = UpdateLayout(interp, corePtr);
    }

    return status;
}

/* TtkNullCleanup --
 * 	Default widget cleanupProc (no-op)
 */
void TtkNullCleanup(void *recordPtr)
{
    return;
}

/* TtkWidgetDoLayout --
 * 	Default widget layoutProc.
 */
void TtkWidgetDoLayout(void *clientData)
{
    WidgetCore *corePtr = clientData;
    Ttk_PlaceLayout(corePtr->layout,corePtr->state,Ttk_WinBox(corePtr->tkwin));
}

/* TtkWidgetDisplay --
 * 	Default widget displayProc.
 */
void TtkWidgetDisplay(void *recordPtr, Drawable d)
{
    WidgetCore *corePtr = recordPtr;
    Ttk_DrawLayout(corePtr->layout, corePtr->state, d);
}

/* TtkWidgetSize --
 * 	Default widget sizeProc()
 */
int TtkWidgetSize(void *recordPtr, int *widthPtr, int *heightPtr)
{
    WidgetCore *corePtr = recordPtr;
    Ttk_LayoutSize(corePtr->layout, corePtr->state, widthPtr, heightPtr);
    return 1;
}

/*------------------------------------------------------------------------
 * +++ Default implementations for widget subcommands.
 */

/* $w cget -option
 */
int TtkWidgetCgetCommand(
Tcl_Interp *interp, int objc, Tcl_Obj * CONST objv[], void *recordPtr)
{
    WidgetCore *corePtr = recordPtr;
    Tcl_Obj *result;

    if (objc != 3) {
	Tcl_WrongNumArgs(interp, 2, objv, "option");
	return TCL_ERROR;
    }
    result = Tk_GetOptionValue(interp, recordPtr,
		corePtr->optionTable, objv[2], corePtr->tkwin);
    if (result == NULL)
	return TCL_ERROR;
    Tcl_SetObjResult(interp, result);
    return TCL_OK;
}

/* $w configure ?-option ?value ....??
 */
int TtkWidgetConfigureCommand(
Tcl_Interp *interp, int objc, Tcl_Obj *CONST objv[], void *recordPtr)
{
    WidgetCore *corePtr = recordPtr;
    Tcl_Obj *result;

    if (objc == 2) {
	result = Tk_GetOptionInfo(interp, recordPtr,
		corePtr->optionTable, (Tcl_Obj *) NULL, corePtr->tkwin);
    } else if (objc == 3) {
	result = Tk_GetOptionInfo(interp, recordPtr,
		corePtr->optionTable, objv[2], corePtr->tkwin);
    } else {
	Tk_SavedOptions savedOptions;
	int status;
	int mask = 0;

	status = Tk_SetOptions(interp, recordPtr,
		corePtr->optionTable, objc - 2, objv + 2,
		corePtr->tkwin, &savedOptions, &mask);
	if (status != TCL_OK)
	    return status;

	if (mask & READONLY_OPTION) {
	    Tcl_SetResult(interp,
		    "Attempt to change read-only option", TCL_STATIC);
	    Tk_RestoreSavedOptions(&savedOptions);
	    return TCL_ERROR;
	}

	status = corePtr->widgetSpec->configureProc(interp, recordPtr, mask);
	if (status != TCL_OK) {
	    Tk_RestoreSavedOptions(&savedOptions);
	    return status;
	}
	Tk_FreeSavedOptions(&savedOptions);

	status = corePtr->widgetSpec->postConfigureProc(interp,recordPtr,mask);
	if (status != TCL_OK) {
	    return status;
	}

	if (mask & (STYLE_CHANGED | GEOMETRY_CHANGED)) {
	    SizeChanged(corePtr);
	}

	TtkRedisplayWidget(corePtr);
	result = Tcl_NewObj();
    }

    if (result == 0) {
	return TCL_ERROR;
    }
    Tcl_SetObjResult(interp, result);
    return TCL_OK;
}

/* $w state ? $stateSpec ?
 *
 * 	If $stateSpec is specified, modify the widget state accordingly,
 * 	return a new stateSpec representing the changed bits.
 *
 * 	Otherwise, return a statespec matching all the currently-set bits.
 */

int TtkWidgetStateCommand(
    Tcl_Interp *interp, int objc, Tcl_Obj *CONST objv[], void *recordPtr)
{
    WidgetCore *corePtr = recordPtr;
    Ttk_StateSpec spec;
    int status;
    Ttk_State oldState, changed;

    if (objc == 2) {
	Tcl_SetObjResult(interp,
	    Ttk_NewStateSpecObj(corePtr->state, 0ul));
	return TCL_OK;
    }

    if (objc != 3) {
	Tcl_WrongNumArgs(interp, 2, objv, "state-spec");
	return TCL_ERROR;
    }
    status = Ttk_GetStateSpecFromObj(interp, objv[2], &spec);
    if (status != TCL_OK)
	return status;

    oldState = corePtr->state;
    corePtr->state = Ttk_ModifyState(corePtr->state, &spec);
    changed = corePtr->state ^ oldState;

    TtkRedisplayWidget(corePtr);

    Tcl_SetObjResult(interp,
	Ttk_NewStateSpecObj(oldState & changed, ~oldState & changed));
    return status;
}

/* $w instate $stateSpec ?$script?
 *
 * 	Tests if widget state matches $stateSpec.
 *	If $script is specified, execute script if state matches.
 *	Otherwise, return true/false
 */

int TtkWidgetInstateCommand(
    Tcl_Interp *interp, int objc, Tcl_Obj *CONST objv[], void *recordPtr)
{
    WidgetCore *corePtr = recordPtr;
    Ttk_State state = corePtr->state;
    Ttk_StateSpec spec;
    int status = TCL_OK;

    if (objc < 3 || objc > 4) {
	Tcl_WrongNumArgs(interp, 2, objv, "state-spec ?script?");
	return TCL_ERROR;
    }
    status = Ttk_GetStateSpecFromObj(interp, objv[2], &spec);
    if (status != TCL_OK)
	return status;

    if (objc == 3) {
	Tcl_SetObjResult(interp,
	    Tcl_NewBooleanObj(Ttk_StateMatches(state,&spec)));
    } else if (objc == 4) {
	if (Ttk_StateMatches(state,&spec)) {
	    status = Tcl_EvalObjEx(interp, objv[3], 0);
	}
    }
    return status;
}

/* $w identify $x $y
 * 	Returns: name of element at $x, $y
 */
int TtkWidgetIdentifyCommand(
    Tcl_Interp *interp, int objc, Tcl_Obj *CONST objv[], void *recordPtr)
{
    WidgetCore *corePtr = recordPtr;
    Ttk_LayoutNode *node;
    int x, y;

    if (objc != 4) {
	Tcl_WrongNumArgs(interp, 2, objv, "x y");
	return TCL_ERROR;
    }

    if (Tcl_GetIntFromObj(interp, objv[2], &x) != TCL_OK
	|| Tcl_GetIntFromObj(interp, objv[3], &y) != TCL_OK)
	return TCL_ERROR;

    node = Ttk_LayoutIdentify(corePtr->layout, x, y);
    if (node) {
	const char *elementName = Ttk_LayoutNodeName(node);
	Tcl_SetObjResult(interp,Tcl_NewStringObj(elementName,-1));
    }

    return TCL_OK;
}

/*EOF*/
