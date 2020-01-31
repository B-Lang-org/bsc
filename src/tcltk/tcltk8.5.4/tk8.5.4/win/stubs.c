#include "tk.h"

/*
 * Undocumented Xlib internal function
 */

int
_XInitImageFuncPtrs(
    XImage *image)
{
    return 0;
}

/*
 * From Xutil.h
 */

void
XSetWMClientMachine(
    Display *display,
    Window w,
    XTextProperty *text_prop)
{
}

Status
XStringListToTextProperty(
    char **list,
    int count,
    XTextProperty *text_prop_return)
{
    return (Status) NULL;
}

/*
 * From Xlib.h
 */

void
XChangeProperty(
    Display *display,
    Window w,
    Atom property,
    Atom type,
    int format,
    int mode,
    _Xconst unsigned char *data,
    int nelements)
{
}

Cursor
XCreateGlyphCursor(
    Display *display,
    Font source_font,
    Font mask_font,
    unsigned int source_char,
    unsigned int mask_char,
    XColor *foreground_color,
    XColor *background_color)
{
    return 1;
}

XIC
XCreateIC(void)
{
    return NULL;
}

Cursor
XCreatePixmapCursor(
    Display *display,
    Pixmap source,
    Pixmap mask,
    XColor *foreground_color,
    XColor *background_color,
    unsigned int x,
    unsigned int y)
{
    return (Cursor) NULL;
}

void
XDeleteProperty(
    Display *display,
    Window w,
    Atom property)
{
}

void
XDestroyIC(
    XIC ic)
{
}

Bool
XFilterEvent(
    XEvent *event,
    Window window)
{
    return 0;
}

void
XForceScreenSaver(
    Display *display,
    int mode)
{
}

void
XFreeCursor(
    Display *display,
    Cursor cursor)
{
}

GContext
XGContextFromGC(
    GC gc)
{
    return (GContext) NULL;
}

char *
XGetAtomName(
    Display *display,
    Atom atom)
{
    return NULL;
}

int
XGetWindowAttributes(
    Display *display,
    Window w,
    XWindowAttributes *window_attributes_return)
{
    return 0;
}

Status
XGetWMColormapWindows(
    Display *display,
    Window w,
    Window **windows_return,
    int *count_return)
{
    return (Status) NULL;
}

int
XIconifyWindow(
    Display *display,
    Window w,
    int screen_number)
{
    return 0;
}

XHostAddress *
XListHosts(
    Display *display,
    int *nhosts_return,
    Bool *state_return)
{
    return NULL;
}

int
XLookupColor(
    Display *display,
    Colormap colormap,
    _Xconst char *color_name,
    XColor *exact_def_return,
    XColor *screen_def_return)
{
    return 0;
}

void
XNextEvent(
    Display *display,
    XEvent *event_return)
{
}

void
XPutBackEvent(
    Display *display,
    XEvent *event)
{
}

void
XQueryColors(
    Display *display,
    Colormap colormap,
    XColor *defs_in_out,
    int ncolors)
{
}

int
XQueryTree(
    Display *display,
    Window w,
    Window *root_return,
    Window *parent_return,
    Window **children_return,
    unsigned int *nchildren_return)
{
    return 0;
}

void
XRefreshKeyboardMapping(
    XMappingEvent *event_map)
{
}

Window
XRootWindow(
    Display *display,
    int screen_number)
{
    return (Window) NULL;
}

void
XSelectInput(
    Display *display,
    Window w,
    long event_mask)
{
}

int
XSendEvent(
    Display *display,
    Window w,
    Bool propagate,
    long event_mask,
    XEvent *event_send)
{
    return 0;
}

void
XSetCommand(
    Display *display,
    Window w,
    CONST char **argv,
    int argc)
{
}

XErrorHandler
XSetErrorHandler(
    XErrorHandler handler)
{
    return NULL;
}

void
XSetIconName(
    Display *display,
    Window w,
    _Xconst char *icon_name)
{
}

void
XSetWindowBackground(
    Display *display,
    Window w,
    unsigned long background_pixel)
{
}

void
XSetWindowBackgroundPixmap(
    Display *display,
    Window w,
    Pixmap background_pixmap)
{
}

void
XSetWindowBorder(
    Display *display,
    Window w,
    unsigned long border_pixel)
{
}

void
XSetWindowBorderPixmap(
    Display *display,
    Window w,
    Pixmap border_pixmap)
{
}

void
XSetWindowBorderWidth(
    Display *display,
    Window w,
    unsigned int width)
{
}

void
XSetWindowColormap(
    Display *display,
    Window w,
    Colormap colormap)
{
}

Bool
XTranslateCoordinates(
    Display *display,
    Window src_w,
    Window dest_w,
    int src_x,
    int src_y,
    int *dest_x_return,
    int *dest_y_return,
    Window *child_return)
{
    return 0;
}

void
XWindowEvent(
    Display *display,
    Window w,
    long event_mask,
    XEvent *event_return)
{
}

int
XWithdrawWindow(
    Display *display,
    Window w,
    int screen_number)
{
    return 0;
}

int
XmbLookupString(
    XIC ic,
    XKeyPressedEvent *event,
    char *buffer_return,
    int bytes_buffer,
    KeySym *keysym_return,
    Status *status_return)
{
    return 0;
}

int
XGetWindowProperty(
    Display *display,
    Window w,
    Atom property,
    long long_offset,
    long long_length,
    Bool delete,
    Atom req_type,
    Atom *actual_type_return,
    int *actual_format_return,
    unsigned long *nitems_return,
    unsigned long *bytes_after_return,
    unsigned char **prop_return)
{
    *actual_type_return = None;
    *actual_format_return = 0;
    *nitems_return = 0;
    *bytes_after_return = 0;
    *prop_return = NULL;
    return BadValue;
}
