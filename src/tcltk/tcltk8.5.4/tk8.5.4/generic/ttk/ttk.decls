#
# $Id: ttk.decls,v 1.2 2006/12/10 19:19:44 jenglish Exp $
#

library 	ttk
interface 	ttk
epoch  		0
scspec		TTKAPI

declare 0 current {
    Ttk_Theme Ttk_GetTheme(Tcl_Interp *interp, const char *name);
}
declare 1 current {
    Ttk_Theme Ttk_GetDefaultTheme(Tcl_Interp *interp);
}
declare 2 current {
    Ttk_Theme Ttk_GetCurrentTheme(Tcl_Interp *interp);
}
declare 3 current {
    Ttk_Theme Ttk_CreateTheme(
	Tcl_Interp *interp, const char *name, Ttk_Theme parent);
}
declare 4 current {
    void Ttk_RegisterCleanup(
	Tcl_Interp *interp, void *deleteData, Ttk_CleanupProc *cleanupProc);
}

declare 5 current {
    int Ttk_RegisterElementSpec(
	Ttk_Theme theme, 
	const char *elementName,
	Ttk_ElementSpec *elementSpec,
	void *clientData);
}

declare 6 current {
    Ttk_ElementImpl Ttk_RegisterElement(
	Tcl_Interp *interp,
	Ttk_Theme theme, 
	const char *elementName,
	Ttk_ElementSpec *elementSpec,
	void *clientData);
}

declare 7 current {
    int Ttk_RegisterElementFactory(
	Tcl_Interp *interp, 
	const char *name,
	Ttk_ElementFactory factoryProc,
	void *clientData);
}

declare 8 current {
    void Ttk_RegisterLayout(
	Ttk_Theme theme, const char *className, Ttk_LayoutSpec layoutSpec);
}

#
# State maps.
#
declare 10 current {
    int Ttk_GetStateSpecFromObj(
    	Tcl_Interp *interp, Tcl_Obj *objPtr, Ttk_StateSpec *spec_rtn);
}
declare 11 current {
    Tcl_Obj *Ttk_NewStateSpecObj(
    	unsigned int onbits,unsigned int offbits);
}
declare 12 current {
    Ttk_StateMap Ttk_GetStateMapFromObj(
    	Tcl_Interp *interp, Tcl_Obj *objPtr);
}
declare 13 current {
    Tcl_Obj *Ttk_StateMapLookup(
	Tcl_Interp *interp, Ttk_StateMap map, Ttk_State state);
}
declare 14 current {
    int Ttk_StateTableLookup(
    	Ttk_StateTable map[], Ttk_State state);
}


#
# Low-level geometry utilities.
#
declare 20 current {
    int Ttk_GetPaddingFromObj(
    	Tcl_Interp *interp, 
	Tk_Window tkwin, 
	Tcl_Obj *objPtr, 
	Ttk_Padding *pad_rtn);
}
declare 21 current {
    int Ttk_GetBorderFromObj(
    	Tcl_Interp *interp, 
	Tcl_Obj *objPtr, 
	Ttk_Padding *pad_rtn);
}
declare 22 current {
    int Ttk_GetStickyFromObj(
    	Tcl_Interp *interp, Tcl_Obj *objPtr, Ttk_Sticky *sticky_rtn);
}
declare 23 current {
    Ttk_Padding Ttk_MakePadding(
    	short l, short t, short r, short b);
}
declare 24 current {
    Ttk_Padding Ttk_UniformPadding(
    	short borderWidth);
}
declare 25 current {
    Ttk_Padding Ttk_AddPadding(Ttk_Padding pad1, Ttk_Padding pad2);
}
declare 26 current {
    Ttk_Padding Ttk_RelievePadding(
    	Ttk_Padding padding, int relief, int n);
}
declare 27 current {
    Ttk_Box Ttk_MakeBox(int x, int y, int width, int height);
}
declare 28 current {
    int Ttk_BoxContains(Ttk_Box box, int x, int y);
}
declare 29 current {
    Ttk_Box Ttk_PackBox(Ttk_Box *cavity, int w, int h, Ttk_Side side);
}
declare 30 current {
    Ttk_Box Ttk_StickBox(Ttk_Box parcel, int w, int h, Ttk_Sticky sticky);
}
declare 31 current {
    Ttk_Box Ttk_AnchorBox(Ttk_Box parcel, int w, int h, Tk_Anchor anchor);
}
declare 32 current {
    Ttk_Box Ttk_PadBox(Ttk_Box b, Ttk_Padding p);
}
declare 33 current {
    Ttk_Box Ttk_ExpandBox(Ttk_Box b, Ttk_Padding p);
}
declare 34 current {
    Ttk_Box Ttk_PlaceBox(
	Ttk_Box *cavity, int w, int h, Ttk_Side side, Ttk_Sticky sticky);
}
declare 35 current {
    Tcl_Obj *Ttk_NewBoxObj(Ttk_Box box);
}

#
# Utilities.
#
declare 40 current {
    int Ttk_GetOrientFromObj(Tcl_Interp *interp, Tcl_Obj *objPtr, int *orient);
}


