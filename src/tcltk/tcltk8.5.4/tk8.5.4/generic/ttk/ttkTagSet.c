/* $Id: ttkTagSet.c,v 1.3 2007/01/11 19:59:26 jenglish Exp $
 *
 * Ttk widget set: tag tables.  Half-baked, work in progress.
 *
 * Copyright (C) 2005, Joe English.  Freely redistributable.
 */

#include <string.h>	/* for memset() */
#include <tcl.h>
#include <tk.h>

#include "ttkTheme.h"
#include "ttkWidget.h"

/*------------------------------------------------------------------------
 * +++ Internal data structures.
 */
struct TtkTag {
    Tcl_Obj **tagRecord;	/* ... hrmph. */
};

struct TtkTagTable {
    Tk_OptionTable	tagOptionTable;	/* ... */
    int         	tagRecordSize;	/* size of tag record */
    Tcl_HashTable	tags;		/* defined tags */
};

/*------------------------------------------------------------------------
 * +++ Tags.
 */
static Ttk_Tag NewTag(Ttk_TagTable tagTable)
{
    Ttk_Tag tag = (Ttk_Tag)ckalloc(sizeof(*tag));
    tag->tagRecord = (Tcl_Obj **)ckalloc(tagTable->tagRecordSize);
    memset(tag->tagRecord, 0, tagTable->tagRecordSize);
    return tag;
}

static void DeleteTag(Ttk_Tag tag, int nOptions) 
{
    int i;
    for (i = 0; i < nOptions; ++i) {
	if (tag->tagRecord[i]) {
	    Tcl_DecrRefCount(tag->tagRecord[i]);
	}
    }
    ckfree((void*)tag->tagRecord);
    ckfree((void*)tag);
}

Tcl_Obj **Ttk_TagRecord(Ttk_Tag tag)
{
    return tag->tagRecord;
}

/*------------------------------------------------------------------------
 * +++ Tag tables.
 */

Ttk_TagTable Ttk_CreateTagTable(
    Tk_OptionTable tagOptionTable, int tagRecordSize)
{
    Ttk_TagTable tagTable = (Ttk_TagTable)ckalloc(sizeof(*tagTable));
    tagTable->tagOptionTable = tagOptionTable;
    tagTable->tagRecordSize = tagRecordSize;
    Tcl_InitHashTable(&tagTable->tags, TCL_STRING_KEYS);
    return tagTable;
}

void Ttk_DeleteTagTable(Ttk_TagTable tagTable)
{
    Tcl_HashSearch search;
    Tcl_HashEntry *entryPtr;
    int nOptions = tagTable->tagRecordSize / sizeof(Tcl_Obj *);

    entryPtr = Tcl_FirstHashEntry(&tagTable->tags, &search);
    while (entryPtr != NULL) {
	DeleteTag(Tcl_GetHashValue(entryPtr), nOptions);
	entryPtr = Tcl_NextHashEntry(&search);
    }

    Tcl_DeleteHashTable(&tagTable->tags);
    ckfree((void*)tagTable);
}

Ttk_Tag Ttk_GetTag(Ttk_TagTable tagTable, const char *tagName)
{
    int isNew = 0;
    Tcl_HashEntry *entryPtr = Tcl_CreateHashEntry(
	&tagTable->tags, tagName, &isNew);

    if (isNew) {
	Tcl_SetHashValue(entryPtr, NewTag(tagTable));
    }
    return Tcl_GetHashValue(entryPtr);
}

Ttk_Tag Ttk_GetTagFromObj(Ttk_TagTable tagTable, Tcl_Obj *objPtr)
{
    return Ttk_GetTag(tagTable, Tcl_GetString(objPtr));
}

/* Ttk_GetTagListFromObj --
 * 	Extract an array of pointers to Ttk_Tags from a Tcl_Obj.
 * 	(suitable for passing to Tk_BindEvent).
 *
 * Result must be passed to Ttk_FreeTagList().
 */
extern int Ttk_GetTagListFromObj(
    Tcl_Interp *interp, 
    Ttk_TagTable tagTable,
    Tcl_Obj *objPtr,
    int *nTags_rtn,
    void **taglist_rtn)
{
    Tcl_Obj **objv;
    int i, objc;
    void **tags;

    *taglist_rtn = NULL; *nTags_rtn = 0;

    if (objPtr == NULL) {
	return TCL_OK;
    }

    if (Tcl_ListObjGetElements(interp, objPtr, &objc, &objv) != TCL_OK) {
    	return TCL_ERROR;
    }

    tags = (void**)ckalloc((objc+1) * sizeof(void*));
    for (i=0; i<objc; ++i) {
	tags[i] = Ttk_GetTagFromObj(tagTable, objv[i]);
    }
    tags[i] = NULL;

    *taglist_rtn = tags;
    *nTags_rtn = objc;

    return TCL_OK;
}

void Ttk_FreeTagList(void **taglist)
{
    if (taglist) 
	ckfree((ClientData)taglist);
}

