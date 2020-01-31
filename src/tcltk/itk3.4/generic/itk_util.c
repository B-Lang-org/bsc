/*
 * ------------------------------------------------------------------------
 *      PACKAGE:  [incr Tk]
 *  DESCRIPTION:  Building mega-widgets with [incr Tcl]
 *
 *  [incr Tk] provides a framework for building composite "mega-widgets"
 *  using [incr Tcl] classes.  It defines a set of base classes that are
 *  specialized to create all other widgets.
 *
 *  This part defines some utility procedures that are useful for
 *  [incr Tk].
 *
 * ========================================================================
 *  AUTHOR:  Michael J. McLennan
 *           Bell Labs Innovations for Lucent Technologies
 *           mmclennan@lucent.com
 *           http://www.tcltk.com/itcl
 *
 *     RCS:  $Id: itk_util.c,v 1.1 1998/07/27 18:45:25 stanton Exp $
 * ========================================================================
 *           Copyright (c) 1993-1998  Lucent Technologies, Inc.
 * ------------------------------------------------------------------------
 * See the file "license.terms" for information on usage and redistribution
 * of this file, and for a DISCLAIMER OF ALL WARRANTIES.
 */
#include "itk.h"


/*
 * ------------------------------------------------------------------------
 *  Itk_OptListInit()
 *
 *  Initializes an ordered option list, allocating a certain amount of
 *  memory for an initial option list.
 * ------------------------------------------------------------------------
 */
void
Itk_OptListInit(olist, options)
    ItkOptList *olist;       /* list to be initialized */
    Tcl_HashTable *options;  /* table containing the real option entries */
{
    olist->options = options;
    olist->len = 0;
    olist->max = 10;
    olist->list = (Tcl_HashEntry**)ckalloc(
        (unsigned)(olist->max*sizeof(Tcl_HashEntry*))
    );
}


/*
 * ------------------------------------------------------------------------
 *  Itk_OptListFree()
 *
 *  Frees an ordered option list created by Itk_OptListInit().
 *  This only frees the memory associated with the list, not the
 *  list itself.
 * ------------------------------------------------------------------------
 */
void
Itk_OptListFree(olist)
    ItkOptList *olist;     /* list to be freed */
{
    ckfree((char*)olist->list);
    olist->len = olist->max = 0;
}


/*
 * ------------------------------------------------------------------------
 *  Itk_OptListAdd()
 *
 *  Adds the hash table entry for an option like '-background' to an
 *  ordered list of options.  The list is kept in alphabetical order,
 *  so that it can be searched quickly and printed out in order.
 * ------------------------------------------------------------------------
 */
void
Itk_OptListAdd(olist, entry)
    ItkOptList *olist;     /* ordered list */
    Tcl_HashEntry *entry;  /* entry to be added to the list */
{
    int i, first, last, cmp, pos, size;
    Tcl_HashEntry** newOrder;
    char *swname, *optname;

    /*
     *  Make sure that the option list is big enough.  Resize
     *  if needed.
     */
    if (olist->len >= olist->max) {
        size = olist->max*sizeof(Tcl_HashEntry*);
        newOrder = (Tcl_HashEntry**)ckalloc((unsigned)2*size);
        memcpy((VOID*)newOrder, (VOID*)olist->list, (size_t)size);
        ckfree((char*)olist->list);

        olist->list = newOrder;
        olist->max *= 2;
    }

    /*
     *  Perform a binary search to find the option switch quickly.
     */
    first = 0;
    last  = olist->len-1;
    swname = Tcl_GetHashKey(olist->options, entry) + 1;

    while (last >= first) {
        pos = (first+last)/2;
        optname = Tcl_GetHashKey(olist->options, olist->list[pos]) + 1;
        if (*swname == *optname) {
            cmp = strcmp(swname, optname);
            if (cmp == 0) {
                break;    /* found it! */
            }
        }
        else if (*swname < *optname) {
            cmp = -1;
        }
        else {
            cmp = 1;
        }

        if (cmp > 0)
            first = pos+1;
        else
            last = pos-1;
    }

    /*
     *  If a matching entry was not found, then insert one.
     */
    if (last < first) {
        pos = first;

        for (i=olist->len; i > pos; i--) {
            olist->list[i] = olist->list[i-1];
        }
        olist->list[pos] = entry;
        olist->len++;
    }
}


/*
 * ------------------------------------------------------------------------
 *  Itk_OptListRemove()
 *
 *  Removes a hash table entry from an ordered list of options.
 *  This negates the action of Itk_OptionListAdd(), and is usually
 *  called when an option is completely removed from a mega-widget.
 *  This should be called before the entry is removed from the
 *  real option table.
 * ------------------------------------------------------------------------
 */
void
Itk_OptListRemove(olist, entry)
    ItkOptList *olist;     /* ordered list */
    Tcl_HashEntry *entry;  /* entry to be removed from the list */
{
    int pos = 0;
    int i, first, last, cmp;
    char *swname, *optname;

    first = 0;
    last  = olist->len-1;
    swname = Tcl_GetHashKey(olist->options, entry) + 1;

    while (last >= first) {
        pos = (first+last)/2;
        optname = Tcl_GetHashKey(olist->options, olist->list[pos]) + 1;
        if (*swname == *optname) {
            cmp = strcmp(swname, optname);
            if (cmp == 0) {
                break;    /* found it! */
            }
        }
        else if (*swname < *optname) {
            cmp = -1;
        }
        else {
            cmp = 1;
        }

        if (cmp > 0)
            first = pos+1;
        else
            last = pos-1;
    }

    /*
     *  If a matching entry was found, then remove it.
     */
    if (last >= first) {
        olist->len--;
        for (i=pos; i < olist->len; i++) {
            olist->list[i] = olist->list[i+1];
        }
    }
}
