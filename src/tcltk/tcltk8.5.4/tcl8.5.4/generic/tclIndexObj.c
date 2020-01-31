/*
 * tclIndexObj.c --
 *
 *	This file implements objects of type "index". This object type is used
 *	to lookup a keyword in a table of valid values and cache the index of
 *	the matching entry.
 *
 * Copyright (c) 1997 Sun Microsystems, Inc.
 *
 * See the file "license.terms" for information on usage and redistribution of
 * this file, and for a DISCLAIMER OF ALL WARRANTIES.
 *
 * RCS: @(#) $Id: tclIndexObj.c,v 1.38 2007/12/13 15:23:18 dgp Exp $
 */

#include "tclInt.h"

/*
 * Prototypes for functions defined later in this file:
 */

static int		SetIndexFromAny(Tcl_Interp *interp, Tcl_Obj *objPtr);
static void		UpdateStringOfIndex(Tcl_Obj *objPtr);
static void		DupIndex(Tcl_Obj *srcPtr, Tcl_Obj *dupPtr);
static void		FreeIndex(Tcl_Obj *objPtr);

/*
 * The structure below defines the index Tcl object type by means of functions
 * that can be invoked by generic object code.
 */

static Tcl_ObjType indexType = {
    "index",				/* name */
    FreeIndex,				/* freeIntRepProc */
    DupIndex,				/* dupIntRepProc */
    UpdateStringOfIndex,		/* updateStringProc */
    SetIndexFromAny			/* setFromAnyProc */
};

/*
 * The definition of the internal representation of the "index" object; The
 * internalRep.otherValuePtr field of an object of "index" type will be a
 * pointer to one of these structures.
 *
 * Keep this structure declaration in sync with tclTestObj.c
 */

typedef struct {
    void *tablePtr;			/* Pointer to the table of strings */
    int offset;				/* Offset between table entries */
    int index;				/* Selected index into table. */
} IndexRep;

/*
 * The following macros greatly simplify moving through a table...
 */

#define STRING_AT(table, offset, index) \
	(*((const char *const *)(((char *)(table)) + ((offset) * (index)))))
#define NEXT_ENTRY(table, offset) \
	(&(STRING_AT(table, offset, 1)))
#define EXPAND_OF(indexRep) \
	STRING_AT((indexRep)->tablePtr, (indexRep)->offset, (indexRep)->index)

/*
 *----------------------------------------------------------------------
 *
 * Tcl_GetIndexFromObj --
 *
 *	This function looks up an object's value in a table of strings and
 *	returns the index of the matching string, if any.
 *
 * Results:
 *	If the value of objPtr is identical to or a unique abbreviation for
 *	one of the entries in objPtr, then the return value is TCL_OK and the
 *	index of the matching entry is stored at *indexPtr. If there isn't a
 *	proper match, then TCL_ERROR is returned and an error message is left
 *	in interp's result (unless interp is NULL). The msg argument is used
 *	in the error message; for example, if msg has the value "option" then
 *	the error message will say something flag 'bad option "foo": must be
 *	...'
 *
 * Side effects:
 *	The result of the lookup is cached as the internal rep of objPtr, so
 *	that repeated lookups can be done quickly.
 *
 *----------------------------------------------------------------------
 */

int
Tcl_GetIndexFromObj(
    Tcl_Interp *interp, 	/* Used for error reporting if not NULL. */
    Tcl_Obj *objPtr,		/* Object containing the string to lookup. */
    const char **tablePtr,	/* Array of strings to compare against the
				 * value of objPtr; last entry must be NULL
				 * and there must not be duplicate entries. */
    const char *msg,		/* Identifying word to use in error
				 * messages. */
    int flags,			/* 0 or TCL_EXACT */
    int *indexPtr)		/* Place to store resulting integer index. */
{

    /*
     * See if there is a valid cached result from a previous lookup (doing the
     * check here saves the overhead of calling Tcl_GetIndexFromObjStruct in
     * the common case where the result is cached).
     */

    if (objPtr->typePtr == &indexType) {
	IndexRep *indexRep = objPtr->internalRep.otherValuePtr;

	/*
	 * Here's hoping we don't get hit by unfortunate packing constraints
	 * on odd platforms like a Cray PVP...
	 */

	if (indexRep->tablePtr == (void *) tablePtr
		&& indexRep->offset == sizeof(char *)) {
	    *indexPtr = indexRep->index;
	    return TCL_OK;
	}
    }
    return Tcl_GetIndexFromObjStruct(interp, objPtr, tablePtr, sizeof(char *),
	    msg, flags, indexPtr);
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_GetIndexFromObjStruct --
 *
 *	This function looks up an object's value given a starting string and
 *	an offset for the amount of space between strings. This is useful when
 *	the strings are embedded in some other kind of array.
 *
 * Results:
 *	If the value of objPtr is identical to or a unique abbreviation for
 *	one of the entries in objPtr, then the return value is TCL_OK and the
 *	index of the matching entry is stored at *indexPtr. If there isn't a
 *	proper match, then TCL_ERROR is returned and an error message is left
 *	in interp's result (unless interp is NULL). The msg argument is used
 *	in the error message; for example, if msg has the value "option" then
 *	the error message will say something flag 'bad option "foo": must be
 *	...'
 *
 * Side effects:
 *	The result of the lookup is cached as the internal rep of objPtr, so
 *	that repeated lookups can be done quickly.
 *
 *----------------------------------------------------------------------
 */

int
Tcl_GetIndexFromObjStruct(
    Tcl_Interp *interp, 	/* Used for error reporting if not NULL. */
    Tcl_Obj *objPtr,		/* Object containing the string to lookup. */
    const void *tablePtr,	/* The first string in the table. The second
				 * string will be at this address plus the
				 * offset, the third plus the offset again,
				 * etc. The last entry must be NULL and there
				 * must not be duplicate entries. */
    int offset,			/* The number of bytes between entries */
    const char *msg,		/* Identifying word to use in error
				 * messages. */
    int flags,			/* 0 or TCL_EXACT */
    int *indexPtr)		/* Place to store resulting integer index. */
{
    int index, idx, numAbbrev;
    char *key, *p1;
    const char *p2;
    const char *const *entryPtr;
    Tcl_Obj *resultPtr;
    IndexRep *indexRep;

    /*
     * See if there is a valid cached result from a previous lookup.
     */

    if (objPtr->typePtr == &indexType) {
	indexRep = objPtr->internalRep.otherValuePtr;
	if (indexRep->tablePtr==tablePtr && indexRep->offset==offset) {
	    *indexPtr = indexRep->index;
	    return TCL_OK;
	}
    }

    /*
     * Lookup the value of the object in the table. Accept unique
     * abbreviations unless TCL_EXACT is set in flags.
     */

    key = TclGetString(objPtr);
    index = -1;
    numAbbrev = 0;

    /*
     * Scan the table looking for one of:
     *  - An exact match (always preferred)
     *  - A single abbreviation (allowed depending on flags)
     *  - Several abbreviations (never allowed, but overridden by exact match)
     */

    for (entryPtr = tablePtr, idx = 0; *entryPtr != NULL;
	    entryPtr = NEXT_ENTRY(entryPtr, offset), idx++) {
	for (p1 = key, p2 = *entryPtr; *p1 == *p2; p1++, p2++) {
	    if (*p1 == '\0') {
		index = idx;
		goto done;
	    }
	}
	if (*p1 == '\0') {
	    /*
	     * The value is an abbreviation for this entry. Continue checking
	     * other entries to make sure it's unique. If we get more than one
	     * unique abbreviation, keep searching to see if there is an exact
	     * match, but remember the number of unique abbreviations and
	     * don't allow either.
	     */

	    numAbbrev++;
	    index = idx;
	}
    }

    /*
     * Check if we were instructed to disallow abbreviations.
     */

    if ((flags & TCL_EXACT) || (key[0] == '\0') || (numAbbrev != 1)) {
	goto error;
    }

  done:
    /*
     * Cache the found representation. Note that we want to avoid allocating a
     * new internal-rep if at all possible since that is potentially a slow
     * operation.
     */

    if (objPtr->typePtr == &indexType) {
 	indexRep = objPtr->internalRep.otherValuePtr;
    } else {
	TclFreeIntRep(objPtr);
 	indexRep = (IndexRep *) ckalloc(sizeof(IndexRep));
 	objPtr->internalRep.otherValuePtr = indexRep;
 	objPtr->typePtr = &indexType;
    }
    indexRep->tablePtr = (void *) tablePtr;
    indexRep->offset = offset;
    indexRep->index = index;

    *indexPtr = index;
    return TCL_OK;

  error:
    if (interp != NULL) {
	/*
	 * Produce a fancy error message.
	 */

	int count;

	TclNewObj(resultPtr);
	Tcl_SetObjResult(interp, resultPtr);
	Tcl_AppendStringsToObj(resultPtr, (numAbbrev > 1) &&
		!(flags & TCL_EXACT) ? "ambiguous " : "bad ", msg, " \"", key,
		"\": must be ", STRING_AT(tablePtr, offset, 0), NULL);
	for (entryPtr = NEXT_ENTRY(tablePtr, offset), count = 0;
		*entryPtr != NULL;
		entryPtr = NEXT_ENTRY(entryPtr, offset), count++) {
	    if (*NEXT_ENTRY(entryPtr, offset) == NULL) {
		Tcl_AppendStringsToObj(resultPtr, ((count > 0) ? "," : ""),
			" or ", *entryPtr, NULL);
	    } else {
		Tcl_AppendStringsToObj(resultPtr, ", ", *entryPtr, NULL);
	    }
	}
	Tcl_SetErrorCode(interp, "TCL", "LOOKUP", "INDEX", msg, key, NULL);
    }
    return TCL_ERROR;
}

/*
 *----------------------------------------------------------------------
 *
 * SetIndexFromAny --
 *
 *	This function is called to convert a Tcl object to index internal
 *	form. However, this doesn't make sense (need to have a table of
 *	keywords in order to do the conversion) so the function always
 *	generates an error.
 *
 * Results:
 *	The return value is always TCL_ERROR, and an error message is left in
 *	interp's result if interp isn't NULL.
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */

static int
SetIndexFromAny(
    Tcl_Interp *interp,		/* Used for error reporting if not NULL. */
    register Tcl_Obj *objPtr)	/* The object to convert. */
{
    Tcl_SetObjResult(interp, Tcl_NewStringObj(
	    "can't convert value to index except via Tcl_GetIndexFromObj API",
	    -1));
    return TCL_ERROR;
}

/*
 *----------------------------------------------------------------------
 *
 * UpdateStringOfIndex --
 *
 *	This function is called to convert a Tcl object from index internal
 *	form to its string form. No abbreviation is ever generated.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	The string representation of the object is updated.
 *
 *----------------------------------------------------------------------
 */

static void
UpdateStringOfIndex(
    Tcl_Obj *objPtr)
{
    IndexRep *indexRep = objPtr->internalRep.otherValuePtr;
    register char *buf;
    register unsigned len;
    register const char *indexStr = EXPAND_OF(indexRep);

    len = strlen(indexStr);
    buf = (char *) ckalloc(len + 1);
    memcpy(buf, indexStr, len+1);
    objPtr->bytes = buf;
    objPtr->length = len;
}

/*
 *----------------------------------------------------------------------
 *
 * DupIndex --
 *
 *	This function is called to copy the internal rep of an index Tcl
 *	object from to another object.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	The internal representation of the target object is updated and the
 *	type is set.
 *
 *----------------------------------------------------------------------
 */

static void
DupIndex(
    Tcl_Obj *srcPtr,
    Tcl_Obj *dupPtr)
{
    IndexRep *srcIndexRep = srcPtr->internalRep.otherValuePtr;
    IndexRep *dupIndexRep = (IndexRep *) ckalloc(sizeof(IndexRep));

    memcpy(dupIndexRep, srcIndexRep, sizeof(IndexRep));
    dupPtr->internalRep.otherValuePtr = dupIndexRep;
    dupPtr->typePtr = &indexType;
}

/*
 *----------------------------------------------------------------------
 *
 * FreeIndex --
 *
 *	This function is called to delete the internal rep of an index Tcl
 *	object.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	The internal representation of the target object is deleted.
 *
 *----------------------------------------------------------------------
 */

static void
FreeIndex(
    Tcl_Obj *objPtr)
{
    ckfree((char *) objPtr->internalRep.otherValuePtr);
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_WrongNumArgs --
 *
 *	This function generates a "wrong # args" error message in an
 *	interpreter. It is used as a utility function by many command
 *	functions, including the function that implements procedures.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	An error message is generated in interp's result object to indicate
 *	that a command was invoked with the wrong number of arguments. The
 *	message has the form
 *		wrong # args: should be "foo bar additional stuff"
 *	where "foo" and "bar" are the initial objects in objv (objc determines
 *	how many of these are printed) and "additional stuff" is the contents
 *	of the message argument.
 *
 *	The message printed is modified somewhat if the command is wrapped
 *	inside an ensemble. In that case, the error message generated is
 *	rewritten in such a way that it appears to be generated from the
 *	user-visible command and not how that command is actually implemented,
 *	giving a better overall user experience.
 *
 *	Internally, the Tcl core may set the flag INTERP_ALTERNATE_WRONG_ARGS
 *	in the interpreter to generate complex multi-part messages by calling
 *	this function repeatedly. This allows the code that knows how to
 *	handle ensemble-related error messages to be kept here while still
 *	generating suitable error messages for commands like [read] and
 *	[socket]. Ideally, this would be done through an extra flags argument,
 *	but that wouldn't be source-compatible with the existing API and it's
 *	a fairly rare requirement anyway.
 *
 *----------------------------------------------------------------------
 */

void
Tcl_WrongNumArgs(
    Tcl_Interp *interp,		/* Current interpreter. */
    int objc,			/* Number of arguments to print from objv. */
    Tcl_Obj *const objv[],	/* Initial argument objects, which should be
				 * included in the error message. */
    const char *message)	/* Error message to print after the leading
				 * objects in objv. The message may be
				 * NULL. */
{
    Tcl_Obj *objPtr;
    int i, len, elemLen, flags;
    Interp *iPtr = (Interp *) interp;
    const char *elementStr;

    /*
     * [incr Tcl] does something fairly horrific when generating error
     * messages for its ensembles; it passes the whole set of ensemble
     * arguments as a list in the first argument. This means that this code
     * causes a problem in iTcl if it attempts to correctly quote all
     * arguments, which would be the correct thing to do. We work around this
     * nasty behaviour for now, and hope that we can remove it all in the
     * future...
     */

#ifndef AVOID_HACKS_FOR_ITCL
    int isFirst = 1;		/* Special flag used to inhibit the treating
				 * of the first word as a list element so the
				 * hacky way Itcl generates error messages for
				 * its ensembles will still work. [Bug
				 * 1066837] */
#   define MAY_QUOTE_WORD	(!isFirst)
#   define AFTER_FIRST_WORD	(isFirst = 0)
#else /* !AVOID_HACKS_FOR_ITCL */
#   define MAY_QUOTE_WORD	1
#   define AFTER_FIRST_WORD	(void) 0
#endif /* AVOID_HACKS_FOR_ITCL */

    TclNewObj(objPtr);
    if (iPtr->flags & INTERP_ALTERNATE_WRONG_ARGS) {
	Tcl_AppendObjToObj(objPtr, Tcl_GetObjResult(interp));
	Tcl_AppendToObj(objPtr, " or \"", -1);
    } else {
	Tcl_AppendToObj(objPtr, "wrong # args: should be \"", -1);
    }

    /*
     * Check to see if we are processing an ensemble implementation, and if so
     * rewrite the results in terms of how the ensemble was invoked.
     */

    if (iPtr->ensembleRewrite.sourceObjs != NULL) {
	int toSkip = iPtr->ensembleRewrite.numInsertedObjs;
	int toPrint = iPtr->ensembleRewrite.numRemovedObjs;
	Tcl_Obj *const *origObjv = iPtr->ensembleRewrite.sourceObjs;

	/*
	 * We only know how to do rewriting if all the replaced objects are
	 * actually arguments (in objv) to this function. Otherwise it just
	 * gets too complicated and we'd be better off just giving a slightly
	 * confusing error message...
	 */

	if (objc < toSkip) {
	    goto addNormalArgumentsToMessage;
	}

	/*
	 * Strip out the actual arguments that the ensemble inserted.
	 */

	objv += toSkip;
	objc -= toSkip;

	/*
	 * We assume no object is of index type.
	 */

	for (i=0 ; i<toPrint ; i++) {
	    /*
	     * Add the element, quoting it if necessary.
	     */

	    if (origObjv[i]->typePtr == &indexType) {
		register IndexRep *indexRep =
			origObjv[i]->internalRep.otherValuePtr;

		elementStr = EXPAND_OF(indexRep);
		elemLen = strlen(elementStr);
	    } else if (origObjv[i]->typePtr == &tclEnsembleCmdType) {
		register EnsembleCmdRep *ecrPtr =
			origObjv[i]->internalRep.otherValuePtr;

		elementStr = ecrPtr->fullSubcmdName;
		elemLen = strlen(elementStr);
	    } else {
		elementStr = TclGetStringFromObj(origObjv[i], &elemLen);
	    }
	    len = Tcl_ScanCountedElement(elementStr, elemLen, &flags);

	    if (MAY_QUOTE_WORD && len != elemLen) {
		char *quotedElementStr = TclStackAlloc(interp, (unsigned)len);

		len = Tcl_ConvertCountedElement(elementStr, elemLen,
			quotedElementStr, flags);
		Tcl_AppendToObj(objPtr, quotedElementStr, len);
		TclStackFree(interp, quotedElementStr);
	    } else {
		Tcl_AppendToObj(objPtr, elementStr, elemLen);
	    }

	    AFTER_FIRST_WORD;

	    /*
	     * Add a space if the word is not the last one (which has a
	     * moderately complex condition here).
	     */

	    if (i<toPrint-1 || objc!=0 || message!=NULL) {
		Tcl_AppendStringsToObj(objPtr, " ", NULL);
	    }
	}
    }

    /*
     * Now add the arguments (other than those rewritten) that the caller took
     * from its calling context.
     */

  addNormalArgumentsToMessage:
    for (i = 0; i < objc; i++) {
	/*
	 * If the object is an index type use the index table which allows for
	 * the correct error message even if the subcommand was abbreviated.
	 * Otherwise, just use the string rep.
	 */

	if (objv[i]->typePtr == &indexType) {
	    register IndexRep *indexRep = objv[i]->internalRep.otherValuePtr;

	    Tcl_AppendStringsToObj(objPtr, EXPAND_OF(indexRep), NULL);
	} else if (objv[i]->typePtr == &tclEnsembleCmdType) {
	    register EnsembleCmdRep *ecrPtr =
		    objv[i]->internalRep.otherValuePtr;

	    Tcl_AppendStringsToObj(objPtr, ecrPtr->fullSubcmdName, NULL);
	} else {
	    /*
	     * Quote the argument if it contains spaces (Bug 942757).
	     */

	    elementStr = TclGetStringFromObj(objv[i], &elemLen);
	    len = Tcl_ScanCountedElement(elementStr, elemLen, &flags);

	    if (MAY_QUOTE_WORD && len != elemLen) {
		char *quotedElementStr = TclStackAlloc(interp,(unsigned) len);

		len = Tcl_ConvertCountedElement(elementStr, elemLen,
			quotedElementStr, flags);
		Tcl_AppendToObj(objPtr, quotedElementStr, len);
		TclStackFree(interp, quotedElementStr);
	    } else {
		Tcl_AppendToObj(objPtr, elementStr, elemLen);
	    }
	}

	AFTER_FIRST_WORD;

	/*
	 * Append a space character (" ") if there is more text to follow
	 * (either another element from objv, or the message string).
	 */

	if (i<objc-1 || message!=NULL) {
	    Tcl_AppendStringsToObj(objPtr, " ", NULL);
	}
    }

    /*
     * Add any trailing message bits and set the resulting string as the
     * interpreter result. Caller is responsible for reporting this as an
     * actual error.
     */

    if (message != NULL) {
	Tcl_AppendStringsToObj(objPtr, message, NULL);
    }
    Tcl_AppendStringsToObj(objPtr, "\"", NULL);
    Tcl_SetObjResult(interp, objPtr);
#undef MAY_QUOTE_WORD
#undef AFTER_FIRST_WORD
}

/*
 * Local Variables:
 * mode: c
 * c-basic-offset: 4
 * fill-column: 78
 * End:
 */
