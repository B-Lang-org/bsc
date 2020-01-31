/*
 * tclUtil.c --
 *
 *	This file contains utility functions that are used by many Tcl
 *	commands.
 *
 * Copyright (c) 1987-1993 The Regents of the University of California.
 * Copyright (c) 1994-1998 Sun Microsystems, Inc.
 * Copyright (c) 2001 by Kevin B. Kenny. All rights reserved.
 *
 * See the file "license.terms" for information on usage and redistribution of
 * this file, and for a DISCLAIMER OF ALL WARRANTIES.
 *
 * RCS: @(#) $Id: tclUtil.c,v 1.97 2008/02/26 20:18:14 hobbs Exp $
 */

#include "tclInt.h"
#include <float.h>
#include <math.h>

/*
 * The absolute pathname of the executable in which this Tcl library is
 * running.
 */

static ProcessGlobalValue executableName = {
    0, 0, NULL, NULL, NULL, NULL, NULL
};

/*
 * The following values are used in the flags returned by Tcl_ScanElement and
 * used by Tcl_ConvertElement. The values TCL_DONT_USE_BRACES and
 * TCL_DONT_QUOTE_HASH are defined in tcl.h; make sure neither value overlaps
 * with any of the values below.
 *
 * TCL_DONT_USE_BRACES -	1 means the string mustn't be enclosed in
 *				braces (e.g. it contains unmatched braces, or
 *				ends in a backslash character, or user just
 *				doesn't want braces); handle all special
 *				characters by adding backslashes.
 * USE_BRACES -			1 means the string contains a special
 *				character that can be handled simply by
 *				enclosing the entire argument in braces.
 * BRACES_UNMATCHED -		1 means that braces aren't properly matched in
 *				the argument.
 * TCL_DONT_QUOTE_HASH -	1 means the caller insists that a leading hash
 * 				character ('#') should *not* be quoted. This
 * 				is appropriate when the caller can guarantee
 * 				the element is not the first element of a
 * 				list, so [eval] cannot mis-parse the element
 * 				as a comment.
 */

#define USE_BRACES		2
#define BRACES_UNMATCHED	4

/*
 * The following key is used by Tcl_PrintDouble and TclPrecTraceProc to
 * access the precision to be used for double formatting.
 */

static Tcl_ThreadDataKey precisionKey;

/*
 * Prototypes for functions defined later in this file.
 */

static void		ClearHash(Tcl_HashTable *tablePtr);
static void		FreeProcessGlobalValue(ClientData clientData);
static void		FreeThreadHash(ClientData clientData);
static Tcl_HashTable *	GetThreadHash(Tcl_ThreadDataKey *keyPtr);
static int		SetEndOffsetFromAny(Tcl_Interp* interp,
			    Tcl_Obj* objPtr);
static void		UpdateStringOfEndOffset(Tcl_Obj* objPtr);

/*
 * The following is the Tcl object type definition for an object that
 * represents a list index in the form, "end-offset". It is used as a
 * performance optimization in TclGetIntForIndex. The internal rep is an
 * integer, so no memory management is required for it.
 */

Tcl_ObjType tclEndOffsetType = {
    "end-offset",			/* name */
    NULL,				/* freeIntRepProc */
    NULL,				/* dupIntRepProc */
    UpdateStringOfEndOffset,		/* updateStringProc */
    SetEndOffsetFromAny
};

/*
 *----------------------------------------------------------------------
 *
 * TclFindElement --
 *
 *	Given a pointer into a Tcl list, locate the first (or next) element in
 *	the list.
 *
 * Results:
 *	The return value is normally TCL_OK, which means that the element was
 *	successfully located. If TCL_ERROR is returned it means that list
 *	didn't have proper list structure; the interp's result contains a more
 *	detailed error message.
 *
 *	If TCL_OK is returned, then *elementPtr will be set to point to the
 *	first element of list, and *nextPtr will be set to point to the
 *	character just after any white space following the last character
 *	that's part of the element. If this is the last argument in the list,
 *	then *nextPtr will point just after the last character in the list
 *	(i.e., at the character at list+listLength). If sizePtr is non-NULL,
 *	*sizePtr is filled in with the number of characters in the element. If
 *	the element is in braces, then *elementPtr will point to the character
 *	after the opening brace and *sizePtr will not include either of the
 *	braces. If there isn't an element in the list, *sizePtr will be zero,
 *	and both *elementPtr and *termPtr will point just after the last
 *	character in the list. Note: this function does NOT collapse backslash
 *	sequences.
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */

int
TclFindElement(
    Tcl_Interp *interp,		/* Interpreter to use for error reporting. If
				 * NULL, then no error message is left after
				 * errors. */
    CONST char *list,		/* Points to the first byte of a string
				 * containing a Tcl list with zero or more
				 * elements (possibly in braces). */
    int listLength,		/* Number of bytes in the list's string. */
    CONST char **elementPtr,	/* Where to put address of first significant
				 * character in first element of list. */
    CONST char **nextPtr,	/* Fill in with location of character just
				 * after all white space following end of
				 * argument (next arg or end of list). */
    int *sizePtr,		/* If non-zero, fill in with size of
				 * element. */
    int *bracePtr)		/* If non-zero, fill in with non-zero/zero to
				 * indicate that arg was/wasn't in braces. */
{
    CONST char *p = list;
    CONST char *elemStart;	/* Points to first byte of first element. */
    CONST char *limit;		/* Points just after list's last byte. */
    int openBraces = 0;		/* Brace nesting level during parse. */
    int inQuotes = 0;
    int size = 0;		/* lint. */
    int numChars;
    CONST char *p2;

    /*
     * Skim off leading white space and check for an opening brace or quote.
     * We treat embedded NULLs in the list as bytes belonging to a list
     * element.
     */

    limit = (list + listLength);
    while ((p < limit) && (isspace(UCHAR(*p)))) { /* INTL: ISO space. */
	p++;
    }
    if (p == limit) {		/* no element found */
	elemStart = limit;
	goto done;
    }

    if (*p == '{') {
	openBraces = 1;
	p++;
    } else if (*p == '"') {
	inQuotes = 1;
	p++;
    }
    elemStart = p;
    if (bracePtr != 0) {
	*bracePtr = openBraces;
    }

    /*
     * Find element's end (a space, close brace, or the end of the string).
     */

    while (p < limit) {
	switch (*p) {
	    /*
	     * Open brace: don't treat specially unless the element is in
	     * braces. In this case, keep a nesting count.
	     */

	case '{':
	    if (openBraces != 0) {
		openBraces++;
	    }
	    break;

	    /*
	     * Close brace: if element is in braces, keep nesting count and
	     * quit when the last close brace is seen.
	     */

	case '}':
	    if (openBraces > 1) {
		openBraces--;
	    } else if (openBraces == 1) {
		size = (p - elemStart);
		p++;
		if ((p >= limit)
			|| isspace(UCHAR(*p))) {	/* INTL: ISO space. */
		    goto done;
		}

		/*
		 * Garbage after the closing brace; return an error.
		 */

		if (interp != NULL) {
		    p2 = p;
		    while ((p2 < limit)
			    && (!isspace(UCHAR(*p2)))	/* INTL: ISO space. */
			    && (p2 < p+20)) {
			p2++;
		    }
		    Tcl_SetObjResult(interp, Tcl_ObjPrintf(
			    "list element in braces followed by \"%.*s\" "
			    "instead of space", (int) (p2-p), p));
		}
		return TCL_ERROR;
	    }
	    break;

	    /*
	     * Backslash: skip over everything up to the end of the backslash
	     * sequence.
	     */

	case '\\':
	    Tcl_UtfBackslash(p, &numChars, NULL);
	    p += (numChars - 1);
	    break;

	    /*
	     * Space: ignore if element is in braces or quotes; otherwise
	     * terminate element.
	     */

	case ' ':
	case '\f':
	case '\n':
	case '\r':
	case '\t':
	case '\v':
	    if ((openBraces == 0) && !inQuotes) {
		size = (p - elemStart);
		goto done;
	    }
	    break;

	    /*
	     * Double-quote: if element is in quotes then terminate it.
	     */

	case '"':
	    if (inQuotes) {
		size = (p - elemStart);
		p++;
		if ((p >= limit)
			|| isspace(UCHAR(*p))) {	/* INTL: ISO space */
		    goto done;
		}

		/*
		 * Garbage after the closing quote; return an error.
		 */

		if (interp != NULL) {
		    p2 = p;
		    while ((p2 < limit)
			    && (!isspace(UCHAR(*p2)))	/* INTL: ISO space */
			    && (p2 < p+20)) {
			p2++;
		    }
		    Tcl_SetObjResult(interp, Tcl_ObjPrintf(
			    "list element in quotes followed by \"%.*s\" "
			    "instead of space", (int) (p2-p), p));
		}
		return TCL_ERROR;
	    }
	    break;
	}
	p++;
    }

    /*
     * End of list: terminate element.
     */

    if (p == limit) {
	if (openBraces != 0) {
	    if (interp != NULL) {
		Tcl_SetResult(interp, "unmatched open brace in list",
			TCL_STATIC);
	    }
	    return TCL_ERROR;
	} else if (inQuotes) {
	    if (interp != NULL) {
		Tcl_SetResult(interp, "unmatched open quote in list",
			TCL_STATIC);
	    }
	    return TCL_ERROR;
	}
	size = (p - elemStart);
    }

  done:
    while ((p < limit) && (isspace(UCHAR(*p)))) { /* INTL: ISO space. */
	p++;
    }
    *elementPtr = elemStart;
    *nextPtr = p;
    if (sizePtr != 0) {
	*sizePtr = size;
    }
    return TCL_OK;
}

/*
 *----------------------------------------------------------------------
 *
 * TclCopyAndCollapse --
 *
 *	Copy a string and eliminate any backslashes that aren't in braces.
 *
 * Results:
 *	Count characters get copied from src to dst. Along the way, if
 *	backslash sequences are found outside braces, the backslashes are
 *	eliminated in the copy. After scanning count chars from source, a null
 *	character is placed at the end of dst. Returns the number of
 *	characters that got copied.
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */

int
TclCopyAndCollapse(
    int count,			/* Number of characters to copy from src. */
    CONST char *src,		/* Copy from here... */
    char *dst)			/* ... to here. */
{
    register char c;
    int numRead;
    int newCount = 0;
    int backslashCount;

    for (c = *src;  count > 0;  src++, c = *src, count--) {
	if (c == '\\') {
	    backslashCount = Tcl_UtfBackslash(src, &numRead, dst);
	    dst += backslashCount;
	    newCount += backslashCount;
	    src += numRead-1;
	    count -= numRead-1;
	} else {
	    *dst = c;
	    dst++;
	    newCount++;
	}
    }
    *dst = 0;
    return newCount;
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_SplitList --
 *
 *	Splits a list up into its constituent fields.
 *
 * Results
 *	The return value is normally TCL_OK, which means that the list was
 *	successfully split up. If TCL_ERROR is returned, it means that "list"
 *	didn't have proper list structure; the interp's result will contain a
 *	more detailed error message.
 *
 *	*argvPtr will be filled in with the address of an array whose elements
 *	point to the elements of list, in order. *argcPtr will get filled in
 *	with the number of valid elements in the array. A single block of
 *	memory is dynamically allocated to hold both the argv array and a copy
 *	of the list (with backslashes and braces removed in the standard way).
 *	The caller must eventually free this memory by calling free() on
 *	*argvPtr. Note: *argvPtr and *argcPtr are only modified if the
 *	function returns normally.
 *
 * Side effects:
 *	Memory is allocated.
 *
 *----------------------------------------------------------------------
 */

int
Tcl_SplitList(
    Tcl_Interp *interp,		/* Interpreter to use for error reporting. If
				 * NULL, no error message is left. */
    CONST char *list,		/* Pointer to string with list structure. */
    int *argcPtr,		/* Pointer to location to fill in with the
				 * number of elements in the list. */
    CONST char ***argvPtr)	/* Pointer to place to store pointer to array
				 * of pointers to list elements. */
{
    CONST char **argv, *l, *element;
    char *p;
    int length, size, i, result, elSize, brace;

    /*
     * Figure out how much space to allocate. There must be enough space for
     * both the array of pointers and also for a copy of the list. To estimate
     * the number of pointers needed, count the number of space characters in
     * the list.
     */

    for (size = 2, l = list; *l != 0; l++) {
	if (isspace(UCHAR(*l))) {			/* INTL: ISO space. */
	    size++;

	    /*
	     * Consecutive space can only count as a single list delimiter.
	     */

	    while (1) {
		char next = *(l + 1);

		if (next == '\0') {
		    break;
		}
		++l;
		if (isspace(UCHAR(next))) {		/* INTL: ISO space. */
		    continue;
		}
		break;
	    }
	}
    }
    length = l - list;
    argv = (CONST char **) ckalloc((unsigned)
	    ((size * sizeof(char *)) + length + 1));
    for (i = 0, p = ((char *) argv) + size*sizeof(char *);
	    *list != 0;  i++) {
	CONST char *prevList = list;

	result = TclFindElement(interp, list, length, &element, &list,
		&elSize, &brace);
	length -= (list - prevList);
	if (result != TCL_OK) {
	    ckfree((char *) argv);
	    return result;
	}
	if (*element == 0) {
	    break;
	}
	if (i >= size) {
	    ckfree((char *) argv);
	    if (interp != NULL) {
		Tcl_SetResult(interp, "internal error in Tcl_SplitList",
			TCL_STATIC);
	    }
	    return TCL_ERROR;
	}
	argv[i] = p;
	if (brace) {
	    memcpy(p, element, (size_t) elSize);
	    p += elSize;
	    *p = 0;
	    p++;
	} else {
	    TclCopyAndCollapse(elSize, element, p);
	    p += elSize+1;
	}
    }

    argv[i] = NULL;
    *argvPtr = argv;
    *argcPtr = i;
    return TCL_OK;
}

/*
 *----------------------------------------------------------------------
 *
 * TclMarkList --
 *
 *	Marks the locations within a string where list elements start and
 *	computes where they end.
 *
 * Results
 *	The return value is normally TCL_OK, which means that the list was
 *	successfully split up. If TCL_ERROR is returned, it means that "list"
 *	didn't have proper list structure; the interp's result will contain a
 *	more detailed error message.
 *
 *	*argvPtr will be filled in with the address of an array whose elements
 *	point to the places where the elements of list start, in order.
 *	*argcPtr will get filled in with the number of valid elements in the
 *	array. *argszPtr will get filled in with the address of an array whose
 *	elements are the lengths of the elements of the list, in order.
 *	Note: *argvPtr, *argcPtr and *argszPtr are only modified if the
 *	function returns normally.
 *
 * Side effects:
 *	Memory is allocated.
 *
 *----------------------------------------------------------------------
 */

int
TclMarkList(
    Tcl_Interp *interp,		/* Interpreter to use for error reporting. If
				 * NULL, no error message is left. */
    CONST char *list,		/* Pointer to string with list structure. */
    CONST char *end,		/* Pointer to first char after the list. */
    int *argcPtr,		/* Pointer to location to fill in with the
				 * number of elements in the list. */
    CONST int **argszPtr,	/* Pointer to place to store length of list
				 * elements. */
    CONST char ***argvPtr)	/* Pointer to place to store pointer to array
				 * of pointers to list elements. */
{
    CONST char **argv, *l, *element;
    int *argn, length, size, i, result, elSize, brace;

    /*
     * Figure out how much space to allocate. There must be enough space for
     * the array of pointers and lengths. To estimate the number of pointers
     * needed, count the number of whitespace characters in the list.
     */

    for (size=2, l=list ; l!=end ; l++) {
	if (isspace(UCHAR(*l))) {			/* INTL: ISO space. */
	    size++;

	    /*
	     * Consecutive space can only count as a single list delimiter.
	     */

	    while (1) {
		char next = *(l + 1);

		if ((l+1) == end) {
		    break;
		}
		++l;
		if (isspace(UCHAR(next))) {		/* INTL: ISO space. */
		    continue;
		}
		break;
	    }
	}
    }
    length = l - list;
    argv = (CONST char **) ckalloc((unsigned) size * sizeof(char *));
    argn = (int *) ckalloc((unsigned) size * sizeof(int *));

    for (i = 0; list != end;  i++) {
	CONST char *prevList = list;

	result = TclFindElement(interp, list, length, &element, &list,
		&elSize, &brace);
	length -= (list - prevList);
	if (result != TCL_OK) {
	    ckfree((char *) argv);
	    ckfree((char *) argn);
	    return result;
	}
	if (*element == 0) {
	    break;
	}
	if (i >= size) {
	    ckfree((char *) argv);
	    ckfree((char *) argn);
	    if (interp != NULL) {
		Tcl_SetResult(interp, "internal error in TclMarkList",
			TCL_STATIC);
	    }
	    return TCL_ERROR;
	}
	argv[i] = element;
	argn[i] = elSize;
    }

    argv[i] = NULL;
    argn[i] = 0;
    *argvPtr = argv;
    *argszPtr = argn;
    *argcPtr = i;
    return TCL_OK;
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_ScanElement --
 *
 *	This function is a companion function to Tcl_ConvertElement. It scans
 *	a string to see what needs to be done to it (e.g. add backslashes or
 *	enclosing braces) to make the string into a valid Tcl list element.
 *
 * Results:
 *	The return value is an overestimate of the number of characters that
 *	will be needed by Tcl_ConvertElement to produce a valid list element
 *	from string. The word at *flagPtr is filled in with a value needed by
 *	Tcl_ConvertElement when doing the actual conversion.
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */

int
Tcl_ScanElement(
    register CONST char *string,/* String to convert to list element. */
    register int *flagPtr)	/* Where to store information to guide
				 * Tcl_ConvertCountedElement. */
{
    return Tcl_ScanCountedElement(string, -1, flagPtr);
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_ScanCountedElement --
 *
 *	This function is a companion function to Tcl_ConvertCountedElement. It
 *	scans a string to see what needs to be done to it (e.g. add
 *	backslashes or enclosing braces) to make the string into a valid Tcl
 *	list element. If length is -1, then the string is scanned up to the
 *	first null byte.
 *
 * Results:
 *	The return value is an overestimate of the number of characters that
 *	will be needed by Tcl_ConvertCountedElement to produce a valid list
 *	element from string. The word at *flagPtr is filled in with a value
 *	needed by Tcl_ConvertCountedElement when doing the actual conversion.
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */

int
Tcl_ScanCountedElement(
    CONST char *string,		/* String to convert to Tcl list element. */
    int length,			/* Number of bytes in string, or -1. */
    int *flagPtr)		/* Where to store information to guide
				 * Tcl_ConvertElement. */
{
    int flags, nestingLevel;
    register CONST char *p, *lastChar;

    /*
     * This function and Tcl_ConvertElement together do two things:
     *
     * 1. They produce a proper list, one that will yield back the argument
     *	  strings when evaluated or when disassembled with Tcl_SplitList. This
     *	  is the most important thing.
     *
     * 2. They try to produce legible output, which means minimizing the use
     *	  of backslashes (using braces instead). However, there are some
     *	  situations where backslashes must be used (e.g. an element like
     *	  "{abc": the leading brace will have to be backslashed. For each
     *	  element, one of three things must be done:
     *
     * 	  (a) Use the element as-is (it doesn't contain any special
     *	      characters). This is the most desirable option.
     *
     *	  (b) Enclose the element in braces, but leave the contents alone.
     *	      This happens if the element contains embedded space, or if it
     *	      contains characters with special interpretation ($, [, ;, or \),
     *	      or if it starts with a brace or double-quote, or if there are no
     *	      characters in the element.
     *
     *	  (c) Don't enclose the element in braces, but add backslashes to
     *	      prevent special interpretation of special characters. This is a
     *	      last resort used when the argument would normally fall under
     *	      case (b) but contains unmatched braces. It also occurs if the
     *	      last character of the argument is a backslash or if the element
     *	      contains a backslash followed by newline.
     *
     * The function figures out how many bytes will be needed to store the
     * result (actually, it overestimates). It also collects information about
     * the element in the form of a flags word.
     *
     * Note: list elements produced by this function and
     * Tcl_ConvertCountedElement must have the property that they can be
     * enclosing in curly braces to make sub-lists. This means, for example,
     * that we must not leave unmatched curly braces in the resulting list
     * element. This property is necessary in order for functions like
     * Tcl_DStringStartSublist to work.
     */

    nestingLevel = 0;
    flags = 0;
    if (string == NULL) {
	string = "";
    }
    if (length == -1) {
	length = strlen(string);
    }
    lastChar = string + length;
    p = string;
    if ((p == lastChar) || (*p == '{') || (*p == '"')) {
	flags |= USE_BRACES;
    }
    for (; p < lastChar; p++) {
	switch (*p) {
	case '{':
	    nestingLevel++;
	    break;
	case '}':
	    nestingLevel--;
	    if (nestingLevel < 0) {
		flags |= TCL_DONT_USE_BRACES|BRACES_UNMATCHED;
	    }
	    break;
	case '[':
	case '$':
	case ';':
	case ' ':
	case '\f':
	case '\n':
	case '\r':
	case '\t':
	case '\v':
	    flags |= USE_BRACES;
	    break;
	case '\\':
	    if ((p+1 == lastChar) || (p[1] == '\n')) {
		flags = TCL_DONT_USE_BRACES | BRACES_UNMATCHED;
	    } else {
		int size;

		Tcl_UtfBackslash(p, &size, NULL);
		p += size-1;
		flags |= USE_BRACES;
	    }
	    break;
	}
    }
    if (nestingLevel != 0) {
	flags = TCL_DONT_USE_BRACES | BRACES_UNMATCHED;
    }
    *flagPtr = flags;

    /*
     * Allow enough space to backslash every character plus leave two spaces
     * for braces.
     */

    return 2*(p-string) + 2;
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_ConvertElement --
 *
 *	This is a companion function to Tcl_ScanElement. Given the information
 *	produced by Tcl_ScanElement, this function converts a string to a list
 *	element equal to that string.
 *
 * Results:
 *	Information is copied to *dst in the form of a list element identical
 *	to src (i.e. if Tcl_SplitList is applied to dst it will produce a
 *	string identical to src). The return value is a count of the number of
 *	characters copied (not including the terminating NULL character).
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */

int
Tcl_ConvertElement(
    register CONST char *src,	/* Source information for list element. */
    register char *dst,		/* Place to put list-ified element. */
    register int flags)		/* Flags produced by Tcl_ScanElement. */
{
    return Tcl_ConvertCountedElement(src, -1, dst, flags);
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_ConvertCountedElement --
 *
 *	This is a companion function to Tcl_ScanCountedElement. Given the
 *	information produced by Tcl_ScanCountedElement, this function converts
 *	a string to a list element equal to that string.
 *
 * Results:
 *	Information is copied to *dst in the form of a list element identical
 *	to src (i.e. if Tcl_SplitList is applied to dst it will produce a
 *	string identical to src). The return value is a count of the number of
 *	characters copied (not including the terminating NULL character).
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */

int
Tcl_ConvertCountedElement(
    register CONST char *src,	/* Source information for list element. */
    int length,			/* Number of bytes in src, or -1. */
    char *dst,			/* Place to put list-ified element. */
    int flags)			/* Flags produced by Tcl_ScanElement. */
{
    register char *p = dst;
    register CONST char *lastChar;

    /*
     * See the comment block at the beginning of the Tcl_ScanElement code for
     * details of how this works.
     */

    if (src && length == -1) {
	length = strlen(src);
    }
    if ((src == NULL) || (length == 0)) {
	p[0] = '{';
	p[1] = '}';
	p[2] = 0;
	return 2;
    }
    lastChar = src + length;
    if ((*src == '#') && !(flags & TCL_DONT_QUOTE_HASH)) {
	flags |= USE_BRACES;
    }
    if ((flags & USE_BRACES) && !(flags & TCL_DONT_USE_BRACES)) {
	*p = '{';
	p++;
	for (; src != lastChar; src++, p++) {
	    *p = *src;
	}
	*p = '}';
	p++;
    } else {
	if (*src == '{') {
	    /*
	     * Can't have a leading brace unless the whole element is enclosed
	     * in braces. Add a backslash before the brace. Furthermore, this
	     * may destroy the balance between open and close braces, so set
	     * BRACES_UNMATCHED.
	     */

	    p[0] = '\\';
	    p[1] = '{';
	    p += 2;
	    src++;
	    flags |= BRACES_UNMATCHED;
	} else if ((*src == '#') && !(flags & TCL_DONT_QUOTE_HASH)) {
	    /*
	     * Leading '#' could be seen by [eval] as the start of a comment,
	     * if on the first element of a list, so quote it.
	     */

	    p[0] = '\\';
	    p[1] = '#';
	    p += 2;
	    src++;
	}
	for (; src != lastChar; src++) {
	    switch (*src) {
	    case ']':
	    case '[':
	    case '$':
	    case ';':
	    case ' ':
	    case '\\':
	    case '"':
		*p = '\\';
		p++;
		break;
	    case '{':
	    case '}':
		/*
		 * It may not seem necessary to backslash braces, but it is.
		 * The reason for this is that the resulting list element may
		 * actually be an element of a sub-list enclosed in braces
		 * (e.g. if Tcl_DStringStartSublist has been invoked), so
		 * there may be a brace mismatch if the braces aren't
		 * backslashed.
		 */

		if (flags & BRACES_UNMATCHED) {
		    *p = '\\';
		    p++;
		}
		break;
	    case '\f':
		*p = '\\';
		p++;
		*p = 'f';
		p++;
		continue;
	    case '\n':
		*p = '\\';
		p++;
		*p = 'n';
		p++;
		continue;
	    case '\r':
		*p = '\\';
		p++;
		*p = 'r';
		p++;
		continue;
	    case '\t':
		*p = '\\';
		p++;
		*p = 't';
		p++;
		continue;
	    case '\v':
		*p = '\\';
		p++;
		*p = 'v';
		p++;
		continue;
	    }
	    *p = *src;
	    p++;
	}
    }
    *p = '\0';
    return p-dst;
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_Merge --
 *
 *	Given a collection of strings, merge them together into a single
 *	string that has proper Tcl list structured (i.e. Tcl_SplitList may be
 *	used to retrieve strings equal to the original elements, and Tcl_Eval
 *	will parse the string back into its original elements).
 *
 * Results:
 *	The return value is the address of a dynamically-allocated string
 *	containing the merged list.
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */

char *
Tcl_Merge(
    int argc,			/* How many strings to merge. */
    CONST char * CONST *argv)	/* Array of string values. */
{
#   define LOCAL_SIZE 20
    int localFlags[LOCAL_SIZE], *flagPtr;
    int numChars;
    char *result;
    char *dst;
    int i;

    /*
     * Pass 1: estimate space, gather flags.
     */

    if (argc <= LOCAL_SIZE) {
	flagPtr = localFlags;
    } else {
	flagPtr = (int *) ckalloc((unsigned) argc*sizeof(int));
    }
    numChars = 1;
    for (i = 0; i < argc; i++) {
	numChars += Tcl_ScanElement(argv[i], &flagPtr[i]) + 1;
    }

    /*
     * Pass two: copy into the result area.
     */

    result = (char *) ckalloc((unsigned) numChars);
    dst = result;
    for (i = 0; i < argc; i++) {
	numChars = Tcl_ConvertElement(argv[i], dst,
		flagPtr[i] | (i==0 ? 0 : TCL_DONT_QUOTE_HASH));
	dst += numChars;
	*dst = ' ';
	dst++;
    }
    if (dst == result) {
	*dst = 0;
    } else {
	dst[-1] = 0;
    }

    if (flagPtr != localFlags) {
	ckfree((char *) flagPtr);
    }
    return result;
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_Backslash --
 *
 *	Figure out how to handle a backslash sequence.
 *
 * Results:
 *	The return value is the character that should be substituted in place
 *	of the backslash sequence that starts at src. If readPtr isn't NULL
 *	then it is filled in with a count of the number of characters in the
 *	backslash sequence.
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */

char
Tcl_Backslash(
    CONST char *src,		/* Points to the backslash character of a
				 * backslash sequence. */
    int *readPtr)		/* Fill in with number of characters read from
				 * src, unless NULL. */
{
    char buf[TCL_UTF_MAX];
    Tcl_UniChar ch;

    Tcl_UtfBackslash(src, readPtr, buf);
    TclUtfToUniChar(buf, &ch);
    return (char) ch;
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_Concat --
 *
 *	Concatenate a set of strings into a single large string.
 *
 * Results:
 *	The return value is dynamically-allocated string containing a
 *	concatenation of all the strings in argv, with spaces between the
 *	original argv elements.
 *
 * Side effects:
 *	Memory is allocated for the result; the caller is responsible for
 *	freeing the memory.
 *
 *----------------------------------------------------------------------
 */

char *
Tcl_Concat(
    int argc,			/* Number of strings to concatenate. */
    CONST char * CONST *argv)	/* Array of strings to concatenate. */
{
    int totalSize, i;
    char *p;
    char *result;

    for (totalSize = 1, i = 0; i < argc; i++) {
	totalSize += strlen(argv[i]) + 1;
    }
    result = (char *) ckalloc((unsigned) totalSize);
    if (argc == 0) {
	*result = '\0';
	return result;
    }
    for (p = result, i = 0; i < argc; i++) {
	CONST char *element;
	int length;

	/*
	 * Clip white space off the front and back of the string to generate a
	 * neater result, and ignore any empty elements.
	 */

	element = argv[i];
	while (isspace(UCHAR(*element))) { /* INTL: ISO space. */
	    element++;
	}
	for (length = strlen(element);
		(length > 0)
		&& (isspace(UCHAR(element[length-1]))) /* INTL: ISO space. */
		&& ((length < 2) || (element[length-2] != '\\'));
		length--) {
	    /* Null loop body. */
	}
	if (length == 0) {
	    continue;
	}
	memcpy(p, element, (size_t) length);
	p += length;
	*p = ' ';
	p++;
    }
    if (p != result) {
	p[-1] = 0;
    } else {
	*p = 0;
    }
    return result;
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_ConcatObj --
 *
 *	Concatenate the strings from a set of objects into a single string
 *	object with spaces between the original strings.
 *
 * Results:
 *	The return value is a new string object containing a concatenation of
 *	the strings in objv. Its ref count is zero.
 *
 * Side effects:
 *	A new object is created.
 *
 *----------------------------------------------------------------------
 */

Tcl_Obj *
Tcl_ConcatObj(
    int objc,			/* Number of objects to concatenate. */
    Tcl_Obj *CONST objv[])	/* Array of objects to concatenate. */
{
    int allocSize, finalSize, length, elemLength, i;
    char *p;
    char *element;
    char *concatStr;
    Tcl_Obj *objPtr, *resPtr;

    /*
     * Check first to see if all the items are of list type or empty. If so,
     * we will concat them together as lists, and return a list object. This
     * is only valid when the lists have no current string representation,
     * since we don't know what the original type was. An original string rep
     * may have lost some whitespace info when converted which could be
     * important.
     */

    for (i = 0;  i < objc;  i++) {
	List *listRepPtr;

	objPtr = objv[i];
	if (objPtr->typePtr != &tclListType) {
	    TclGetString(objPtr);
	    if (objPtr->length) {
		break;
	    } else {
		continue;
	    }
	}
	listRepPtr = (List *) objPtr->internalRep.twoPtrValue.ptr1;
	if (objPtr->bytes != NULL && !listRepPtr->canonicalFlag) {
	    break;
	}
    }
    if (i == objc) {
	Tcl_Obj **listv;
	int listc;

	resPtr = NULL;
	for (i = 0;  i < objc;  i++) {
	    /*
	     * Tcl_ListObjAppendList could be used here, but this saves us a
	     * bit of type checking (since we've already done it). Use of
	     * INT_MAX tells us to always put the new stuff on the end. It
	     * will be set right in Tcl_ListObjReplace.
	     * Note that all objs at this point are either lists or have an
	     * empty string rep.
	     */

	    objPtr = objv[i];
	    if (objPtr->bytes && !objPtr->length) {
		continue;
	    }
	    TclListObjGetElements(NULL, objPtr, &listc, &listv);
	    if (listc) {
		if (resPtr) {
		    Tcl_ListObjReplace(NULL, resPtr, INT_MAX, 0, listc, listv);
		} else {
		    if (Tcl_IsShared(objPtr)) {
			resPtr = TclListObjCopy(NULL, objPtr);
		    } else {
			resPtr = objPtr;
		    }
		}
	    }
	}
	if (!resPtr) {
	    resPtr = Tcl_NewObj();
	}
	return resPtr;
    }

    /*
     * Something cannot be determined to be safe, so build the concatenation
     * the slow way, using the string representations.
     */

    allocSize = 0;
    for (i = 0;  i < objc;  i++) {
	objPtr = objv[i];
	element = TclGetStringFromObj(objPtr, &length);
	if ((element != NULL) && (length > 0)) {
	    allocSize += (length + 1);
	}
    }
    if (allocSize == 0) {
	allocSize = 1;		/* enough for the NULL byte at end */
    }

    /*
     * Allocate storage for the concatenated result. Note that allocSize is
     * one more than the total number of characters, and so includes room for
     * the terminating NULL byte.
     */

    concatStr = ckalloc((unsigned) allocSize);

    /*
     * Now concatenate the elements. Clip white space off the front and back
     * to generate a neater result, and ignore any empty elements. Also put a
     * null byte at the end.
     */

    finalSize = 0;
    if (objc == 0) {
	*concatStr = '\0';
    } else {
	p = concatStr;
	for (i = 0;  i < objc;  i++) {
	    objPtr = objv[i];
	    element = TclGetStringFromObj(objPtr, &elemLength);
	    while ((elemLength > 0) && (UCHAR(*element) < 127)
		    && isspace(UCHAR(*element))) { /* INTL: ISO C space. */
		element++;
		elemLength--;
	    }

	    /*
	     * Trim trailing white space. But, be careful not to trim a space
	     * character if it is preceded by a backslash: in this case it
	     * could be significant.
	     */

	    while ((elemLength > 0) && (UCHAR(element[elemLength-1]) < 127)
		    && isspace(UCHAR(element[elemLength-1]))
						/* INTL: ISO C space. */
		    && ((elemLength < 2) || (element[elemLength-2] != '\\'))) {
		elemLength--;
	    }
	    if (elemLength == 0) {
		continue;	/* nothing left of this element */
	    }
	    memcpy(p, element, (size_t) elemLength);
	    p += elemLength;
	    *p = ' ';
	    p++;
	    finalSize += (elemLength + 1);
	}
	if (p != concatStr) {
	    p[-1] = 0;
	    finalSize -= 1;	/* we overwrote the final ' ' */
	} else {
	    *p = 0;
	}
    }

    TclNewObj(objPtr);
    objPtr->bytes = concatStr;
    objPtr->length = finalSize;
    return objPtr;
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_StringMatch --
 *
 *	See if a particular string matches a particular pattern.
 *
 * Results:
 *	The return value is 1 if string matches pattern, and 0 otherwise. The
 *	matching operation permits the following special characters in the
 *	pattern: *?\[] (see the manual entry for details on what these mean).
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */

int
Tcl_StringMatch(
    CONST char *str,		/* String. */
    CONST char *pattern)	/* Pattern, which may contain special
				 * characters. */
{
    return Tcl_StringCaseMatch(str, pattern, 0);
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_StringCaseMatch --
 *
 *	See if a particular string matches a particular pattern. Allows case
 *	insensitivity.
 *
 * Results:
 *	The return value is 1 if string matches pattern, and 0 otherwise. The
 *	matching operation permits the following special characters in the
 *	pattern: *?\[] (see the manual entry for details on what these mean).
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */

int
Tcl_StringCaseMatch(
    CONST char *str,		/* String. */
    CONST char *pattern,	/* Pattern, which may contain special
				 * characters. */
    int nocase)			/* 0 for case sensitive, 1 for insensitive */
{
    int p, charLen;
    CONST char *pstart = pattern;
    Tcl_UniChar ch1, ch2;

    while (1) {
	p = *pattern;

	/*
	 * See if we're at the end of both the pattern and the string. If so,
	 * we succeeded. If we're at the end of the pattern but not at the end
	 * of the string, we failed.
	 */

	if (p == '\0') {
	    return (*str == '\0');
	}
	if ((*str == '\0') && (p != '*')) {
	    return 0;
	}

	/*
	 * Check for a "*" as the next pattern character. It matches any
	 * substring. We handle this by calling ourselves recursively for each
	 * postfix of string, until either we match or we reach the end of the
	 * string.
	 */

	if (p == '*') {
	    /*
	     * Skip all successive *'s in the pattern
	     */

	    while (*(++pattern) == '*') {}
	    p = *pattern;
	    if (p == '\0') {
		return 1;
	    }

	    /*
	     * This is a special case optimization for single-byte utf.
	     */

	    if (UCHAR(*pattern) < 0x80) {
		ch2 = (Tcl_UniChar)
			(nocase ? tolower(UCHAR(*pattern)) : UCHAR(*pattern));
	    } else {
		Tcl_UtfToUniChar(pattern, &ch2);
		if (nocase) {
		    ch2 = Tcl_UniCharToLower(ch2);
		}
	    }

	    while (1) {
		/*
		 * Optimization for matching - cruise through the string
		 * quickly if the next char in the pattern isn't a special
		 * character
		 */

		if ((p != '[') && (p != '?') && (p != '\\')) {
		    if (nocase) {
			while (*str) {
			    charLen = TclUtfToUniChar(str, &ch1);
			    if (ch2==ch1 || ch2==Tcl_UniCharToLower(ch1)) {
				break;
			    }
			    str += charLen;
			}
		    } else {
			/*
			 * There's no point in trying to make this code
			 * shorter, as the number of bytes you want to compare
			 * each time is non-constant.
			 */

			while (*str) {
			    charLen = TclUtfToUniChar(str, &ch1);
			    if (ch2 == ch1) {
				break;
			    }
			    str += charLen;
			}
		    }
		}
		if (Tcl_StringCaseMatch(str, pattern, nocase)) {
		    return 1;
		}
		if (*str == '\0') {
		    return 0;
		}
		str += TclUtfToUniChar(str, &ch1);
	    }
	}

	/*
	 * Check for a "?" as the next pattern character. It matches any
	 * single character.
	 */

	if (p == '?') {
	    pattern++;
	    str += TclUtfToUniChar(str, &ch1);
	    continue;
	}

	/*
	 * Check for a "[" as the next pattern character. It is followed by a
	 * list of characters that are acceptable, or by a range (two
	 * characters separated by "-").
	 */

	if (p == '[') {
	    Tcl_UniChar startChar, endChar;

	    pattern++;
	    if (UCHAR(*str) < 0x80) {
		ch1 = (Tcl_UniChar)
			(nocase ? tolower(UCHAR(*str)) : UCHAR(*str));
		str++;
	    } else {
		str += Tcl_UtfToUniChar(str, &ch1);
		if (nocase) {
		    ch1 = Tcl_UniCharToLower(ch1);
		}
	    }
	    while (1) {
		if ((*pattern == ']') || (*pattern == '\0')) {
		    return 0;
		}
		if (UCHAR(*pattern) < 0x80) {
		    startChar = (Tcl_UniChar) (nocase
			    ? tolower(UCHAR(*pattern)) : UCHAR(*pattern));
		    pattern++;
		} else {
		    pattern += Tcl_UtfToUniChar(pattern, &startChar);
		    if (nocase) {
			startChar = Tcl_UniCharToLower(startChar);
		    }
		}
		if (*pattern == '-') {
		    pattern++;
		    if (*pattern == '\0') {
			return 0;
		    }
		    if (UCHAR(*pattern) < 0x80) {
			endChar = (Tcl_UniChar) (nocase
				? tolower(UCHAR(*pattern)) : UCHAR(*pattern));
			pattern++;
		    } else {
			pattern += Tcl_UtfToUniChar(pattern, &endChar);
			if (nocase) {
			    endChar = Tcl_UniCharToLower(endChar);
			}
		    }
		    if (((startChar <= ch1) && (ch1 <= endChar))
			    || ((endChar <= ch1) && (ch1 <= startChar))) {
			/*
			 * Matches ranges of form [a-z] or [z-a].
			 */

			break;
		    }
		} else if (startChar == ch1) {
		    break;
		}
	    }
	    while (*pattern != ']') {
		if (*pattern == '\0') {
		    pattern = Tcl_UtfPrev(pattern, pstart);
		    break;
		}
		pattern++;
	    }
	    pattern++;
	    continue;
	}

	/*
	 * If the next pattern character is '\', just strip off the '\' so we
	 * do exact matching on the character that follows.
	 */

	if (p == '\\') {
	    pattern++;
	    if (*pattern == '\0') {
		return 0;
	    }
	}

	/*
	 * There's no special character. Just make sure that the next bytes of
	 * each string match.
	 */

	str += TclUtfToUniChar(str, &ch1);
	pattern += TclUtfToUniChar(pattern, &ch2);
	if (nocase) {
	    if (Tcl_UniCharToLower(ch1) != Tcl_UniCharToLower(ch2)) {
		return 0;
	    }
	} else if (ch1 != ch2) {
	    return 0;
	}
    }
}

/*
 *----------------------------------------------------------------------
 *
 * TclByteArrayMatch --
 *
 *	See if a particular string matches a particular pattern.  Does not
 *	allow for case insensitivity.
 *	Parallels tclUtf.c:TclUniCharMatch, adjusted for char* and sans nocase.
 *
 * Results:
 *	The return value is 1 if string matches pattern, and 0 otherwise. The
 *	matching operation permits the following special characters in the
 *	pattern: *?\[] (see the manual entry for details on what these mean).
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */

int
TclByteArrayMatch(
    const unsigned char *string,	/* String. */
    int strLen,				/* Length of String */
    const unsigned char *pattern,	/* Pattern, which may contain special
					 * characters. */
    int ptnLen,				/* Length of Pattern */
    int flags)
{
    const unsigned char *stringEnd, *patternEnd;
    unsigned char p;

    stringEnd = string + strLen;
    patternEnd = pattern + ptnLen;

    while (1) {
	/*
	 * See if we're at the end of both the pattern and the string. If so,
	 * we succeeded. If we're at the end of the pattern but not at the end
	 * of the string, we failed.
	 */

	if (pattern == patternEnd) {
	    return (string == stringEnd);
	}
	p = *pattern;
	if ((string == stringEnd) && (p != '*')) {
	    return 0;
	}

	/*
	 * Check for a "*" as the next pattern character. It matches any
	 * substring. We handle this by skipping all the characters up to the
	 * next matching one in the pattern, and then calling ourselves
	 * recursively for each postfix of string, until either we match or we
	 * reach the end of the string.
	 */

	if (p == '*') {
	    /*
	     * Skip all successive *'s in the pattern.
	     */

	    while (*(++pattern) == '*') {
		/* empty body */
	    }
	    if (pattern == patternEnd) {
		return 1;
	    }
	    p = *pattern;
	    while (1) {
		/*
		 * Optimization for matching - cruise through the string
		 * quickly if the next char in the pattern isn't a special
		 * character.
		 */

		if ((p != '[') && (p != '?') && (p != '\\')) {
		    while ((string < stringEnd) && (p != *string)) {
			string++;
		    }
		}
		if (TclByteArrayMatch(string, stringEnd - string,
				pattern, patternEnd - pattern, 0)) {
		    return 1;
		}
		if (string == stringEnd) {
		    return 0;
		}
		string++;
	    }
	}

	/*
	 * Check for a "?" as the next pattern character. It matches any
	 * single character.
	 */

	if (p == '?') {
	    pattern++;
	    string++;
	    continue;
	}

	/*
	 * Check for a "[" as the next pattern character. It is followed by a
	 * list of characters that are acceptable, or by a range (two
	 * characters separated by "-").
	 */

	if (p == '[') {
	    unsigned char ch1, startChar, endChar;

	    pattern++;
	    ch1 = *string;
	    string++;
	    while (1) {
		if ((*pattern == ']') || (pattern == patternEnd)) {
		    return 0;
		}
		startChar = *pattern;
		pattern++;
		if (*pattern == '-') {
		    pattern++;
		    if (pattern == patternEnd) {
			return 0;
		    }
		    endChar = *pattern;
		    pattern++;
		    if (((startChar <= ch1) && (ch1 <= endChar))
			    || ((endChar <= ch1) && (ch1 <= startChar))) {
			/*
			 * Matches ranges of form [a-z] or [z-a].
			 */
			break;
		    }
		} else if (startChar == ch1) {
		    break;
		}
	    }
	    while (*pattern != ']') {
		if (pattern == patternEnd) {
		    pattern--;
		    break;
		}
		pattern++;
	    }
	    pattern++;
	    continue;
	}

	/*
	 * If the next pattern character is '\', just strip off the '\' so we
	 * do exact matching on the character that follows.
	 */

	if (p == '\\') {
	    if (++pattern == patternEnd) {
		return 0;
	    }
	}

	/*
	 * There's no special character. Just make sure that the next bytes of
	 * each string match.
	 */

	if (*string != *pattern) {
	    return 0;
	}
	string++;
	pattern++;
    }
}

/*
 *----------------------------------------------------------------------
 *
 * TclStringMatchObj --
 *
 *	See if a particular string matches a particular pattern.
 *	Allows case insensitivity.  This is the generic multi-type handler
 *	for the various matching algorithms.
 *
 * Results:
 *	The return value is 1 if string matches pattern, and 0 otherwise. The
 *	matching operation permits the following special characters in the
 *	pattern: *?\[] (see the manual entry for details on what these mean).
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */

int
TclStringMatchObj(
    Tcl_Obj *strObj,	/* string object. */
    Tcl_Obj *ptnObj,	/* pattern object. */
    int flags)		/* Only TCL_MATCH_NOCASE should be passed or 0. */
{
    int match, length, plen;

    /*
     * Promote based on the type of incoming object.
     * XXX: Currently doesn't take advantage of exact-ness that
     * XXX: TclReToGlob tells us about
    trivial = nocase ? 0 : TclMatchIsTrivial(TclGetString(ptnObj));
     */

    if ((strObj->typePtr == &tclStringType)) {
	Tcl_UniChar *udata, *uptn;

	udata = Tcl_GetUnicodeFromObj(strObj, &length);
	uptn  = Tcl_GetUnicodeFromObj(ptnObj, &plen);
	match = TclUniCharMatch(udata, length, uptn, plen, flags);
    } else if ((strObj->typePtr == &tclByteArrayType) && !flags) {
	unsigned char *data, *ptn;

	data = Tcl_GetByteArrayFromObj(strObj, &length);
	ptn  = Tcl_GetByteArrayFromObj(ptnObj, &plen);
	match = TclByteArrayMatch(data, length, ptn, plen, 0);
    } else {
	match = Tcl_StringCaseMatch(TclGetString(strObj),
		TclGetString(ptnObj), flags);
    }
    return match;
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_DStringInit --
 *
 *	Initializes a dynamic string, discarding any previous contents of the
 *	string (Tcl_DStringFree should have been called already if the dynamic
 *	string was previously in use).
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	The dynamic string is initialized to be empty.
 *
 *----------------------------------------------------------------------
 */

void
Tcl_DStringInit(
    Tcl_DString *dsPtr)		/* Pointer to structure for dynamic string. */
{
    dsPtr->string = dsPtr->staticSpace;
    dsPtr->length = 0;
    dsPtr->spaceAvl = TCL_DSTRING_STATIC_SIZE;
    dsPtr->staticSpace[0] = '\0';
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_DStringAppend --
 *
 *	Append more bytes to the current value of a dynamic string.
 *
 * Results:
 *	The return value is a pointer to the dynamic string's new value.
 *
 * Side effects:
 *	Length bytes from "bytes" (or all of "bytes" if length is less than
 *	zero) are added to the current value of the string. Memory gets
 *	reallocated if needed to accomodate the string's new size.
 *
 *----------------------------------------------------------------------
 */

char *
Tcl_DStringAppend(
    Tcl_DString *dsPtr,		/* Structure describing dynamic string. */
    CONST char *bytes,		/* String to append. If length is -1 then this
				 * must be null-terminated. */
    int length)			/* Number of bytes from "bytes" to append. If
				 * < 0, then append all of bytes, up to null
				 * at end. */
{
    int newSize;
    char *dst;
    CONST char *end;

    if (length < 0) {
	length = strlen(bytes);
    }
    newSize = length + dsPtr->length;

    /*
     * Allocate a larger buffer for the string if the current one isn't large
     * enough. Allocate extra space in the new buffer so that there will be
     * room to grow before we have to allocate again.
     */

    if (newSize >= dsPtr->spaceAvl) {
	dsPtr->spaceAvl = newSize * 2;
	if (dsPtr->string == dsPtr->staticSpace) {
	    char *newString = ckalloc((unsigned) dsPtr->spaceAvl);

	    memcpy(newString, dsPtr->string, (size_t) dsPtr->length);
	    dsPtr->string = newString;
	} else {
	    dsPtr->string = ckrealloc((void *) dsPtr->string,
		    (size_t) dsPtr->spaceAvl);
	}
    }

    /*
     * Copy the new string into the buffer at the end of the old one.
     */

    for (dst = dsPtr->string + dsPtr->length, end = bytes+length;
	    bytes < end; bytes++, dst++) {
	*dst = *bytes;
    }
    *dst = '\0';
    dsPtr->length += length;
    return dsPtr->string;
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_DStringAppendElement --
 *
 *	Append a list element to the current value of a dynamic string.
 *
 * Results:
 *	The return value is a pointer to the dynamic string's new value.
 *
 * Side effects:
 *	String is reformatted as a list element and added to the current value
 *	of the string. Memory gets reallocated if needed to accomodate the
 *	string's new size.
 *
 *----------------------------------------------------------------------
 */

char *
Tcl_DStringAppendElement(
    Tcl_DString *dsPtr,		/* Structure describing dynamic string. */
    CONST char *element)	/* String to append. Must be
				 * null-terminated. */
{
    int newSize, flags, strSize;
    char *dst;

    strSize = ((element== NULL) ? 0 : strlen(element));
    newSize = Tcl_ScanCountedElement(element, strSize, &flags)
	+ dsPtr->length + 1;

    /*
     * Allocate a larger buffer for the string if the current one isn't large
     * enough. Allocate extra space in the new buffer so that there will be
     * room to grow before we have to allocate again. SPECIAL NOTE: must use
     * memcpy, not strcpy, to copy the string to a larger buffer, since there
     * may be embedded NULLs in the string in some cases.
     */

    if (newSize >= dsPtr->spaceAvl) {
	dsPtr->spaceAvl = newSize * 2;
	if (dsPtr->string == dsPtr->staticSpace) {
	    char *newString = ckalloc((unsigned) dsPtr->spaceAvl);

	    memcpy(newString, dsPtr->string, (size_t) dsPtr->length);
	    dsPtr->string = newString;
	} else {
	    dsPtr->string = (char *) ckrealloc((void *) dsPtr->string,
		    (size_t) dsPtr->spaceAvl);
	}
    }

    /*
     * Convert the new string to a list element and copy it into the buffer at
     * the end, with a space, if needed.
     */

    dst = dsPtr->string + dsPtr->length;
    if (TclNeedSpace(dsPtr->string, dst)) {
	*dst = ' ';
	dst++;
	dsPtr->length++;

	/*
	 * If we need a space to separate this element from preceding stuff,
	 * then this element will not lead a list, and need not have it's
	 * leading '#' quoted.
	 */

	flags |= TCL_DONT_QUOTE_HASH;
    }
    dsPtr->length += Tcl_ConvertCountedElement(element, strSize, dst, flags);
    return dsPtr->string;
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_DStringSetLength --
 *
 *	Change the length of a dynamic string. This can cause the string to
 *	either grow or shrink, depending on the value of length.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	The length of dsPtr is changed to length and a null byte is stored at
 *	that position in the string. If length is larger than the space
 *	allocated for dsPtr, then a panic occurs.
 *
 *----------------------------------------------------------------------
 */

void
Tcl_DStringSetLength(
    Tcl_DString *dsPtr,		/* Structure describing dynamic string. */
    int length)			/* New length for dynamic string. */
{
    int newsize;

    if (length < 0) {
	length = 0;
    }
    if (length >= dsPtr->spaceAvl) {
	/*
	 * There are two interesting cases here. In the first case, the user
	 * may be trying to allocate a large buffer of a specific size. It
	 * would be wasteful to overallocate that buffer, so we just allocate
	 * enough for the requested size plus the trailing null byte. In the
	 * second case, we are growing the buffer incrementally, so we need
	 * behavior similar to Tcl_DStringAppend. The requested length will
	 * usually be a small delta above the current spaceAvl, so we'll end
	 * up doubling the old size. This won't grow the buffer quite as
	 * quickly, but it should be close enough.
	 */

	newsize = dsPtr->spaceAvl * 2;
	if (length < newsize) {
	    dsPtr->spaceAvl = newsize;
	} else {
	    dsPtr->spaceAvl = length + 1;
	}
	if (dsPtr->string == dsPtr->staticSpace) {
	    char *newString = ckalloc((unsigned) dsPtr->spaceAvl);

	    memcpy(newString, dsPtr->string, (size_t) dsPtr->length);
	    dsPtr->string = newString;
	} else {
	    dsPtr->string = (char *) ckrealloc((void *) dsPtr->string,
		    (size_t) dsPtr->spaceAvl);
	}
    }
    dsPtr->length = length;
    dsPtr->string[length] = 0;
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_DStringFree --
 *
 *	Frees up any memory allocated for the dynamic string and reinitializes
 *	the string to an empty state.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	The previous contents of the dynamic string are lost, and the new
 *	value is an empty string.
 *
 *----------------------------------------------------------------------
 */

void
Tcl_DStringFree(
    Tcl_DString *dsPtr)		/* Structure describing dynamic string. */
{
    if (dsPtr->string != dsPtr->staticSpace) {
	ckfree(dsPtr->string);
    }
    dsPtr->string = dsPtr->staticSpace;
    dsPtr->length = 0;
    dsPtr->spaceAvl = TCL_DSTRING_STATIC_SIZE;
    dsPtr->staticSpace[0] = '\0';
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_DStringResult --
 *
 *	This function moves the value of a dynamic string into an interpreter
 *	as its string result. Afterwards, the dynamic string is reset to an
 *	empty string.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	The string is "moved" to interp's result, and any existing string
 *	result for interp is freed. dsPtr is reinitialized to an empty string.
 *
 *----------------------------------------------------------------------
 */

void
Tcl_DStringResult(
    Tcl_Interp *interp,		/* Interpreter whose result is to be reset. */
    Tcl_DString *dsPtr)		/* Dynamic string that is to become the
				 * result of interp. */
{
    Tcl_ResetResult(interp);

    if (dsPtr->string != dsPtr->staticSpace) {
	interp->result = dsPtr->string;
	interp->freeProc = TCL_DYNAMIC;
    } else if (dsPtr->length < TCL_RESULT_SIZE) {
	interp->result = ((Interp *) interp)->resultSpace;
	strcpy(interp->result, dsPtr->string);
    } else {
	Tcl_SetResult(interp, dsPtr->string, TCL_VOLATILE);
    }

    dsPtr->string = dsPtr->staticSpace;
    dsPtr->length = 0;
    dsPtr->spaceAvl = TCL_DSTRING_STATIC_SIZE;
    dsPtr->staticSpace[0] = '\0';
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_DStringGetResult --
 *
 *	This function moves an interpreter's result into a dynamic string.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	The interpreter's string result is cleared, and the previous contents
 *	of dsPtr are freed.
 *
 *	If the string result is empty, the object result is moved to the
 *	string result, then the object result is reset.
 *
 *----------------------------------------------------------------------
 */

void
Tcl_DStringGetResult(
    Tcl_Interp *interp,		/* Interpreter whose result is to be reset. */
    Tcl_DString *dsPtr)		/* Dynamic string that is to become the result
				 * of interp. */
{
    Interp *iPtr = (Interp *) interp;

    if (dsPtr->string != dsPtr->staticSpace) {
	ckfree(dsPtr->string);
    }

    /*
     * If the string result is empty, move the object result to the string
     * result, then reset the object result.
     */

    (void) Tcl_GetStringResult(interp);

    dsPtr->length = strlen(iPtr->result);
    if (iPtr->freeProc != NULL) {
	if (iPtr->freeProc == TCL_DYNAMIC) {
	    dsPtr->string = iPtr->result;
	    dsPtr->spaceAvl = dsPtr->length+1;
	} else {
	    dsPtr->string = (char *) ckalloc((unsigned) (dsPtr->length+1));
	    memcpy(dsPtr->string, iPtr->result, (unsigned) dsPtr->length+1);
	    (*iPtr->freeProc)(iPtr->result);
	}
	dsPtr->spaceAvl = dsPtr->length+1;
	iPtr->freeProc = NULL;
    } else {
	if (dsPtr->length < TCL_DSTRING_STATIC_SIZE) {
	    dsPtr->string = dsPtr->staticSpace;
	    dsPtr->spaceAvl = TCL_DSTRING_STATIC_SIZE;
	} else {
	    dsPtr->string = (char *) ckalloc((unsigned) (dsPtr->length + 1));
	    dsPtr->spaceAvl = dsPtr->length + 1;
	}
	memcpy(dsPtr->string, iPtr->result, (unsigned) dsPtr->length+1);
    }

    iPtr->result = iPtr->resultSpace;
    iPtr->resultSpace[0] = 0;
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_DStringStartSublist --
 *
 *	This function adds the necessary information to a dynamic string
 *	(e.g. " {") to start a sublist. Future element appends will be in the
 *	sublist rather than the main list.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	Characters get added to the dynamic string.
 *
 *----------------------------------------------------------------------
 */

void
Tcl_DStringStartSublist(
    Tcl_DString *dsPtr)		/* Dynamic string. */
{
    if (TclNeedSpace(dsPtr->string, dsPtr->string + dsPtr->length)) {
	Tcl_DStringAppend(dsPtr, " {", -1);
    } else {
	Tcl_DStringAppend(dsPtr, "{", -1);
    }
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_DStringEndSublist --
 *
 *	This function adds the necessary characters to a dynamic string to end
 *	a sublist (e.g. "}"). Future element appends will be in the enclosing
 *	(sub)list rather than the current sublist.
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
Tcl_DStringEndSublist(
    Tcl_DString *dsPtr)		/* Dynamic string. */
{
    Tcl_DStringAppend(dsPtr, "}", -1);
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_PrintDouble --
 *
 *	Given a floating-point value, this function converts it to an ASCII
 *	string using.
 *
 * Results:
 *	The ASCII equivalent of "value" is written at "dst". It is written
 *	using the current precision, and it is guaranteed to contain a decimal
 *	point or exponent, so that it looks like a floating-point value and
 *	not an integer.
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */

void
Tcl_PrintDouble(
    Tcl_Interp *interp,		/* Interpreter whose tcl_precision variable
				 * used to be used to control printing. It's
				 * ignored now. */
    double value,		/* Value to print as string. */
    char *dst)			/* Where to store converted value; must have
				 * at least TCL_DOUBLE_SPACE characters. */
{
    char *p, c;
    int exp;
    int signum;
    char buffer[TCL_DOUBLE_SPACE];
    Tcl_UniChar ch;

    int *precisionPtr = Tcl_GetThreadData(&precisionKey, (int)sizeof(int));

    /*
     * If *precisionPtr == 0, then use TclDoubleDigits to develop a decimal
     * significand and exponent, then format it in E or F format as
     * appropriate. If *precisionPtr != 0, use the native sprintf and then add
     * a trailing ".0" if there is no decimal point in the rep.
     */

    if (*precisionPtr == 0) {
	/*
	 * Handle NaN.
	 */

	if (TclIsNaN(value)) {
	    TclFormatNaN(value, dst);
	    return;
	}

	/*
	 * Handle infinities.
	 */

	if (TclIsInfinite(value)) {
	    if (value < 0) {
		strcpy(dst, "-Inf");
	    } else {
		strcpy(dst, "Inf");
	    }
	    return;
	}

	/*
	 * Ordinary (normal and denormal) values.
	 */

	exp = TclDoubleDigits(buffer, value, &signum);
	if (signum) {
	    *dst++ = '-';
	}
	p = buffer;
	if (exp < -3 || exp > 17) {
	    /*
	     * E format for numbers < 1e-3 or >= 1e17.
	     */

	    *dst++ = *p++;
	    c = *p;
	    if (c != '\0') {
		*dst++ = '.';
		while (c != '\0') {
		    *dst++ = c;
		    c = *++p;
		}
	    }
	    sprintf(dst, "e%+d", exp-1);
	} else {
	    /*
	     * F format for others.
	     */

	    if (exp <= 0) {
		*dst++ = '0';
	    }
	    c = *p;
	    while (exp-- > 0) {
		if (c != '\0') {
		    *dst++ = c;
		    c = *++p;
		} else {
		    *dst++ = '0';
		}
	    }
	    *dst++ = '.';
	    if (c == '\0') {
		*dst++ = '0';
	    } else {
		while (++exp < 0) {
		    *dst++ = '0';
		}
		while (c != '\0') {
		    *dst++ = c;
		    c = *++p;
		}
	    }
	    *dst++ = '\0';
	}
    } else {
	/*
	 * tcl_precision is supplied, pass it to the native sprintf.
	 */

	sprintf(dst, "%.*g", *precisionPtr, value);

	/*
	 * If the ASCII result looks like an integer, add ".0" so that it
	 * doesn't look like an integer anymore. This prevents floating-point
	 * values from being converted to integers unintentionally. Check for
	 * ASCII specifically to speed up the function.
	 */

	for (p = dst; *p != 0;) {
	    if (UCHAR(*p) < 0x80) {
		c = *p++;
	    } else {
		p += Tcl_UtfToUniChar(p, &ch);
		c = UCHAR(ch);
	    }
	    if ((c == '.') || isalpha(UCHAR(c))) {	/* INTL: ISO only. */
		return;
	    }
	}
	p[0] = '.';
	p[1] = '0';
	p[2] = 0;
    }
}

/*
 *----------------------------------------------------------------------
 *
 * TclPrecTraceProc --
 *
 *	This function is invoked whenever the variable "tcl_precision" is
 *	written.
 *
 * Results:
 *	Returns NULL if all went well, or an error message if the new value
 *	for the variable doesn't make sense.
 *
 * Side effects:
 *	If the new value doesn't make sense then this function undoes the
 *	effect of the variable modification. Otherwise it modifies the format
 *	string that's used by Tcl_PrintDouble.
 *
 *----------------------------------------------------------------------
 */

	/* ARGSUSED */
char *
TclPrecTraceProc(
    ClientData clientData,	/* Not used. */
    Tcl_Interp *interp,		/* Interpreter containing variable. */
    CONST char *name1,		/* Name of variable. */
    CONST char *name2,		/* Second part of variable name. */
    int flags)			/* Information about what happened. */
{
    Tcl_Obj* value;
    int prec;
    int *precisionPtr = Tcl_GetThreadData(&precisionKey, (int) sizeof(int));

    /*
     * If the variable is unset, then recreate the trace.
     */

    if (flags & TCL_TRACE_UNSETS) {
	if ((flags & TCL_TRACE_DESTROYED) && !Tcl_InterpDeleted(interp)) {
	    Tcl_TraceVar2(interp, name1, name2,
		    TCL_GLOBAL_ONLY|TCL_TRACE_READS|TCL_TRACE_WRITES
		    |TCL_TRACE_UNSETS, TclPrecTraceProc, clientData);
	}
	return NULL;
    }

    /*
     * When the variable is read, reset its value from our shared value. This
     * is needed in case the variable was modified in some other interpreter
     * so that this interpreter's value is out of date.
     */


    if (flags & TCL_TRACE_READS) {
	Tcl_SetVar2Ex(interp, name1, name2, Tcl_NewIntObj(*precisionPtr),
		flags & TCL_GLOBAL_ONLY);
	return NULL;
    }

    /*
     * The variable is being written. Check the new value and disallow it if
     * it isn't reasonable or if this is a safe interpreter (we don't want
     * safe interpreters messing up the precision of other interpreters).
     */

    if (Tcl_IsSafe(interp)) {
	return "can't modify precision from a safe interpreter";
    }
    value = Tcl_GetVar2Ex(interp, name1, name2, flags & TCL_GLOBAL_ONLY);
    if (value == NULL
	    || Tcl_GetIntFromObj((Tcl_Interp*) NULL, value, &prec) != TCL_OK
	    || prec < 0 || prec > TCL_MAX_PREC) {
	return "improper value for precision";
    }
    *precisionPtr = prec;
    return NULL;
}

/*
 *----------------------------------------------------------------------
 *
 * TclNeedSpace --
 *
 *	This function checks to see whether it is appropriate to add a space
 *	before appending a new list element to an existing string.
 *
 * Results:
 *	The return value is 1 if a space is appropriate, 0 otherwise.
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */

int
TclNeedSpace(
    CONST char *start,		/* First character in string. */
    CONST char *end)		/* End of string (place where space will be
				 * added, if appropriate). */
{
    /*
     * A space is needed unless either:
     * (a) we're at the start of the string, or
     */

    if (end == start) {
	return 0;
    }

    /*
     * (b) we're at the start of a nested list-element, quoted with an open
     *	   curly brace; we can be nested arbitrarily deep, so long as the
     *	   first curly brace starts an element, so backtrack over open curly
     *	   braces that are trailing characters of the string; and
     */

    end = Tcl_UtfPrev(end, start);
    while (*end == '{') {
	if (end == start) {
	    return 0;
	}
	end = Tcl_UtfPrev(end, start);
    }

    /*
     * (c) the trailing character of the string is already a list-element
     *	   separator (according to TclFindElement); that is, one of these
     *	   characters:
     *		\u0009	\t	TAB
     *		\u000A	\n	NEWLINE
     *		\u000B	\v	VERTICAL TAB
     *		\u000C	\f	FORM FEED
     *		\u000D	\r	CARRIAGE RETURN
     *		\u0020		SPACE
     *	   with the condition that the penultimate character is not a
     *	   backslash.
     */

    if (*end > 0x20) {
	/*
	 * Performance tweak. All ASCII spaces are <= 0x20. So get a quick
	 * answer for most characters before comparing against all spaces in
	 * the switch below.
	 *
	 * NOTE: Remove this if other Unicode spaces ever get accepted as
	 * list-element separators.
	 */
	return 1;
    }
    switch (*end) {
    case ' ':
    case '\t':
    case '\n':
    case '\r':
    case '\v':
    case '\f':
	if ((end == start) || (end[-1] != '\\')) {
	    return 0;
	}
    }
    return 1;
}

/*
 *----------------------------------------------------------------------
 *
 * TclGetIntForIndex --
 *
 *	This function returns an integer corresponding to the list index held
 *	in a Tcl object. The Tcl object's value is expected to be in the
 *	format integer([+-]integer)? or the format end([+-]integer)?.
 *
 * Results:
 *	The return value is normally TCL_OK, which means that the index was
 *	successfully stored into the location referenced by "indexPtr". If the
 *	Tcl object referenced by "objPtr" has the value "end", the value
 *	stored is "endValue". If "objPtr"s values is not of one of the
 *	expected formats, TCL_ERROR is returned and, if "interp" is non-NULL,
 *	an error message is left in the interpreter's result object.
 *
 * Side effects:
 *	The object referenced by "objPtr" might be converted to an integer,
 *	wide integer, or end-based-index object.
 *
 *----------------------------------------------------------------------
 */

int
TclGetIntForIndex(
    Tcl_Interp *interp,		/* Interpreter to use for error reporting. If
				 * NULL, then no error message is left after
				 * errors. */
    Tcl_Obj *objPtr,		/* Points to an object containing either "end"
				 * or an integer. */
    int endValue,		/* The value to be stored at "indexPtr" if
				 * "objPtr" holds "end". */
    int *indexPtr)		/* Location filled in with an integer
				 * representing an index. */
{
    int length;
    char *opPtr, *bytes;

    if (TclGetIntFromObj(NULL, objPtr, indexPtr) == TCL_OK) {
	return TCL_OK;
    }

    if (SetEndOffsetFromAny(NULL, objPtr) == TCL_OK) {
	/*
	 * If the object is already an offset from the end of the list, or can
	 * be converted to one, use it.
	 */

	*indexPtr = endValue + objPtr->internalRep.longValue;
	return TCL_OK;
    }

    bytes = TclGetStringFromObj(objPtr, &length);

    /*
     * Leading whitespace is acceptable in an index.
     */

    while (length && isspace(UCHAR(*bytes))) {		/* INTL: ISO space. */
	bytes++;
	length--;
    }

    if (TclParseNumber(NULL, NULL, NULL, bytes, length, (const char **)&opPtr,
	    TCL_PARSE_INTEGER_ONLY | TCL_PARSE_NO_WHITESPACE) == TCL_OK) {
	int code, first, second;
	char savedOp = *opPtr;

	if ((savedOp != '+') && (savedOp != '-')) {
	    goto parseError;
	}
	if (isspace(UCHAR(opPtr[1]))) {
	    goto parseError;
	}
	*opPtr = '\0';
	code = Tcl_GetInt(interp, bytes, &first);
	*opPtr = savedOp;
	if (code == TCL_ERROR) {
	    goto parseError;
	}
	if (TCL_ERROR == Tcl_GetInt(interp, opPtr+1, &second)) {
	    goto parseError;
	}
	if (savedOp == '+') {
	    *indexPtr = first + second;
	} else {
	    *indexPtr = first - second;
	}
	return TCL_OK;
    }

    /*
     * Report a parse error.
     */

  parseError:
    if (interp != NULL) {
	char *bytes = Tcl_GetString(objPtr);

	/*
	 * The result might not be empty; this resets it which should be both
	 * a cheap operation, and of little problem because this is an
	 * error-generation path anyway.
	 */

	Tcl_ResetResult(interp);
	Tcl_AppendResult(interp, "bad index \"", bytes,
		"\": must be integer?[+-]integer? or end?[+-]integer?", NULL);
	if (!strncmp(bytes, "end-", 4)) {
	    bytes += 4;
	}
	TclCheckBadOctal(interp, bytes);
    }

    return TCL_ERROR;
}

/*
 *----------------------------------------------------------------------
 *
 * UpdateStringOfEndOffset --
 *
 *	Update the string rep of a Tcl object holding an "end-offset"
 *	expression.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	Stores a valid string in the object's string rep.
 *
 * This function does NOT free any earlier string rep. If it is called on an
 * object that already has a valid string rep, it will leak memory.
 *
 *----------------------------------------------------------------------
 */

static void
UpdateStringOfEndOffset(
    register Tcl_Obj* objPtr)
{
    char buffer[TCL_INTEGER_SPACE + sizeof("end") + 1];
    register int len;

    strcpy(buffer, "end");
    len = sizeof("end") - 1;
    if (objPtr->internalRep.longValue != 0) {
	buffer[len++] = '-';
	len += TclFormatInt(buffer+len, -(objPtr->internalRep.longValue));
    }
    objPtr->bytes = ckalloc((unsigned) len+1);
    memcpy(objPtr->bytes, buffer, (unsigned) len+1);
    objPtr->length = len;
}

/*
 *----------------------------------------------------------------------
 *
 * SetEndOffsetFromAny --
 *
 *	Look for a string of the form "end[+-]offset" and convert it to an
 *	internal representation holding the offset.
 *
 * Results:
 *	Returns TCL_OK if ok, TCL_ERROR if the string was badly formed.
 *
 * Side effects:
 *	If interp is not NULL, stores an error message in the interpreter
 *	result.
 *
 *----------------------------------------------------------------------
 */

static int
SetEndOffsetFromAny(
    Tcl_Interp *interp,		/* Tcl interpreter or NULL */
    Tcl_Obj *objPtr)		/* Pointer to the object to parse */
{
    int offset;			/* Offset in the "end-offset" expression */
    register char* bytes;	/* String rep of the object */
    int length;			/* Length of the object's string rep */

    /*
     * If it's already the right type, we're fine.
     */

    if (objPtr->typePtr == &tclEndOffsetType) {
	return TCL_OK;
    }

    /*
     * Check for a string rep of the right form.
     */

    bytes = TclGetStringFromObj(objPtr, &length);
    if ((*bytes != 'e') || (strncmp(bytes, "end",
	    (size_t)((length > 3) ? 3 : length)) != 0)) {
	if (interp != NULL) {
	    Tcl_ResetResult(interp);
	    Tcl_AppendResult(interp, "bad index \"", bytes,
		    "\": must be end?[+-]integer?", NULL);
	}
	return TCL_ERROR;
    }

    /*
     * Convert the string rep.
     */

    if (length <= 3) {
	offset = 0;
    } else if ((length > 4) && ((bytes[3] == '-') || (bytes[3] == '+'))) {
	/*
	 * This is our limited string expression evaluator. Pass everything
	 * after "end-" to Tcl_GetInt, then reverse for offset.
	 */

	if (isspace(UCHAR(bytes[4]))) {
	    return TCL_ERROR;
	}
	if (Tcl_GetInt(interp, bytes+4, &offset) != TCL_OK) {
	    return TCL_ERROR;
	}
	if (bytes[3] == '-') {
	    offset = -offset;
	}
    } else {
	/*
	 * Conversion failed. Report the error.
	 */

	if (interp != NULL) {
	    Tcl_ResetResult(interp);
	    Tcl_AppendResult(interp, "bad index \"", bytes,
		    "\": must be end?[+-]integer?", NULL);
	}
	return TCL_ERROR;
    }

    /*
     * The conversion succeeded. Free the old internal rep and set the new
     * one.
     */

    TclFreeIntRep(objPtr);
    objPtr->internalRep.longValue = offset;
    objPtr->typePtr = &tclEndOffsetType;

    return TCL_OK;
}

/*
 *----------------------------------------------------------------------
 *
 * TclCheckBadOctal --
 *
 *	This function checks for a bad octal value and appends a meaningful
 *	error to the interp's result.
 *
 * Results:
 *	1 if the argument was a bad octal, else 0.
 *
 * Side effects:
 *	The interpreter's result is modified.
 *
 *----------------------------------------------------------------------
 */

int
TclCheckBadOctal(
    Tcl_Interp *interp,		/* Interpreter to use for error reporting. If
				 * NULL, then no error message is left after
				 * errors. */
    CONST char *value)		/* String to check. */
{
    register CONST char *p = value;

    /*
     * A frequent mistake is invalid octal values due to an unwanted leading
     * zero. Try to generate a meaningful error message.
     */

    while (isspace(UCHAR(*p))) {	/* INTL: ISO space. */
	p++;
    }
    if (*p == '+' || *p == '-') {
	p++;
    }
    if (*p == '0') {
	if ((p[1] == 'o') || p[1] == 'O') {
	    p+=2;
	}
	while (isdigit(UCHAR(*p))) {	/* INTL: digit. */
	    p++;
	}
	while (isspace(UCHAR(*p))) {	/* INTL: ISO space. */
	    p++;
	}
	if (*p == '\0') {
	    /*
	     * Reached end of string.
	     */

	    if (interp != NULL) {
		/*
		 * Don't reset the result here because we want this result to
		 * be added to an existing error message as extra info.
		 */

		Tcl_AppendResult(interp, " (looks like invalid octal number)",
			NULL);
	    }
	    return 1;
	}
    }
    return 0;
}

/*
 *----------------------------------------------------------------------
 *
 * ClearHash --
 *
 *	Remove all the entries in the hash table *tablePtr.
 *
 *----------------------------------------------------------------------
 */

static void
ClearHash(
    Tcl_HashTable *tablePtr)
{
    Tcl_HashSearch search;
    Tcl_HashEntry *hPtr;

    for (hPtr = Tcl_FirstHashEntry(tablePtr, &search); hPtr != NULL;
	    hPtr = Tcl_NextHashEntry(&search)) {
	Tcl_Obj *objPtr = (Tcl_Obj *) Tcl_GetHashValue(hPtr);
	Tcl_DecrRefCount(objPtr);
	Tcl_DeleteHashEntry(hPtr);
    }
}

/*
 *----------------------------------------------------------------------
 *
 * GetThreadHash --
 *
 *	Get a thread-specific (Tcl_HashTable *) associated with a thread data
 *	key.
 *
 * Results:
 *	The Tcl_HashTable * corresponding to *keyPtr.
 *
 * Side effects:
 *	The first call on a keyPtr in each thread creates a new Tcl_HashTable,
 *	and registers a thread exit handler to dispose of it.
 *
 *----------------------------------------------------------------------
 */

static Tcl_HashTable *
GetThreadHash(
    Tcl_ThreadDataKey *keyPtr)
{
    Tcl_HashTable **tablePtrPtr = (Tcl_HashTable **)
	    Tcl_GetThreadData(keyPtr, (int) sizeof(Tcl_HashTable *));

    if (NULL == *tablePtrPtr) {
	*tablePtrPtr = (Tcl_HashTable *)ckalloc(sizeof(Tcl_HashTable));
	Tcl_CreateThreadExitHandler(FreeThreadHash, (ClientData)*tablePtrPtr);
	Tcl_InitHashTable(*tablePtrPtr, TCL_ONE_WORD_KEYS);
    }
    return *tablePtrPtr;
}

/*
 *----------------------------------------------------------------------
 *
 * FreeThreadHash --
 *
 *	Thread exit handler used by GetThreadHash to dispose of a thread hash
 *	table.
 *
 * Side effects:
 *	Frees a Tcl_HashTable.
 *
 *----------------------------------------------------------------------
 */

static void
FreeThreadHash(
    ClientData clientData)
{
    Tcl_HashTable *tablePtr = (Tcl_HashTable *) clientData;

    ClearHash(tablePtr);
    Tcl_DeleteHashTable(tablePtr);
    ckfree((char *) tablePtr);
}

/*
 *----------------------------------------------------------------------
 *
 * FreeProcessGlobalValue --
 *
 *	Exit handler used by Tcl(Set|Get)ProcessGlobalValue to cleanup a
 *	ProcessGlobalValue at exit.
 *
 *----------------------------------------------------------------------
 */

static void
FreeProcessGlobalValue(
    ClientData clientData)
{
    ProcessGlobalValue *pgvPtr = (ProcessGlobalValue *) clientData;

    pgvPtr->epoch++;
    pgvPtr->numBytes = 0;
    ckfree(pgvPtr->value);
    pgvPtr->value = NULL;
    if (pgvPtr->encoding) {
	Tcl_FreeEncoding(pgvPtr->encoding);
	pgvPtr->encoding = NULL;
    }
    Tcl_MutexFinalize(&pgvPtr->mutex);
}

/*
 *----------------------------------------------------------------------
 *
 * TclSetProcessGlobalValue --
 *
 *	Utility routine to set a global value shared by all threads in the
 *	process while keeping a thread-local copy as well.
 *
 *----------------------------------------------------------------------
 */

void
TclSetProcessGlobalValue(
    ProcessGlobalValue *pgvPtr,
    Tcl_Obj *newValue,
    Tcl_Encoding encoding)
{
    CONST char *bytes;
    Tcl_HashTable *cacheMap;
    Tcl_HashEntry *hPtr;
    int dummy;

    Tcl_MutexLock(&pgvPtr->mutex);

    /*
     * Fill the global string value.
     */

    pgvPtr->epoch++;
    if (NULL != pgvPtr->value) {
	ckfree(pgvPtr->value);
    } else {
	Tcl_CreateExitHandler(FreeProcessGlobalValue, (ClientData) pgvPtr);
    }
    bytes = Tcl_GetStringFromObj(newValue, &pgvPtr->numBytes);
    pgvPtr->value = ckalloc((unsigned) pgvPtr->numBytes + 1);
    memcpy(pgvPtr->value, bytes, (unsigned) pgvPtr->numBytes + 1);
    if (pgvPtr->encoding) {
	Tcl_FreeEncoding(pgvPtr->encoding);
    }
    pgvPtr->encoding = encoding;

    /*
     * Fill the local thread copy directly with the Tcl_Obj value to avoid
     * loss of the intrep. Increment newValue refCount early to handle case
     * where we set a PGV to itself.
     */

    Tcl_IncrRefCount(newValue);
    cacheMap = GetThreadHash(&pgvPtr->key);
    ClearHash(cacheMap);
    hPtr = Tcl_CreateHashEntry(cacheMap,
	    (char *) INT2PTR(pgvPtr->epoch), &dummy);
    Tcl_SetHashValue(hPtr, (ClientData) newValue);
    Tcl_MutexUnlock(&pgvPtr->mutex);
}

/*
 *----------------------------------------------------------------------
 *
 * TclGetProcessGlobalValue --
 *
 *	Retrieve a global value shared among all threads of the process,
 *	preferring a thread-local copy as long as it remains valid.
 *
 * Results:
 *	Returns a (Tcl_Obj *) that holds a copy of the global value.
 *
 *----------------------------------------------------------------------
 */

Tcl_Obj *
TclGetProcessGlobalValue(
    ProcessGlobalValue *pgvPtr)
{
    Tcl_Obj *value = NULL;
    Tcl_HashTable *cacheMap;
    Tcl_HashEntry *hPtr;
    int epoch = pgvPtr->epoch;

    if (pgvPtr->encoding) {
	Tcl_Encoding current = Tcl_GetEncoding(NULL, NULL);

	if (pgvPtr->encoding != current) {
	    /*
	     * The system encoding has changed since the master string value
	     * was saved. Convert the master value to be based on the new
	     * system encoding.
	     */

	    Tcl_DString native, newValue;

	    Tcl_MutexLock(&pgvPtr->mutex);
	    pgvPtr->epoch++;
	    epoch = pgvPtr->epoch;
	    Tcl_UtfToExternalDString(pgvPtr->encoding, pgvPtr->value,
		    pgvPtr->numBytes, &native);
	    Tcl_ExternalToUtfDString(current, Tcl_DStringValue(&native),
	    Tcl_DStringLength(&native), &newValue);
	    Tcl_DStringFree(&native);
	    ckfree(pgvPtr->value);
	    pgvPtr->value = ckalloc((unsigned int)
		    Tcl_DStringLength(&newValue) + 1);
	    memcpy(pgvPtr->value, Tcl_DStringValue(&newValue),
		    (size_t) Tcl_DStringLength(&newValue) + 1);
	    Tcl_DStringFree(&newValue);
	    Tcl_FreeEncoding(pgvPtr->encoding);
	    pgvPtr->encoding = current;
	    Tcl_MutexUnlock(&pgvPtr->mutex);
	} else {
	    Tcl_FreeEncoding(current);
	}
    }
    cacheMap = GetThreadHash(&pgvPtr->key);
    hPtr = Tcl_FindHashEntry(cacheMap, (char *) INT2PTR(epoch));
    if (NULL == hPtr) {
	int dummy;

	/*
	 * No cache for the current epoch - must be a new one.
	 *
	 * First, clear the cacheMap, as anything in it must refer to some
	 * expired epoch.
	 */

	ClearHash(cacheMap);

	/*
	 * If no thread has set the shared value, call the initializer.
	 */

	Tcl_MutexLock(&pgvPtr->mutex);
	if ((NULL == pgvPtr->value) && (pgvPtr->proc)) {
	    pgvPtr->epoch++;
	    (*(pgvPtr->proc))(&pgvPtr->value, &pgvPtr->numBytes,
		    &pgvPtr->encoding);
	    if (pgvPtr->value == NULL) {
		Tcl_Panic("PGV Initializer did not initialize");
	    }
	    Tcl_CreateExitHandler(FreeProcessGlobalValue, (ClientData)pgvPtr);
	}

	/*
	 * Store a copy of the shared value in our epoch-indexed cache.
	 */

	value = Tcl_NewStringObj(pgvPtr->value, pgvPtr->numBytes);
	hPtr = Tcl_CreateHashEntry(cacheMap,
		(char *) INT2PTR(pgvPtr->epoch), &dummy);
	Tcl_MutexUnlock(&pgvPtr->mutex);
	Tcl_SetHashValue(hPtr, (ClientData) value);
	Tcl_IncrRefCount(value);
    }
    return (Tcl_Obj *) Tcl_GetHashValue(hPtr);
}

/*
 *----------------------------------------------------------------------
 *
 * TclSetObjNameOfExecutable --
 *
 *	This function stores the absolute pathname of the executable file
 *	(normally as computed by TclpFindExecutable).
 *
 * Results:
 * 	None.
 *
 * Side effects:
 *	Stores the executable name.
 *
 *----------------------------------------------------------------------
 */

void
TclSetObjNameOfExecutable(
    Tcl_Obj *name,
    Tcl_Encoding encoding)
{
    TclSetProcessGlobalValue(&executableName, name, encoding);
}

/*
 *----------------------------------------------------------------------
 *
 * TclGetObjNameOfExecutable --
 *
 *	This function retrieves the absolute pathname of the application in
 *	which the Tcl library is running, usually as previously stored by
 *	TclpFindExecutable(). This function call is the C API equivalent to
 *	the "info nameofexecutable" command.
 *
 * Results:
 *	A pointer to an "fsPath" Tcl_Obj, or to an empty Tcl_Obj if the
 *	pathname of the application is unknown.
 *
 * Side effects:
 * 	None.
 *
 *----------------------------------------------------------------------
 */

Tcl_Obj *
TclGetObjNameOfExecutable(void)
{
    return TclGetProcessGlobalValue(&executableName);
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_GetNameOfExecutable --
 *
 *	This function retrieves the absolute pathname of the application in
 *	which the Tcl library is running, and returns it in string form.
 *
 * 	The returned string belongs to Tcl and should be copied if the caller
 * 	plans to keep it, to guard against it becoming invalid.
 *
 * Results:
 *	A pointer to the internal string or NULL if the internal full path
 *	name has not been computed or unknown.
 *
 * Side effects:
 * 	None.
 *
 *----------------------------------------------------------------------
 */

CONST char *
Tcl_GetNameOfExecutable(void)
{
    int numBytes;
    const char *bytes =
	    Tcl_GetStringFromObj(TclGetObjNameOfExecutable(), &numBytes);

    if (numBytes == 0) {
	return NULL;
    }
    return bytes;
}

/*
 *----------------------------------------------------------------------
 *
 * TclpGetTime --
 *
 *	Deprecated synonym for Tcl_GetTime. This function is provided for the
 *	benefit of extensions written before Tcl_GetTime was exported from the
 *	library.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	Stores current time in the buffer designated by "timePtr"
 *
 *----------------------------------------------------------------------
 */

void
TclpGetTime(
    Tcl_Time *timePtr)
{
    Tcl_GetTime(timePtr);
}

/*
 *----------------------------------------------------------------------
 *
 * TclGetPlatform --
 *
 *	This is a kludge that allows the test library to get access the
 *	internal tclPlatform variable.
 *
 * Results:
 *	Returns a pointer to the tclPlatform variable.
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */

TclPlatformType *
TclGetPlatform(void)
{
    return &tclPlatform;
}

/*
 *----------------------------------------------------------------------
 *
 * TclReToGlob --
 *
 *	Attempt to convert a regular expression to an equivalent glob pattern.
 *
 * Results:
 *	Returns TCL_OK on success, TCL_ERROR on failure. If interp is not
 *	NULL, an error message is placed in the result. On success, the
 *	DString will contain an exact equivalent glob pattern. The caller is
 *	responsible for calling Tcl_DStringFree on success. If exactPtr is not
 *	NULL, it will be 1 if an exact match qualifies.
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */

int
TclReToGlob(
    Tcl_Interp *interp,
    const char *reStr,
    int reStrLen,
    Tcl_DString *dsPtr,
    int *exactPtr)
{
    int anchorLeft, anchorRight, lastIsStar;
    char *dsStr, *dsStrStart, *msg;
    const char *p, *strEnd;

    strEnd = reStr + reStrLen;
    Tcl_DStringInit(dsPtr);

    /*
     * "***=xxx" == "*xxx*"
     */

    if ((reStrLen >= 4) && (memcmp("***=", reStr, 4) == 0)) {
	if (exactPtr) {
	    *exactPtr = 1;
	}
	Tcl_DStringAppend(dsPtr, reStr + 4, reStrLen - 4);
	return TCL_OK;
    }

    /*
     * Write to the ds directly without the function overhead.
     * An equivalent glob pattern can be no more than reStrLen+2 in size.
     */

    Tcl_DStringSetLength(dsPtr, reStrLen + 2);
    dsStrStart = Tcl_DStringValue(dsPtr);

    /*
     * Check for anchored REs (ie ^foo$), so we can use string equal if
     * possible. Do not alter the start of str so we can free it correctly.
     *
     * Keep track of the last char being an unescaped star to prevent
     * multiple instances.  Simpler than checking that the last star
     * may be escaped.
     */

    msg = NULL;
    p = reStr;
    anchorRight = 0;
    lastIsStar = 0;
    dsStr = dsStrStart;
    if (*p == '^') {
	anchorLeft = 1;
	p++;
    } else {
	anchorLeft = 0;
	*dsStr++ = '*';
	lastIsStar = 1;
    }

    for ( ; p < strEnd; p++) {
	switch (*p) {
	case '\\':
	    p++;
	    switch (*p) {
	    case 'a':
		*dsStr++ = '\a';
		break;
	    case 'b':
		*dsStr++ = '\b';
		break;
	    case 'f':
		*dsStr++ = '\f';
		break;
	    case 'n':
		*dsStr++ = '\n';
		break;
	    case 'r':
		*dsStr++ = '\r';
		break;
	    case 't':
		*dsStr++ = '\t';
		break;
	    case 'v':
		*dsStr++ = '\v';
		break;
	    case 'B': case '\\':
		*dsStr++ = '\\';
		*dsStr++ = '\\';
		anchorLeft = 0; /* prevent exact match */
		break;
	    case '*': case '[': case ']': case '?':
		/* Only add \ where necessary for glob */
		*dsStr++ = '\\';
		anchorLeft = 0; /* prevent exact match */
		/* fall through */
	    case '{': case '}': case '(': case ')': case '+':
	    case '.': case '|': case '^': case '$':
		*dsStr++ = *p;
		break;
	    default:
		msg = "invalid escape sequence";
		goto invalidGlob;
	    }
	    break;
	case '.':
	    anchorLeft = 0; /* prevent exact match */
	    if (p+1 < strEnd) {
		if (p[1] == '*') {
		    p++;
		    if (!lastIsStar) {
			*dsStr++ = '*';
			lastIsStar = 1;
		    }
		    continue;
		} else if (p[1] == '+') {
		    p++;
		    *dsStr++ = '?';
		    *dsStr++ = '*';
		    lastIsStar = 1;
		    continue;
		}
	    }
	    *dsStr++ = '?';
	    break;
	case '$':
	    if (p+1 != strEnd) {
		msg = "$ not anchor";
		goto invalidGlob;
	    }
	    anchorRight = 1;
	    break;
	case '*': case '+': case '?': case '|': case '^':
	case '{': case '}': case '(': case ')': case '[': case ']':
	    msg = "unhandled RE special char";
	    goto invalidGlob;
	    break;
	default:
	    *dsStr++ = *p;
	    break;
	}
	lastIsStar = 0;
    }
    if (!anchorRight && !lastIsStar) {
	*dsStr++ = '*';
    }
    Tcl_DStringSetLength(dsPtr, dsStr - dsStrStart);

    if (exactPtr) {
	*exactPtr = (anchorLeft && anchorRight);
    }

#if 0
    fprintf(stderr, "INPUT RE '%.*s' OUTPUT GLOB '%s' anchor %d:%d \n",
	    reStrLen, reStr,
	    Tcl_DStringValue(dsPtr), anchorLeft, anchorRight);
    fflush(stderr);
#endif
    return TCL_OK;

  invalidGlob:
#if 0
    fprintf(stderr, "INPUT RE '%.*s' NO OUTPUT GLOB %s (%c)\n",
	    reStrLen, reStr, msg, *p);
    fflush(stderr);
#endif
    if (interp != NULL) {
	Tcl_AppendResult(interp, msg, NULL);
    }
    Tcl_DStringFree(dsPtr);
    return TCL_ERROR;
}

/*
 * Local Variables:
 * mode: c
 * c-basic-offset: 4
 * fill-column: 78
 * End:
 */
