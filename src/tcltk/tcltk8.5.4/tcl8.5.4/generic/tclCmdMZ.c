/*
 * tclCmdMZ.c --
 *
 *	This file contains the top-level command routines for most of the Tcl
 *	built-in commands whose names begin with the letters M to Z. It
 *	contains only commands in the generic core (i.e. those that don't
 *	depend much upon UNIX facilities).
 *
 * Copyright (c) 1987-1993 The Regents of the University of California.
 * Copyright (c) 1994-1997 Sun Microsystems, Inc.
 * Copyright (c) 1998-2000 Scriptics Corporation.
 * Copyright (c) 2002 ActiveState Corporation.
 * Copyright (c) 2003 Donal K. Fellows.
 *
 * See the file "license.terms" for information on usage and redistribution of
 * this file, and for a DISCLAIMER OF ALL WARRANTIES.
 *
 * RCS: @(#) $Id: tclCmdMZ.c,v 1.163 2007/12/13 15:23:15 dgp Exp $
 */

#include "tclInt.h"
#include "tclRegexp.h"

static int		UniCharIsAscii(int character);

/*
 *----------------------------------------------------------------------
 *
 * Tcl_PwdObjCmd --
 *
 *	This procedure is invoked to process the "pwd" Tcl command. See the
 *	user documentation for details on what it does.
 *
 * Results:
 *	A standard Tcl result.
 *
 * Side effects:
 *	See the user documentation.
 *
 *----------------------------------------------------------------------
 */

int
Tcl_PwdObjCmd(
    ClientData dummy,		/* Not used. */
    Tcl_Interp *interp,		/* Current interpreter. */
    int objc,			/* Number of arguments. */
    Tcl_Obj *CONST objv[])	/* Argument objects. */
{
    Tcl_Obj *retVal;

    if (objc != 1) {
	Tcl_WrongNumArgs(interp, 1, objv, NULL);
	return TCL_ERROR;
    }

    retVal = Tcl_FSGetCwd(interp);
    if (retVal == NULL) {
	return TCL_ERROR;
    }
    Tcl_SetObjResult(interp, retVal);
    Tcl_DecrRefCount(retVal);
    return TCL_OK;
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_RegexpObjCmd --
 *
 *	This procedure is invoked to process the "regexp" Tcl command. See
 *	the user documentation for details on what it does.
 *
 * Results:
 *	A standard Tcl result.
 *
 * Side effects:
 *	See the user documentation.
 *
 *----------------------------------------------------------------------
 */

int
Tcl_RegexpObjCmd(
    ClientData dummy,		/* Not used. */
    Tcl_Interp *interp,		/* Current interpreter. */
    int objc,			/* Number of arguments. */
    Tcl_Obj *CONST objv[])	/* Argument objects. */
{
    int i, indices, match, about, offset, all, doinline, numMatchesSaved;
    int cflags, eflags, stringLength;
    Tcl_RegExp regExpr;
    Tcl_Obj *objPtr, *startIndex = NULL, *resultPtr = NULL;
    Tcl_RegExpInfo info;
    static CONST char *options[] = {
	"-all",		"-about",	"-indices",	"-inline",
	"-expanded",	"-line",	"-linestop",	"-lineanchor",
	"-nocase",	"-start",	"--",		NULL
    };
    enum options {
	REGEXP_ALL,	REGEXP_ABOUT,	REGEXP_INDICES,	REGEXP_INLINE,
	REGEXP_EXPANDED,REGEXP_LINE,	REGEXP_LINESTOP,REGEXP_LINEANCHOR,
	REGEXP_NOCASE,	REGEXP_START,	REGEXP_LAST
    };

    indices = 0;
    about = 0;
    cflags = TCL_REG_ADVANCED;
    eflags = 0;
    offset = 0;
    all = 0;
    doinline = 0;

    for (i = 1; i < objc; i++) {
	char *name;
	int index;

	name = TclGetString(objv[i]);
	if (name[0] != '-') {
	    break;
	}
	if (Tcl_GetIndexFromObj(interp, objv[i], options, "switch", TCL_EXACT,
		&index) != TCL_OK) {
	    goto optionError;
	}
	switch ((enum options) index) {
	case REGEXP_ALL:
	    all = 1;
	    break;
	case REGEXP_INDICES:
	    indices = 1;
	    break;
	case REGEXP_INLINE:
	    doinline = 1;
	    break;
	case REGEXP_NOCASE:
	    cflags |= TCL_REG_NOCASE;
	    break;
	case REGEXP_ABOUT:
	    about = 1;
	    break;
	case REGEXP_EXPANDED:
	    cflags |= TCL_REG_EXPANDED;
	    break;
	case REGEXP_LINE:
	    cflags |= TCL_REG_NEWLINE;
	    break;
	case REGEXP_LINESTOP:
	    cflags |= TCL_REG_NLSTOP;
	    break;
	case REGEXP_LINEANCHOR:
	    cflags |= TCL_REG_NLANCH;
	    break;
	case REGEXP_START: {
	    int temp;
	    if (++i >= objc) {
		goto endOfForLoop;
	    }
	    if (TclGetIntForIndexM(interp, objv[i], 0, &temp) != TCL_OK) {
		goto optionError;
	    }
	    if (startIndex) {
		Tcl_DecrRefCount(startIndex);
	    }
	    startIndex = objv[i];
	    Tcl_IncrRefCount(startIndex);
	    break;
	}
	case REGEXP_LAST:
	    i++;
	    goto endOfForLoop;
	}
    }

  endOfForLoop:
    if ((objc - i) < (2 - about)) {
	Tcl_WrongNumArgs(interp, 1, objv,
	    "?switches? exp string ?matchVar? ?subMatchVar subMatchVar ...?");
	goto optionError;
    }
    objc -= i;
    objv += i;

    /*
     * Check if the user requested -inline, but specified match variables; a
     * no-no.
     */

    if (doinline && ((objc - 2) != 0)) {
	Tcl_AppendResult(interp, "regexp match variables not allowed"
		" when using -inline", NULL);
	goto optionError;
    }

    /*
     * Handle the odd about case separately.
     */

    if (about) {
	regExpr = Tcl_GetRegExpFromObj(interp, objv[0], cflags);
	if ((regExpr == NULL) || (TclRegAbout(interp, regExpr) < 0)) {
	optionError:
	    if (startIndex) {
		Tcl_DecrRefCount(startIndex);
	    }
	    return TCL_ERROR;
	}
	return TCL_OK;
    }

    /*
     * Get the length of the string that we are matching against so we can do
     * the termination test for -all matches. Do this before getting the
     * regexp to avoid shimmering problems.
     */

    objPtr = objv[1];
    stringLength = Tcl_GetCharLength(objPtr);

    if (startIndex) {
	TclGetIntForIndexM(NULL, startIndex, stringLength, &offset);
	Tcl_DecrRefCount(startIndex);
	if (offset < 0) {
	    offset = 0;
	}
    }

    regExpr = Tcl_GetRegExpFromObj(interp, objv[0], cflags);
    if (regExpr == NULL) {
	return TCL_ERROR;
    }

    if (offset > 0) {
	/*
	 * Add flag if using offset (string is part of a larger string), so
	 * that "^" won't match.
	 */

	eflags |= TCL_REG_NOTBOL;
    }

    objc -= 2;
    objv += 2;

    if (doinline) {
	/*
	 * Save all the subexpressions, as we will return them as a list
	 */

	numMatchesSaved = -1;
    } else {
	/*
	 * Save only enough subexpressions for matches we want to keep, expect
	 * in the case of -all, where we need to keep at least one to know
	 * where to move the offset.
	 */

	numMatchesSaved = (objc == 0) ? all : objc;
    }

    /*
     * The following loop is to handle multiple matches within the same source
     * string; each iteration handles one match. If "-all" hasn't been
     * specified then the loop body only gets executed once. We terminate the
     * loop when the starting offset is past the end of the string.
     */

    while (1) {
	match = Tcl_RegExpExecObj(interp, regExpr, objPtr,
		offset /* offset */, numMatchesSaved, eflags
		| ((offset > 0 &&
		(Tcl_GetUniChar(objPtr,offset-1) != (Tcl_UniChar)'\n'))
		? TCL_REG_NOTBOL : 0));

	if (match < 0) {
	    return TCL_ERROR;
	}

	if (match == 0) {
	    /*
	     * We want to set the value of the intepreter result only when
	     * this is the first time through the loop.
	     */

	    if (all <= 1) {
		/*
		 * If inlining, the interpreter's object result remains an
		 * empty list, otherwise set it to an integer object w/ value
		 * 0.
		 */

		if (!doinline) {
		    Tcl_SetObjResult(interp, Tcl_NewIntObj(0));
		}
		return TCL_OK;
	    }
	    break;
	}

	/*
	 * If additional variable names have been specified, return index
	 * information in those variables.
	 */

	Tcl_RegExpGetInfo(regExpr, &info);
	if (doinline) {
	    /*
	     * It's the number of substitutions, plus one for the matchVar at
	     * index 0
	     */

	    objc = info.nsubs + 1;
	    if (all <= 1) {
		resultPtr = Tcl_NewObj();
	    }
	}
	for (i = 0; i < objc; i++) {
	    Tcl_Obj *newPtr;

	    if (indices) {
		int start, end;
		Tcl_Obj *objs[2];

		/*
		 * Only adjust the match area if there was a match for that
		 * area. (Scriptics Bug 4391/SF Bug #219232)
		 */

		if (i <= info.nsubs && info.matches[i].start >= 0) {
		    start = offset + info.matches[i].start;
		    end = offset + info.matches[i].end;

		    /*
		     * Adjust index so it refers to the last character in the
		     * match instead of the first character after the match.
		     */

		    if (end >= offset) {
			end--;
		    }
		} else {
		    start = -1;
		    end = -1;
		}

		objs[0] = Tcl_NewLongObj(start);
		objs[1] = Tcl_NewLongObj(end);

		newPtr = Tcl_NewListObj(2, objs);
	    } else {
		if (i <= info.nsubs) {
		    newPtr = Tcl_GetRange(objPtr,
			    offset + info.matches[i].start,
			    offset + info.matches[i].end - 1);
		} else {
		    newPtr = Tcl_NewObj();
		}
	    }
	    if (doinline) {
		if (Tcl_ListObjAppendElement(interp, resultPtr, newPtr)
			!= TCL_OK) {
		    Tcl_DecrRefCount(newPtr);
		    Tcl_DecrRefCount(resultPtr);
		    return TCL_ERROR;
		}
	    } else {
		Tcl_Obj *valuePtr;
		valuePtr = Tcl_ObjSetVar2(interp, objv[i], NULL, newPtr, 0);
		if (valuePtr == NULL) {
		    Tcl_AppendResult(interp, "couldn't set variable \"",
			    TclGetString(objv[i]), "\"", NULL);
		    return TCL_ERROR;
		}
	    }
	}

	if (all == 0) {
	    break;
	}

	/*
	 * Adjust the offset to the character just after the last one in the
	 * matchVar and increment all to count how many times we are making a
	 * match. We always increment the offset by at least one to prevent
	 * endless looping (as in the case: regexp -all {a*} a). Otherwise,
	 * when we match the NULL string at the end of the input string, we
	 * will loop indefinately (because the length of the match is 0, so
	 * offset never changes).
	 */

	if (info.matches[0].end == 0) {
	    offset++;
	}
	offset += info.matches[0].end;
	all++;
	eflags |= TCL_REG_NOTBOL;
	if (offset >= stringLength) {
	    break;
	}
    }

    /*
     * Set the interpreter's object result to an integer object with value 1
     * if -all wasn't specified, otherwise it's all-1 (the number of times
     * through the while - 1).
     */

    if (doinline) {
	Tcl_SetObjResult(interp, resultPtr);
    } else {
	Tcl_SetObjResult(interp, Tcl_NewIntObj(all ? all-1 : 1));
    }
    return TCL_OK;
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_RegsubObjCmd --
 *
 *	This procedure is invoked to process the "regsub" Tcl command. See the
 *	user documentation for details on what it does.
 *
 * Results:
 *	A standard Tcl result.
 *
 * Side effects:
 *	See the user documentation.
 *
 *----------------------------------------------------------------------
 */

int
Tcl_RegsubObjCmd(
    ClientData dummy,		/* Not used. */
    Tcl_Interp *interp,		/* Current interpreter. */
    int objc,			/* Number of arguments. */
    Tcl_Obj *CONST objv[])	/* Argument objects. */
{
    int idx, result, cflags, all, wlen, wsublen, numMatches, offset;
    int start, end, subStart, subEnd, match;
    Tcl_RegExp regExpr;
    Tcl_RegExpInfo info;
    Tcl_Obj *resultPtr, *subPtr, *objPtr, *startIndex = NULL;
    Tcl_UniChar ch, *wsrc, *wfirstChar, *wstring, *wsubspec, *wend;

    static CONST char *options[] = {
	"-all",		"-nocase",	"-expanded",
	"-line",	"-linestop",	"-lineanchor",	"-start",
	"--",		NULL
    };
    enum options {
	REGSUB_ALL,	REGSUB_NOCASE,	REGSUB_EXPANDED,
	REGSUB_LINE,	REGSUB_LINESTOP, REGSUB_LINEANCHOR,	REGSUB_START,
	REGSUB_LAST
    };

    cflags = TCL_REG_ADVANCED;
    all = 0;
    offset = 0;
    resultPtr = NULL;

    for (idx = 1; idx < objc; idx++) {
	char *name;
	int index;

	name = TclGetString(objv[idx]);
	if (name[0] != '-') {
	    break;
	}
	if (Tcl_GetIndexFromObj(interp, objv[idx], options, "switch",
		TCL_EXACT, &index) != TCL_OK) {
	    goto optionError;
	}
	switch ((enum options) index) {
	case REGSUB_ALL:
	    all = 1;
	    break;
	case REGSUB_NOCASE:
	    cflags |= TCL_REG_NOCASE;
	    break;
	case REGSUB_EXPANDED:
	    cflags |= TCL_REG_EXPANDED;
	    break;
	case REGSUB_LINE:
	    cflags |= TCL_REG_NEWLINE;
	    break;
	case REGSUB_LINESTOP:
	    cflags |= TCL_REG_NLSTOP;
	    break;
	case REGSUB_LINEANCHOR:
	    cflags |= TCL_REG_NLANCH;
	    break;
	case REGSUB_START: {
	    int temp;
	    if (++idx >= objc) {
		goto endOfForLoop;
	    }
	    if (TclGetIntForIndexM(interp, objv[idx], 0, &temp) != TCL_OK) {
		goto optionError;
	    }
	    if (startIndex) {
		Tcl_DecrRefCount(startIndex);
	    }
	    startIndex = objv[idx];
	    Tcl_IncrRefCount(startIndex);
	    break;
	}
	case REGSUB_LAST:
	    idx++;
	    goto endOfForLoop;
	}
    }

  endOfForLoop:
    if (objc-idx < 3 || objc-idx > 4) {
	Tcl_WrongNumArgs(interp, 1, objv,
		"?switches? exp string subSpec ?varName?");
    optionError:
	if (startIndex) {
	    Tcl_DecrRefCount(startIndex);
	}
	return TCL_ERROR;
    }

    objc -= idx;
    objv += idx;

    if (startIndex) {
	int stringLength = Tcl_GetCharLength(objv[1]);

	TclGetIntForIndexM(NULL, startIndex, stringLength, &offset);
	Tcl_DecrRefCount(startIndex);
	if (offset < 0) {
	    offset = 0;
	}
    }

    if (all && (offset == 0)
	    && (strpbrk(TclGetString(objv[2]), "&\\") == NULL)
	    && (strpbrk(TclGetString(objv[0]), "*+?{}()[].\\|^$") == NULL)) {
	/*
	 * This is a simple one pair string map situation. We make use of a
	 * slightly modified version of the one pair STR_MAP code.
	 */

	int slen, nocase;
	int (*strCmpFn)(CONST Tcl_UniChar*,CONST Tcl_UniChar*,unsigned long);
	Tcl_UniChar *p, wsrclc;

	numMatches = 0;
	nocase = (cflags & TCL_REG_NOCASE);
	strCmpFn = nocase ? Tcl_UniCharNcasecmp : Tcl_UniCharNcmp;

	wsrc = Tcl_GetUnicodeFromObj(objv[0], &slen);
	wstring = Tcl_GetUnicodeFromObj(objv[1], &wlen);
	wsubspec = Tcl_GetUnicodeFromObj(objv[2], &wsublen);
	wend = wstring + wlen - (slen ? slen - 1 : 0);
	result = TCL_OK;

	if (slen == 0) {
	    /*
	     * regsub behavior for "" matches between each character. 'string
	     * map' skips the "" case.
	     */

	    if (wstring < wend) {
		resultPtr = Tcl_NewUnicodeObj(wstring, 0);
		Tcl_IncrRefCount(resultPtr);
		for (; wstring < wend; wstring++) {
		    Tcl_AppendUnicodeToObj(resultPtr, wsubspec, wsublen);
		    Tcl_AppendUnicodeToObj(resultPtr, wstring, 1);
		    numMatches++;
		}
		wlen = 0;
	    }
	} else {
	    wsrclc = Tcl_UniCharToLower(*wsrc);
	    for (p = wfirstChar = wstring; wstring < wend; wstring++) {
		if ((*wstring == *wsrc ||
			(nocase && Tcl_UniCharToLower(*wstring)==wsrclc)) &&
			(slen==1 || (strCmpFn(wstring, wsrc,
				(unsigned long) slen) == 0))) {
		    if (numMatches == 0) {
			resultPtr = Tcl_NewUnicodeObj(wstring, 0);
			Tcl_IncrRefCount(resultPtr);
		    }
		    if (p != wstring) {
			Tcl_AppendUnicodeToObj(resultPtr, p, wstring - p);
			p = wstring + slen;
		    } else {
			p += slen;
		    }
		    wstring = p - 1;

		    Tcl_AppendUnicodeToObj(resultPtr, wsubspec, wsublen);
		    numMatches++;
		}
	    }
	    if (numMatches) {
		wlen    = wfirstChar + wlen - p;
		wstring = p;
	    }
	}
	objPtr = NULL;
	subPtr = NULL;
	goto regsubDone;
    }

    regExpr = Tcl_GetRegExpFromObj(interp, objv[0], cflags);
    if (regExpr == NULL) {
	return TCL_ERROR;
    }

    /*
     * Make sure to avoid problems where the objects are shared. This can
     * cause RegExpObj <> UnicodeObj shimmering that causes data corruption.
     * [Bug #461322]
     */

    if (objv[1] == objv[0]) {
	objPtr = Tcl_DuplicateObj(objv[1]);
    } else {
	objPtr = objv[1];
    }
    wstring = Tcl_GetUnicodeFromObj(objPtr, &wlen);
    if (objv[2] == objv[0]) {
	subPtr = Tcl_DuplicateObj(objv[2]);
    } else {
	subPtr = objv[2];
    }
    wsubspec = Tcl_GetUnicodeFromObj(subPtr, &wsublen);

    result = TCL_OK;

    /*
     * The following loop is to handle multiple matches within the same source
     * string; each iteration handles one match and its corresponding
     * substitution. If "-all" hasn't been specified then the loop body only
     * gets executed once. We must use 'offset <= wlen' in particular for the
     * case where the regexp pattern can match the empty string - this is
     * useful when doing, say, 'regsub -- ^ $str ...' when $str might be
     * empty.
     */

    numMatches = 0;
    for ( ; offset <= wlen; ) {

	/*
	 * The flags argument is set if string is part of a larger string, so
	 * that "^" won't match.
	 */

	match = Tcl_RegExpExecObj(interp, regExpr, objPtr, offset,
		10 /* matches */, ((offset > 0 &&
		(wstring[offset-1] != (Tcl_UniChar)'\n'))
		? TCL_REG_NOTBOL : 0));

	if (match < 0) {
	    result = TCL_ERROR;
	    goto done;
	}
	if (match == 0) {
	    break;
	}
	if (numMatches == 0) {
	    resultPtr = Tcl_NewUnicodeObj(wstring, 0);
	    Tcl_IncrRefCount(resultPtr);
	    if (offset > 0) {
		/*
		 * Copy the initial portion of the string in if an offset was
		 * specified.
		 */

		Tcl_AppendUnicodeToObj(resultPtr, wstring, offset);
	    }
	}
	numMatches++;

	/*
	 * Copy the portion of the source string before the match to the
	 * result variable.
	 */

	Tcl_RegExpGetInfo(regExpr, &info);
	start = info.matches[0].start;
	end = info.matches[0].end;
	Tcl_AppendUnicodeToObj(resultPtr, wstring + offset, start);

	/*
	 * Append the subSpec argument to the variable, making appropriate
	 * substitutions. This code is a bit hairy because of the backslash
	 * conventions and because the code saves up ranges of characters in
	 * subSpec to reduce the number of calls to Tcl_SetVar.
	 */

	wsrc = wfirstChar = wsubspec;
	wend = wsubspec + wsublen;
	for (ch = *wsrc; wsrc != wend; wsrc++, ch = *wsrc) {
	    if (ch == '&') {
		idx = 0;
	    } else if (ch == '\\') {
		ch = wsrc[1];
		if ((ch >= '0') && (ch <= '9')) {
		    idx = ch - '0';
		} else if ((ch == '\\') || (ch == '&')) {
		    *wsrc = ch;
		    Tcl_AppendUnicodeToObj(resultPtr, wfirstChar,
			    wsrc - wfirstChar + 1);
		    *wsrc = '\\';
		    wfirstChar = wsrc + 2;
		    wsrc++;
		    continue;
		} else {
		    continue;
		}
	    } else {
		continue;
	    }

	    if (wfirstChar != wsrc) {
		Tcl_AppendUnicodeToObj(resultPtr, wfirstChar,
			wsrc - wfirstChar);
	    }

	    if (idx <= info.nsubs) {
		subStart = info.matches[idx].start;
		subEnd = info.matches[idx].end;
		if ((subStart >= 0) && (subEnd >= 0)) {
		    Tcl_AppendUnicodeToObj(resultPtr,
			    wstring + offset + subStart, subEnd - subStart);
		}
	    }

	    if (*wsrc == '\\') {
		wsrc++;
	    }
	    wfirstChar = wsrc + 1;
	}

	if (wfirstChar != wsrc) {
	    Tcl_AppendUnicodeToObj(resultPtr, wfirstChar, wsrc - wfirstChar);
	}

	if (end == 0) {
	    /*
	     * Always consume at least one character of the input string in
	     * order to prevent infinite loops.
	     */

	    if (offset < wlen) {
		Tcl_AppendUnicodeToObj(resultPtr, wstring + offset, 1);
	    }
	    offset++;
	} else {
	    offset += end;
	    if (start == end) {
		/*
		 * We matched an empty string, which means we must go forward
		 * one more step so we don't match again at the same spot.
		 */

		if (offset < wlen) {
		    Tcl_AppendUnicodeToObj(resultPtr, wstring + offset, 1);
		}
		offset++;
	    }
	}
	if (!all) {
	    break;
	}
    }

    /*
     * Copy the portion of the source string after the last match to the
     * result variable.
     */

  regsubDone:
    if (numMatches == 0) {
	/*
	 * On zero matches, just ignore the offset, since it shouldn't matter
	 * to us in this case, and the user may have skewed it.
	 */

	resultPtr = objv[1];
	Tcl_IncrRefCount(resultPtr);
    } else if (offset < wlen) {
	Tcl_AppendUnicodeToObj(resultPtr, wstring + offset, wlen - offset);
    }
    if (objc == 4) {
	if (Tcl_ObjSetVar2(interp, objv[3], NULL, resultPtr, 0) == NULL) {
	    Tcl_AppendResult(interp, "couldn't set variable \"",
		    TclGetString(objv[3]), "\"", NULL);
	    result = TCL_ERROR;
	} else {
	    /*
	     * Set the interpreter's object result to an integer object
	     * holding the number of matches.
	     */

	    Tcl_SetObjResult(interp, Tcl_NewIntObj(numMatches));
	}
    } else {
	/*
	 * No varname supplied, so just return the modified string.
	 */

	Tcl_SetObjResult(interp, resultPtr);
    }

  done:
    if (objPtr && (objv[1] == objv[0])) {
	Tcl_DecrRefCount(objPtr);
    }
    if (subPtr && (objv[2] == objv[0])) {
	Tcl_DecrRefCount(subPtr);
    }
    if (resultPtr) {
	Tcl_DecrRefCount(resultPtr);
    }
    return result;
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_RenameObjCmd --
 *
 *	This procedure is invoked to process the "rename" Tcl command. See the
 *	user documentation for details on what it does.
 *
 * Results:
 *	A standard Tcl object result.
 *
 * Side effects:
 *	See the user documentation.
 *
 *----------------------------------------------------------------------
 */

int
Tcl_RenameObjCmd(
    ClientData dummy,		/* Arbitrary value passed to the command. */
    Tcl_Interp *interp,		/* Current interpreter. */
    int objc,			/* Number of arguments. */
    Tcl_Obj *CONST objv[])	/* Argument objects. */
{
    char *oldName, *newName;

    if (objc != 3) {
	Tcl_WrongNumArgs(interp, 1, objv, "oldName newName");
	return TCL_ERROR;
    }

    oldName = TclGetString(objv[1]);
    newName = TclGetString(objv[2]);
    return TclRenameCommand(interp, oldName, newName);
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_ReturnObjCmd --
 *
 *	This object-based procedure is invoked to process the "return" Tcl
 *	command. See the user documentation for details on what it does.
 *
 * Results:
 *	A standard Tcl object result.
 *
 * Side effects:
 *	See the user documentation.
 *
 *----------------------------------------------------------------------
 */

int
Tcl_ReturnObjCmd(
    ClientData dummy,		/* Not used. */
    Tcl_Interp *interp,		/* Current interpreter. */
    int objc,			/* Number of arguments. */
    Tcl_Obj *CONST objv[])	/* Argument objects. */
{
    int code, level;
    Tcl_Obj *returnOpts;

    /*
     * General syntax: [return ?-option value ...? ?result?]
     * An even number of words means an explicit result argument is present.
     */

    int explicitResult = (0 == (objc % 2));
    int numOptionWords = objc - 1 - explicitResult;

    if (TCL_ERROR == TclMergeReturnOptions(interp, numOptionWords, objv+1,
	    &returnOpts, &code, &level)) {
	return TCL_ERROR;
    }

    code = TclProcessReturn(interp, code, level, returnOpts);
    if (explicitResult) {
	Tcl_SetObjResult(interp, objv[objc-1]);
    }
    return code;
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_SourceObjCmd --
 *
 *	This procedure is invoked to process the "source" Tcl command. See the
 *	user documentation for details on what it does.
 *
 * Results:
 *	A standard Tcl object result.
 *
 * Side effects:
 *	See the user documentation.
 *
 *----------------------------------------------------------------------
 */

int
Tcl_SourceObjCmd(
    ClientData dummy,		/* Not used. */
    Tcl_Interp *interp,		/* Current interpreter. */
    int objc,			/* Number of arguments. */
    Tcl_Obj *CONST objv[])	/* Argument objects. */
{
    CONST char *encodingName = NULL;
    Tcl_Obj *fileName;

    if (objc != 2 && objc !=4) {
	Tcl_WrongNumArgs(interp, 1, objv, "?-encoding name? fileName");
	return TCL_ERROR;
    }

    fileName = objv[objc-1];

    if (objc == 4) {
	static CONST char *options[] = {
	    "-encoding", NULL
	};
	int index;

	if (TCL_ERROR == Tcl_GetIndexFromObj(interp, objv[1], options,
		"option", TCL_EXACT, &index)) {
	    return TCL_ERROR;
	}
	encodingName = TclGetString(objv[2]);
    }

    return Tcl_FSEvalFileEx(interp, fileName, encodingName);
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_SplitObjCmd --
 *
 *	This procedure is invoked to process the "split" Tcl command. See the
 *	user documentation for details on what it does.
 *
 * Results:
 *	A standard Tcl result.
 *
 * Side effects:
 *	See the user documentation.
 *
 *----------------------------------------------------------------------
 */

int
Tcl_SplitObjCmd(
    ClientData dummy,		/* Not used. */
    Tcl_Interp *interp,		/* Current interpreter. */
    int objc,			/* Number of arguments. */
    Tcl_Obj *CONST objv[])	/* Argument objects. */
{
    Tcl_UniChar ch;
    int len;
    char *splitChars, *stringPtr, *end;
    int splitCharLen, stringLen;
    Tcl_Obj *listPtr, *objPtr;

    if (objc == 2) {
	splitChars = " \n\t\r";
	splitCharLen = 4;
    } else if (objc == 3) {
	splitChars = TclGetStringFromObj(objv[2], &splitCharLen);
    } else {
	Tcl_WrongNumArgs(interp, 1, objv, "string ?splitChars?");
	return TCL_ERROR;
    }

    stringPtr = TclGetStringFromObj(objv[1], &stringLen);
    end = stringPtr + stringLen;
    listPtr = Tcl_NewObj();

    if (stringLen == 0) {
	/*
	 * Do nothing.
	 */
    } else if (splitCharLen == 0) {
	Tcl_HashTable charReuseTable;
	Tcl_HashEntry *hPtr;
	int isNew;

	/*
	 * Handle the special case of splitting on every character.
	 *
	 * Uses a hash table to ensure that each kind of character has only
	 * one Tcl_Obj instance (multiply-referenced) in the final list. This
	 * is a *major* win when splitting on a long string (especially in the
	 * megabyte range!) - DKF
	 */

	Tcl_InitHashTable(&charReuseTable, TCL_ONE_WORD_KEYS);

	for ( ; stringPtr < end; stringPtr += len) {
	    len = TclUtfToUniChar(stringPtr, &ch);

	    /*
	     * Assume Tcl_UniChar is an integral type...
	     */

	    hPtr = Tcl_CreateHashEntry(&charReuseTable, (char*)0+ch, &isNew);
	    if (isNew) {
		TclNewStringObj(objPtr, stringPtr, len);

		/*
		 * Don't need to fiddle with refcount...
		 */

		Tcl_SetHashValue(hPtr, (ClientData) objPtr);
	    } else {
		objPtr = (Tcl_Obj *) Tcl_GetHashValue(hPtr);
	    }
	    Tcl_ListObjAppendElement(NULL, listPtr, objPtr);
	}
	Tcl_DeleteHashTable(&charReuseTable);

    } else if (splitCharLen == 1) {
	char *p;

	/*
	 * Handle the special case of splitting on a single character. This is
	 * only true for the one-char ASCII case, as one unicode char is > 1
	 * byte in length.
	 */

	while (*stringPtr && (p=strchr(stringPtr,(int)*splitChars)) != NULL) {
	    objPtr = Tcl_NewStringObj(stringPtr, p - stringPtr);
	    Tcl_ListObjAppendElement(NULL, listPtr, objPtr);
	    stringPtr = p + 1;
	}
	TclNewStringObj(objPtr, stringPtr, end - stringPtr);
	Tcl_ListObjAppendElement(NULL, listPtr, objPtr);
    } else {
	char *element, *p, *splitEnd;
	int splitLen;
	Tcl_UniChar splitChar;

	/*
	 * Normal case: split on any of a given set of characters. Discard
	 * instances of the split characters.
	 */

	splitEnd = splitChars + splitCharLen;

	for (element = stringPtr; stringPtr < end; stringPtr += len) {
	    len = TclUtfToUniChar(stringPtr, &ch);
	    for (p = splitChars; p < splitEnd; p += splitLen) {
		splitLen = TclUtfToUniChar(p, &splitChar);
		if (ch == splitChar) {
		    TclNewStringObj(objPtr, element, stringPtr - element);
		    Tcl_ListObjAppendElement(NULL, listPtr, objPtr);
		    element = stringPtr + len;
		    break;
		}
	    }
	}

	TclNewStringObj(objPtr, element, stringPtr - element);
	Tcl_ListObjAppendElement(NULL, listPtr, objPtr);
    }
    Tcl_SetObjResult(interp, listPtr);
    return TCL_OK;
}

/*
 *----------------------------------------------------------------------
 *
 * StringFirstCmd --
 *
 *	This procedure is invoked to process the "string first" Tcl command.
 *	See the user documentation for details on what it does. Note that this
 *	command only functions correctly on properly formed Tcl UTF strings.
 *
 * Results:
 *	A standard Tcl result.
 *
 * Side effects:
 *	See the user documentation.
 *
 *----------------------------------------------------------------------
 */

static int
StringFirstCmd(
    ClientData dummy,		/* Not used. */
    Tcl_Interp *interp,		/* Current interpreter. */
    int objc,			/* Number of arguments. */
    Tcl_Obj *const objv[])	/* Argument objects. */
{
    Tcl_UniChar *ustring1, *ustring2;
    int match, start, length1, length2;

    if (objc < 3 || objc > 4) {
	Tcl_WrongNumArgs(interp, 1, objv,
		"needleString haystackString ?startIndex?");
	return TCL_ERROR;
    }

    /*
     * We are searching string2 for the sequence string1.
     */

    match = -1;
    start = 0;
    length2 = -1;

    ustring1 = Tcl_GetUnicodeFromObj(objv[1], &length1);
    ustring2 = Tcl_GetUnicodeFromObj(objv[2], &length2);

    if (objc == 4) {
	/*
	 * If a startIndex is specified, we will need to fast forward to that
	 * point in the string before we think about a match.
	 */

	if (TclGetIntForIndexM(interp, objv[3], length2-1, &start) != TCL_OK){
	    return TCL_ERROR;
	}

	/*
	 * Reread to prevent shimmering problems.
	 */

	ustring1 = Tcl_GetUnicodeFromObj(objv[1], &length1);
	ustring2 = Tcl_GetUnicodeFromObj(objv[2], &length2);

	if (start >= length2) {
	    goto str_first_done;
	} else if (start > 0) {
	    ustring2 += start;
	    length2 -= start;
	} else if (start < 0) {
	    /*
	     * Invalid start index mapped to string start; Bug #423581
	     */

	    start = 0;
	}
    }

    if (length1 > 0) {
	register Tcl_UniChar *p, *end;

	end = ustring2 + length2 - length1 + 1;
	for (p = ustring2;  p < end;  p++) {
	    /*
	     * Scan forward to find the first character.
	     */

	    if ((*p == *ustring1) && (TclUniCharNcmp(ustring1, p,
		    (unsigned long) length1) == 0)) {
		match = p - ustring2;
		break;
	    }
	}
    }

    /*
     * Compute the character index of the matching string by counting the
     * number of characters before the match.
     */

    if ((match != -1) && (objc == 4)) {
	match += start;
    }

  str_first_done:
    Tcl_SetObjResult(interp, Tcl_NewIntObj(match));
    return TCL_OK;
}

/*
 *----------------------------------------------------------------------
 *
 * StringLastCmd --
 *
 *	This procedure is invoked to process the "string last" Tcl command.
 *	See the user documentation for details on what it does. Note that this
 *	command only functions correctly on properly formed Tcl UTF strings.
 *
 * Results:
 *	A standard Tcl result.
 *
 * Side effects:
 *	See the user documentation.
 *
 *----------------------------------------------------------------------
 */

static int
StringLastCmd(
    ClientData dummy,		/* Not used. */
    Tcl_Interp *interp,		/* Current interpreter. */
    int objc,			/* Number of arguments. */
    Tcl_Obj *const objv[])	/* Argument objects. */
{
    Tcl_UniChar *ustring1, *ustring2, *p;
    int match, start, length1, length2;

    if (objc < 3 || objc > 4) {
	Tcl_WrongNumArgs(interp, 1, objv,
		"needleString haystackString ?startIndex?");
	return TCL_ERROR;
    }

    /*
     * We are searching string2 for the sequence string1.
     */

    match = -1;
    start = 0;
    length2 = -1;

    ustring1 = Tcl_GetUnicodeFromObj(objv[1], &length1);
    ustring2 = Tcl_GetUnicodeFromObj(objv[2], &length2);

    if (objc == 4) {
	/*
	 * If a startIndex is specified, we will need to restrict the string
	 * range to that char index in the string
	 */

	if (TclGetIntForIndexM(interp, objv[3], length2-1, &start) != TCL_OK){
	    return TCL_ERROR;
	}

	/*
	 * Reread to prevent shimmering problems.
	 */

	ustring1 = Tcl_GetUnicodeFromObj(objv[1], &length1);
	ustring2 = Tcl_GetUnicodeFromObj(objv[2], &length2);

	if (start < 0) {
	    goto str_last_done;
	} else if (start < length2) {
	    p = ustring2 + start + 1 - length1;
	} else {
	    p = ustring2 + length2 - length1;
	}
    } else {
	p = ustring2 + length2 - length1;
    }

    if (length1 > 0) {
	for (; p >= ustring2; p--) {
	    /*
	     * Scan backwards to find the first character.
	     */

	    if ((*p == *ustring1) && !memcmp(ustring1, p,
		    sizeof(Tcl_UniChar) * (size_t)length1)) {
		match = p - ustring2;
		break;
	    }
	}
    }

  str_last_done:
    Tcl_SetObjResult(interp, Tcl_NewIntObj(match));
    return TCL_OK;
}

/*
 *----------------------------------------------------------------------
 *
 * StringIndexCmd --
 *
 *	This procedure is invoked to process the "string index" Tcl command.
 *	See the user documentation for details on what it does. Note that this
 *	command only functions correctly on properly formed Tcl UTF strings.
 *
 * Results:
 *	A standard Tcl result.
 *
 * Side effects:
 *	See the user documentation.
 *
 *----------------------------------------------------------------------
 */

static int
StringIndexCmd(
    ClientData dummy,		/* Not used. */
    Tcl_Interp *interp,		/* Current interpreter. */
    int objc,			/* Number of arguments. */
    Tcl_Obj *const objv[])	/* Argument objects. */
{
    int length, index;

    if (objc != 3) {
	Tcl_WrongNumArgs(interp, 1, objv, "string charIndex");
	return TCL_ERROR;
    }

    /*
     * If we have a ByteArray object, avoid indexing in the Utf string since
     * the byte array contains one byte per character. Otherwise, use the
     * Unicode string rep to get the index'th char.
     */

    if (objv[1]->typePtr == &tclByteArrayType) {
	const unsigned char *string =
		Tcl_GetByteArrayFromObj(objv[1], &length);

	if (TclGetIntForIndexM(interp, objv[2], length-1, &index) != TCL_OK){
	    return TCL_ERROR;
	}
	string = Tcl_GetByteArrayFromObj(objv[1], &length);
	if ((index >= 0) && (index < length)) {
	    Tcl_SetObjResult(interp, Tcl_NewByteArrayObj(string + index, 1));
	}
    } else {
	/*
	 * Get Unicode char length to calulate what 'end' means.
	 */

	length = Tcl_GetCharLength(objv[1]);

	if (TclGetIntForIndexM(interp, objv[2], length-1, &index) != TCL_OK){
	    return TCL_ERROR;
	}
	if ((index >= 0) && (index < length)) {
	    char buf[TCL_UTF_MAX];
	    Tcl_UniChar ch;

	    ch = Tcl_GetUniChar(objv[1], index);
	    length = Tcl_UniCharToUtf(ch, buf);
	    Tcl_SetObjResult(interp, Tcl_NewStringObj(buf, length));
	}
    }
    return TCL_OK;
}

/*
 *----------------------------------------------------------------------
 *
 * StringIsCmd --
 *
 *	This procedure is invoked to process the "string is" Tcl command. See
 *	the user documentation for details on what it does. Note that this
 *	command only functions correctly on properly formed Tcl UTF strings.
 *
 * Results:
 *	A standard Tcl result.
 *
 * Side effects:
 *	See the user documentation.
 *
 *----------------------------------------------------------------------
 */

static int
StringIsCmd(
    ClientData dummy,		/* Not used. */
    Tcl_Interp *interp,		/* Current interpreter. */
    int objc,			/* Number of arguments. */
    Tcl_Obj *const objv[])	/* Argument objects. */
{
    const char *string1, *string2, *end, *stop;
    Tcl_UniChar ch;
    int (*chcomp)(int) = NULL;	/* The UniChar comparison function. */
    int i, failat = 0, result = 1, strict = 0, index, length1, length2;
    Tcl_Obj *objPtr, *failVarObj = NULL;
    Tcl_WideInt w;

    static const char *isOptions[] = {
	"alnum",	"alpha",	"ascii",	"control",
	"boolean",	"digit",	"double",	"false",
	"graph",	"integer",	"list",		"lower",
	"print",	"punct",	"space",	"true",
	"upper",	"wideinteger",	"wordchar",	"xdigit",
	NULL
    };
    enum isOptions {
	STR_IS_ALNUM, STR_IS_ALPHA,	STR_IS_ASCII,  STR_IS_CONTROL,
	STR_IS_BOOL,  STR_IS_DIGIT,	STR_IS_DOUBLE, STR_IS_FALSE,
	STR_IS_GRAPH, STR_IS_INT,	STR_IS_LIST,   STR_IS_LOWER,
	STR_IS_PRINT, STR_IS_PUNCT, STR_IS_SPACE,  STR_IS_TRUE,
	STR_IS_UPPER, STR_IS_WIDE,	STR_IS_WORD,   STR_IS_XDIGIT
    };

    if (objc < 3 || objc > 6) {
	Tcl_WrongNumArgs(interp, 1, objv,
		"class ?-strict? ?-failindex var? str");
	return TCL_ERROR;
    }
    if (Tcl_GetIndexFromObj(interp, objv[1], isOptions, "class", 0,
	    &index) != TCL_OK) {
	return TCL_ERROR;
    }

    if (objc != 3) {
	for (i = 2; i < objc-1; i++) {
	    string2 = TclGetStringFromObj(objv[i], &length2);
	    if ((length2 > 1) &&
		    strncmp(string2, "-strict", (size_t) length2) == 0) {
		strict = 1;
	    } else if ((length2 > 1) &&
		    strncmp(string2, "-failindex", (size_t)length2) == 0){
		if (i+1 >= objc-1) {
		    Tcl_WrongNumArgs(interp, 2, objv,
			    "?-strict? ?-failindex var? str");
		    return TCL_ERROR;
		}
		failVarObj = objv[++i];
	    } else {
		Tcl_AppendResult(interp, "bad option \"", string2,
			"\": must be -strict or -failindex", NULL);
		return TCL_ERROR;
	    }
	}
    }

    /*
     * We get the objPtr so that we can short-cut for some classes by checking
     * the object type (int and double), but we need the string otherwise,
     * because we don't want any conversion of type occuring (as, for example,
     * Tcl_Get*FromObj would do).
     */

    objPtr = objv[objc-1];
    string1 = TclGetStringFromObj(objPtr, &length1);
    if (length1 == 0 && index != STR_IS_LIST) {
	if (strict) {
	    result = 0;
	}
	goto str_is_done;
    }
    end = string1 + length1;

    /*
     * When entering here, result == 1 and failat == 0.
     */

    switch ((enum isOptions) index) {
    case STR_IS_ALNUM:
	chcomp = Tcl_UniCharIsAlnum;
	break;
    case STR_IS_ALPHA:
	chcomp = Tcl_UniCharIsAlpha;
	break;
    case STR_IS_ASCII:
	chcomp = UniCharIsAscii;
	break;
    case STR_IS_BOOL:
    case STR_IS_TRUE:
    case STR_IS_FALSE:
	if (TCL_OK != Tcl_ConvertToType(NULL, objPtr, &tclBooleanType)) {
	    result = 0;
	} else if (((index == STR_IS_TRUE) &&
		objPtr->internalRep.longValue == 0)
	    || ((index == STR_IS_FALSE) &&
		objPtr->internalRep.longValue != 0)) {
	    result = 0;
	}
	break;
    case STR_IS_CONTROL:
	chcomp = Tcl_UniCharIsControl;
	break;
    case STR_IS_DIGIT:
	chcomp = Tcl_UniCharIsDigit;
	break;
    case STR_IS_DOUBLE: {
	/* TODO */
	if ((objPtr->typePtr == &tclDoubleType) ||
		(objPtr->typePtr == &tclIntType) ||
#ifndef NO_WIDE_TYPE
		(objPtr->typePtr == &tclWideIntType) ||
#endif
		(objPtr->typePtr == &tclBignumType)) {
	    break;
	}
	if (TclParseNumber(NULL, objPtr, NULL, NULL, -1,
		(const char **) &stop, 0) != TCL_OK) {
	    result = 0;
	    failat = 0;
	} else {
	    failat = stop - string1;
	    if (stop < end) {
		result = 0;
		TclFreeIntRep(objPtr);
		objPtr->typePtr = NULL;
	    }
	}
	break;
    }
    case STR_IS_GRAPH:
	chcomp = Tcl_UniCharIsGraph;
	break;
    case STR_IS_INT:
	if (TCL_OK == TclGetIntFromObj(NULL, objPtr, &i)) {
	    break;
	}
	goto failedIntParse;
    case STR_IS_WIDE:
	if (TCL_OK == Tcl_GetWideIntFromObj(NULL, objPtr, &w)) {
	    break;
	}

    failedIntParse:
	result = 0;

	if (failVarObj == NULL) {
	    /*
	     * Don't bother computing the failure point if we're not going to
	     * return it.
	     */

	    break;
	}
	if (TclParseNumber(NULL, objPtr, NULL, NULL, -1,
		(const char **) &stop, TCL_PARSE_INTEGER_ONLY) == TCL_OK) {
	    if (stop == end) {
		/*
		 * Entire string parses as an integer, but rejected by
		 * Tcl_Get(Wide)IntFromObj() so we must have overflowed the
		 * target type, and our convention is to return failure at
		 * index -1 in that situation.
		 */

		failat = -1;
	    } else {
		/*
		 * Some prefix parsed as an integer, but not the whole string,
		 * so return failure index as the point where parsing stopped.
		 * Clear out the internal rep, since keeping it would leave
		 * *objPtr in an inconsistent state.
		 */

		failat = stop - string1;
		TclFreeIntRep(objPtr);
		objPtr->typePtr = NULL;
	    }
	} else {
	    /*
	     * No prefix is a valid integer. Fail at beginning.
	     */

	    failat = 0;
	}
	break;
    case STR_IS_LIST:
	/*
	 * We ignore the strictness here, since empty strings are always
	 * well-formed lists.
	 */

	if (TCL_OK == TclListObjLength(NULL, objPtr, &length2)) {
	    break;
	}

	if (failVarObj != NULL) {
	    /*
	     * Need to figure out where the list parsing failed, which is
	     * fairly expensive. This is adapted from the core of
	     * SetListFromAny().
	     */

	    const char *elemStart, *nextElem, *limit;
	    int lenRemain, elemSize, hasBrace;
	    register const char *p;

	    limit = string1 + length1;
	    failat = -1;
	    for (p=string1, lenRemain=length1; lenRemain > 0;
		    p=nextElem, lenRemain=limit-nextElem) {
		if (TCL_ERROR == TclFindElement(NULL, p, lenRemain,
			&elemStart, &nextElem, &elemSize, &hasBrace)) {
		    Tcl_Obj *tmpStr;

		    /*
		     * This is the simplest way of getting the number of
		     * characters parsed. Note that this is not the same as
		     * the number of bytes when parsing strings with non-ASCII
		     * characters in them.
		     *
		     * Skip leading spaces first. This is only really an issue
		     * if it is the first "element" that has the failure.
		     */

		    while (isspace(UCHAR(*p))) {		/* INTL: ? */
			p++;
		    }
		    TclNewStringObj(tmpStr, string1, p-string1);
		    failat = Tcl_GetCharLength(tmpStr);
		    TclDecrRefCount(tmpStr);
		    break;
		}
	    }
	}
	result = 0;
	break;
    case STR_IS_LOWER:
	chcomp = Tcl_UniCharIsLower;
	break;
    case STR_IS_PRINT:
	chcomp = Tcl_UniCharIsPrint;
	break;
    case STR_IS_PUNCT:
	chcomp = Tcl_UniCharIsPunct;
	break;
    case STR_IS_SPACE:
	chcomp = Tcl_UniCharIsSpace;
	break;
    case STR_IS_UPPER:
	chcomp = Tcl_UniCharIsUpper;
	break;
    case STR_IS_WORD:
	chcomp = Tcl_UniCharIsWordChar;
	break;
    case STR_IS_XDIGIT:
	for (; string1 < end; string1++, failat++) {
	    /* INTL: We assume unicode is bad for this class. */
	    if ((*((unsigned char *)string1) >= 0xC0) ||
		    !isxdigit(*(unsigned char *)string1)) {
		result = 0;
		break;
	    }
	}
	break;
    }
    if (chcomp != NULL) {
	for (; string1 < end; string1 += length2, failat++) {
	    length2 = TclUtfToUniChar(string1, &ch);
	    if (!chcomp(ch)) {
		result = 0;
		break;
	    }
	}
    }

    /*
     * Only set the failVarObj when we will return 0 and we have indicated a
     * valid fail index (>= 0).
     */

 str_is_done:
    if ((result == 0) && (failVarObj != NULL) &&
	Tcl_ObjSetVar2(interp, failVarObj, NULL, Tcl_NewIntObj(failat),
		TCL_LEAVE_ERR_MSG) == NULL) {
	return TCL_ERROR;
    }
    Tcl_SetObjResult(interp, Tcl_NewBooleanObj(result));
    return TCL_OK;
}

static int
UniCharIsAscii(
    int character)
{
    return (character >= 0) && (character < 0x80);
}

/*
 *----------------------------------------------------------------------
 *
 * StringMapCmd --
 *
 *	This procedure is invoked to process the "string map" Tcl command. See
 *	the user documentation for details on what it does. Note that this
 *	command only functions correctly on properly formed Tcl UTF strings.
 *
 * Results:
 *	A standard Tcl result.
 *
 * Side effects:
 *	See the user documentation.
 *
 *----------------------------------------------------------------------
 */

static int
StringMapCmd(
    ClientData dummy,		/* Not used. */
    Tcl_Interp *interp,		/* Current interpreter. */
    int objc,			/* Number of arguments. */
    Tcl_Obj *const objv[])	/* Argument objects. */
{
    int length1, length2, mapElemc, index;
    int nocase = 0, mapWithDict = 0, copySource = 0;
    Tcl_Obj **mapElemv, *sourceObj, *resultPtr;
    Tcl_UniChar *ustring1, *ustring2, *p, *end;
    int (*strCmpFn)(const Tcl_UniChar*, const Tcl_UniChar*, unsigned long);

    if (objc < 3 || objc > 4) {
	Tcl_WrongNumArgs(interp, 1, objv, "?-nocase? charMap string");
	return TCL_ERROR;
    }

    if (objc == 4) {
	const char *string = TclGetStringFromObj(objv[1], &length2);

	if ((length2 > 1) &&
		strncmp(string, "-nocase", (size_t) length2) == 0) {
	    nocase = 1;
	} else {
	    Tcl_AppendResult(interp, "bad option \"", string,
		    "\": must be -nocase", NULL);
	    return TCL_ERROR;
	}
    }

    /*
     * This test is tricky, but has to be that way or you get other strange
     * inconsistencies (see test string-10.20 for illustration why!)
     */

    if (objv[objc-2]->typePtr == &tclDictType && objv[objc-2]->bytes == NULL){
	int i, done;
	Tcl_DictSearch search;

	/*
	 * We know the type exactly, so all dict operations will succeed for
	 * sure. This shortens this code quite a bit.
	 */

	Tcl_DictObjSize(interp, objv[objc-2], &mapElemc);
	if (mapElemc == 0) {
	    /*
	     * Empty charMap, just return whatever string was given.
	     */

	    Tcl_SetObjResult(interp, objv[objc-1]);
	    return TCL_OK;
	}

	mapElemc *= 2;
	mapWithDict = 1;

	/*
	 * Copy the dictionary out into an array; that's the easiest way to
	 * adapt this code...
	 */

	mapElemv = (Tcl_Obj **)
		TclStackAlloc(interp, sizeof(Tcl_Obj *) * mapElemc);
	Tcl_DictObjFirst(interp, objv[objc-2], &search, mapElemv+0,
		mapElemv+1, &done);
	for (i=2 ; i<mapElemc ; i+=2) {
	    Tcl_DictObjNext(&search, mapElemv+i, mapElemv+i+1, &done);
	}
	Tcl_DictObjDone(&search);
    } else {
	if (TclListObjGetElements(interp, objv[objc-2], &mapElemc,
		&mapElemv) != TCL_OK) {
	    return TCL_ERROR;
	}
	if (mapElemc == 0) {
	    /*
	     * empty charMap, just return whatever string was given.
	     */

	    Tcl_SetObjResult(interp, objv[objc-1]);
	    return TCL_OK;
	} else if (mapElemc & 1) {
	    /*
	     * The charMap must be an even number of key/value items.
	     */

	    Tcl_SetObjResult(interp,
		    Tcl_NewStringObj("char map list unbalanced", -1));
	    return TCL_ERROR;
	}
    }

    /*
     * Take a copy of the source string object if it is the same as the map
     * string to cut out nasty sharing crashes. [Bug 1018562]
     */

    if (objv[objc-2] == objv[objc-1]) {
	sourceObj = Tcl_DuplicateObj(objv[objc-1]);
	copySource = 1;
    } else {
	sourceObj = objv[objc-1];
    }
    ustring1 = Tcl_GetUnicodeFromObj(sourceObj, &length1);
    if (length1 == 0) {
	/*
	 * Empty input string, just stop now.
	 */

	goto done;
    }
    end = ustring1 + length1;

    strCmpFn = (nocase ? Tcl_UniCharNcasecmp : Tcl_UniCharNcmp);

    /*
     * Force result to be Unicode
     */

    resultPtr = Tcl_NewUnicodeObj(ustring1, 0);

    if (mapElemc == 2) {
	/*
	 * Special case for one map pair which avoids the extra for loop and
	 * extra calls to get Unicode data. The algorithm is otherwise
	 * identical to the multi-pair case. This will be >30% faster on
	 * larger strings.
	 */

	int mapLen;
	Tcl_UniChar *mapString, u2lc;

	ustring2 = Tcl_GetUnicodeFromObj(mapElemv[0], &length2);
	p = ustring1;
	if ((length2 > length1) || (length2 == 0)) {
	    /*
	     * Match string is either longer than input or empty.
	     */

	    ustring1 = end;
	} else {
	    mapString = Tcl_GetUnicodeFromObj(mapElemv[1], &mapLen);
	    u2lc = (nocase ? Tcl_UniCharToLower(*ustring2) : 0);
	    for (; ustring1 < end; ustring1++) {
		if (((*ustring1 == *ustring2) ||
			(nocase&&Tcl_UniCharToLower(*ustring1)==u2lc)) &&
			(length2==1 || strCmpFn(ustring1, ustring2,
				(unsigned long) length2) == 0)) {
		    if (p != ustring1) {
			Tcl_AppendUnicodeToObj(resultPtr, p, ustring1-p);
			p = ustring1 + length2;
		    } else {
			p += length2;
		    }
		    ustring1 = p - 1;

		    Tcl_AppendUnicodeToObj(resultPtr, mapString, mapLen);
		}
	    }
	}
    } else {
	Tcl_UniChar **mapStrings, *u2lc = NULL;
	int *mapLens;

	/*
	 * Precompute pointers to the unicode string and length. This saves us
	 * repeated function calls later, significantly speeding up the
	 * algorithm. We only need the lowercase first char in the nocase
	 * case.
	 */

	mapStrings = (Tcl_UniChar **) TclStackAlloc(interp,
		mapElemc * 2 * sizeof(Tcl_UniChar *));
	mapLens = (int *) TclStackAlloc(interp, mapElemc * 2 * sizeof(int));
	if (nocase) {
	    u2lc = (Tcl_UniChar *) TclStackAlloc(interp,
		    mapElemc * sizeof(Tcl_UniChar));
	}
	for (index = 0; index < mapElemc; index++) {
	    mapStrings[index] = Tcl_GetUnicodeFromObj(mapElemv[index],
		    mapLens+index);
	    if (nocase && ((index % 2) == 0)) {
		u2lc[index/2] = Tcl_UniCharToLower(*mapStrings[index]);
	    }
	}
	for (p = ustring1; ustring1 < end; ustring1++) {
	    for (index = 0; index < mapElemc; index += 2) {
		/*
		 * Get the key string to match on.
		 */

		ustring2 = mapStrings[index];
		length2 = mapLens[index];
		if ((length2 > 0) && ((*ustring1 == *ustring2) || (nocase &&
			(Tcl_UniCharToLower(*ustring1) == u2lc[index/2]))) &&
			/* Restrict max compare length. */
			(end-ustring1 >= length2) && ((length2 == 1) ||
			!strCmpFn(ustring2, ustring1, (unsigned) length2))) {
		    if (p != ustring1) {
			/*
			 * Put the skipped chars onto the result first.
			 */

			Tcl_AppendUnicodeToObj(resultPtr, p, ustring1-p);
			p = ustring1 + length2;
		    } else {
			p += length2;
		    }

		    /*
		     * Adjust len to be full length of matched string.
		     */

		    ustring1 = p - 1;

		    /*
		     * Append the map value to the unicode string.
		     */

		    Tcl_AppendUnicodeToObj(resultPtr,
			    mapStrings[index+1], mapLens[index+1]);
		    break;
		}
	    }
	}
	if (nocase) {
	    TclStackFree(interp, u2lc);
	}
	TclStackFree(interp, mapLens);
	TclStackFree(interp, mapStrings);
    }
    if (p != ustring1) {
	/*
	 * Put the rest of the unmapped chars onto result.
	 */

	Tcl_AppendUnicodeToObj(resultPtr, p, ustring1 - p);
    }
    Tcl_SetObjResult(interp, resultPtr);
  done:
    if (mapWithDict) {
	TclStackFree(interp, mapElemv);
    }
    if (copySource) {
	Tcl_DecrRefCount(sourceObj);
    }
    return TCL_OK;
}

/*
 *----------------------------------------------------------------------
 *
 * StringMatchCmd --
 *
 *	This procedure is invoked to process the "string match" Tcl command.
 *	See the user documentation for details on what it does. Note that this
 *	command only functions correctly on properly formed Tcl UTF strings.
 *
 * Results:
 *	A standard Tcl result.
 *
 * Side effects:
 *	See the user documentation.
 *
 *----------------------------------------------------------------------
 */

static int
StringMatchCmd(
    ClientData dummy,		/* Not used. */
    Tcl_Interp *interp,		/* Current interpreter. */
    int objc,			/* Number of arguments. */
    Tcl_Obj *const objv[])	/* Argument objects. */
{
    int nocase = 0;

    if (objc < 3 || objc > 4) {
	Tcl_WrongNumArgs(interp, 1, objv, "?-nocase? pattern string");
	return TCL_ERROR;
    }

    if (objc == 4) {
	int length;
	const char *string = TclGetStringFromObj(objv[1], &length);

	if ((length > 1) &&
	    strncmp(string, "-nocase", (size_t) length) == 0) {
	    nocase = TCL_MATCH_NOCASE;
	} else {
	    Tcl_AppendResult(interp, "bad option \"", string,
		    "\": must be -nocase", NULL);
	    return TCL_ERROR;
	}
    }
    Tcl_SetObjResult(interp, Tcl_NewBooleanObj(
		TclStringMatchObj(objv[objc-1], objv[objc-2], nocase)));
    return TCL_OK;
}

/*
 *----------------------------------------------------------------------
 *
 * StringRangeCmd --
 *
 *	This procedure is invoked to process the "string range" Tcl command.
 *	See the user documentation for details on what it does. Note that this
 *	command only functions correctly on properly formed Tcl UTF strings.
 *
 * Results:
 *	A standard Tcl result.
 *
 * Side effects:
 *	See the user documentation.
 *
 *----------------------------------------------------------------------
 */

static int
StringRangeCmd(
    ClientData dummy,		/* Not used. */
    Tcl_Interp *interp,		/* Current interpreter. */
    int objc,			/* Number of arguments. */
    Tcl_Obj *const objv[])	/* Argument objects. */
{
    const unsigned char *string;
    int length, first, last;

    if (objc != 4) {
	Tcl_WrongNumArgs(interp, 1, objv, "string first last");
	return TCL_ERROR;
    }

    /*
     * If we have a ByteArray object, avoid indexing in the Utf string since
     * the byte array contains one byte per character. Otherwise, use the
     * Unicode string rep to get the range.
     */

    if (objv[1]->typePtr == &tclByteArrayType) {
	string = Tcl_GetByteArrayFromObj(objv[1], &length);
	length--;
    } else {
	/*
	 * Get the length in actual characters.
	 */

	string = NULL;
	length = Tcl_GetCharLength(objv[1]) - 1;
    }

    if (TclGetIntForIndexM(interp, objv[2], length, &first) != TCL_OK ||
	    TclGetIntForIndexM(interp, objv[3], length, &last) != TCL_OK) {
	return TCL_ERROR;
    }

    if (first < 0) {
	first = 0;
    }
    if (last >= length) {
	last = length;
    }
    if (last >= first) {
	if (string != NULL) {
	    /*
	     * Reread the string to prevent shimmering nasties.
	     */

	    string = Tcl_GetByteArrayFromObj(objv[1], &length);
	    Tcl_SetObjResult(interp,
		    Tcl_NewByteArrayObj(string+first, last - first + 1));
	} else {
	    Tcl_SetObjResult(interp, Tcl_GetRange(objv[1], first, last));
	}
    }
    return TCL_OK;
}

/*
 *----------------------------------------------------------------------
 *
 * StringReptCmd --
 *
 *	This procedure is invoked to process the "string repeat" Tcl command.
 *	See the user documentation for details on what it does. Note that this
 *	command only functions correctly on properly formed Tcl UTF strings.
 *
 * Results:
 *	A standard Tcl result.
 *
 * Side effects:
 *	See the user documentation.
 *
 *----------------------------------------------------------------------
 */

static int
StringReptCmd(
    ClientData dummy,		/* Not used. */
    Tcl_Interp *interp,		/* Current interpreter. */
    int objc,			/* Number of arguments. */
    Tcl_Obj *const objv[])	/* Argument objects. */
{
    const char *string1;
    char *string2;
    int count, index, length1, length2;
    Tcl_Obj *resultPtr;

    if (objc != 3) {
	Tcl_WrongNumArgs(interp, 1, objv, "string count");
	return TCL_ERROR;
    }

    if (TclGetIntFromObj(interp, objv[2], &count) != TCL_OK) {
	return TCL_ERROR;
    }

    /*
     * Check for cases that allow us to skip copying stuff.
     */

    if (count == 1) {
	Tcl_SetObjResult(interp, objv[1]);
	goto done;
    } else if (count < 1) {
	goto done;
    }
    string1 = TclGetStringFromObj(objv[1], &length1);
    if (length1 <= 0) {
	goto done;
    }

    /*
     * Only build up a string that has data. Instead of building it up with
     * repeated appends, we just allocate the necessary space once and copy
     * the string value in. Check for overflow with back-division. [Bug
     * #714106]
     */

    length2 = length1 * count + 1;
    if ((length2-1) / count != length1) {
	Tcl_SetObjResult(interp, Tcl_ObjPrintf(
		"string size overflow, must be less than %d", INT_MAX));
	return TCL_ERROR;
    }

    /*
     * Include space for the NUL.
     */

    string2 = attemptckalloc((size_t) length2);
    if (string2 == NULL) {
	/*
	 * Alloc failed. Note that in this case we try to do an error message
	 * since this is a case that's most likely when the alloc is large and
	 * that's easy to do with this API. Note that if we fail allocating a
	 * short string, this will likely keel over too (and fatally).
	 */

	Tcl_SetObjResult(interp, Tcl_ObjPrintf(
		"string size overflow, out of memory allocating %d bytes",
		length2));
	return TCL_ERROR;
    }
    for (index = 0; index < count; index++) {
	memcpy(string2 + (length1 * index), string1, (size_t) length1);
    }
    string2[length2-1] = '\0';

    /*
     * We have to directly assign this instead of using Tcl_SetStringObj (and
     * indirectly TclInitStringRep) because that makes another copy of the
     * data.
     */

    TclNewObj(resultPtr);
    resultPtr->bytes = string2;
    resultPtr->length = length2-1;
    Tcl_SetObjResult(interp, resultPtr);

  done:
    return TCL_OK;
}

/*
 *----------------------------------------------------------------------
 *
 * StringRplcCmd --
 *
 *	This procedure is invoked to process the "string replace" Tcl command.
 *	See the user documentation for details on what it does. Note that this
 *	command only functions correctly on properly formed Tcl UTF strings.
 *
 * Results:
 *	A standard Tcl result.
 *
 * Side effects:
 *	See the user documentation.
 *
 *----------------------------------------------------------------------
 */

static int
StringRplcCmd(
    ClientData dummy,		/* Not used. */
    Tcl_Interp *interp,		/* Current interpreter. */
    int objc,			/* Number of arguments. */
    Tcl_Obj *const objv[])	/* Argument objects. */
{
    Tcl_UniChar *ustring;
    int first, last, length;

    if (objc < 4 || objc > 5) {
	Tcl_WrongNumArgs(interp, 1, objv, "string first last ?string?");
	return TCL_ERROR;
    }

    ustring = Tcl_GetUnicodeFromObj(objv[1], &length);
    length--;

    if (TclGetIntForIndexM(interp, objv[2], length, &first) != TCL_OK ||
	    TclGetIntForIndexM(interp, objv[3], length, &last) != TCL_OK){
	return TCL_ERROR;
    }

    if ((last < first) || (last < 0) || (first > length)) {
	Tcl_SetObjResult(interp, objv[1]);
    } else {
	Tcl_Obj *resultPtr;

	ustring = Tcl_GetUnicodeFromObj(objv[1], &length);
	length--;

	if (first < 0) {
	    first = 0;
	}

	resultPtr = Tcl_NewUnicodeObj(ustring, first);
	if (objc == 5) {
	    Tcl_AppendObjToObj(resultPtr, objv[4]);
	}
	if (last < length) {
	    Tcl_AppendUnicodeToObj(resultPtr, ustring + last + 1,
		    length - last);
	}
	Tcl_SetObjResult(interp, resultPtr);
    }
    return TCL_OK;
}

/*
 *----------------------------------------------------------------------
 *
 * StringRevCmd --
 *
 *	This procedure is invoked to process the "string reverse" Tcl command.
 *	See the user documentation for details on what it does. Note that this
 *	command only functions correctly on properly formed Tcl UTF strings.
 *
 * Results:
 *	A standard Tcl result.
 *
 * Side effects:
 *	See the user documentation.
 *
 *----------------------------------------------------------------------
 */

static int
StringRevCmd(
    ClientData dummy,		/* Not used. */
    Tcl_Interp *interp,		/* Current interpreter. */
    int objc,			/* Number of arguments. */
    Tcl_Obj *const objv[])	/* Argument objects. */
{
    if (objc != 2) {
	Tcl_WrongNumArgs(interp, 1, objv, "string");
	return TCL_ERROR;
    }

    Tcl_SetObjResult(interp, TclStringObjReverse(objv[1]));
    return TCL_OK;
}

/*
 *----------------------------------------------------------------------
 *
 * StringStartCmd --
 *
 *	This procedure is invoked to process the "string wordstart" Tcl
 *	command. See the user documentation for details on what it does. Note
 *	that this command only functions correctly on properly formed Tcl UTF
 *	strings.
 *
 * Results:
 *	A standard Tcl result.
 *
 * Side effects:
 *	See the user documentation.
 *
 *----------------------------------------------------------------------
 */

static int
StringStartCmd(
    ClientData dummy,		/* Not used. */
    Tcl_Interp *interp,		/* Current interpreter. */
    int objc,			/* Number of arguments. */
    Tcl_Obj *const objv[])	/* Argument objects. */
{
    Tcl_UniChar ch;
    const char *p, *string;
    int cur, index, length, numChars;

    if (objc != 3) {
	Tcl_WrongNumArgs(interp, 1, objv, "string index");
	return TCL_ERROR;
    }

    string = TclGetStringFromObj(objv[1], &length);
    numChars = Tcl_NumUtfChars(string, length);
    if (TclGetIntForIndexM(interp, objv[2], numChars-1, &index) != TCL_OK) {
	return TCL_ERROR;
    }
    string = TclGetStringFromObj(objv[1], &length);
    if (index >= numChars) {
	index = numChars - 1;
    }
    cur = 0;
    if (index > 0) {
	p = Tcl_UtfAtIndex(string, index);
	for (cur = index; cur >= 0; cur--) {
	    TclUtfToUniChar(p, &ch);
	    if (!Tcl_UniCharIsWordChar(ch)) {
		break;
	    }
	    p = Tcl_UtfPrev(p, string);
	}
	if (cur != index) {
	    cur += 1;
	}
    }
    Tcl_SetObjResult(interp, Tcl_NewIntObj(cur));
    return TCL_OK;
}

/*
 *----------------------------------------------------------------------
 *
 * StringEndCmd --
 *
 *	This procedure is invoked to process the "string wordend" Tcl command.
 *	See the user documentation for details on what it does. Note that this
 *	command only functions correctly on properly formed Tcl UTF strings.
 *
 * Results:
 *	A standard Tcl result.
 *
 * Side effects:
 *	See the user documentation.
 *
 *----------------------------------------------------------------------
 */

static int
StringEndCmd(
    ClientData dummy,		/* Not used. */
    Tcl_Interp *interp,		/* Current interpreter. */
    int objc,			/* Number of arguments. */
    Tcl_Obj *const objv[])	/* Argument objects. */
{
    Tcl_UniChar ch;
    const char *p, *end, *string;
    int cur, index, length, numChars;

    if (objc != 3) {
	Tcl_WrongNumArgs(interp, 1, objv, "string index");
	return TCL_ERROR;
    }

    string = TclGetStringFromObj(objv[1], &length);
    numChars = Tcl_NumUtfChars(string, length);
    if (TclGetIntForIndexM(interp, objv[2], numChars-1, &index) != TCL_OK) {
	return TCL_ERROR;
    }
    string = TclGetStringFromObj(objv[1], &length);
    if (index < 0) {
	index = 0;
    }
    if (index < numChars) {
	p = Tcl_UtfAtIndex(string, index);
	end = string+length;
	for (cur = index; p < end; cur++) {
	    p += TclUtfToUniChar(p, &ch);
	    if (!Tcl_UniCharIsWordChar(ch)) {
		break;
	    }
	}
	if (cur == index) {
	    cur++;
	}
    } else {
	cur = numChars;
    }
    Tcl_SetObjResult(interp, Tcl_NewIntObj(cur));
    return TCL_OK;
}

/*
 *----------------------------------------------------------------------
 *
 * StringEqualCmd --
 *
 *	This procedure is invoked to process the "string equal" Tcl command.
 *	See the user documentation for details on what it does. Note that this
 *	command only functions correctly on properly formed Tcl UTF strings.
 *
 * Results:
 *	A standard Tcl result.
 *
 * Side effects:
 *	See the user documentation.
 *
 *----------------------------------------------------------------------
 */

static int
StringEqualCmd(
    ClientData dummy,		/* Not used. */
    Tcl_Interp *interp,		/* Current interpreter. */
    int objc,			/* Number of arguments. */
    Tcl_Obj *const objv[])	/* Argument objects. */
{
    /*
     * Remember to keep code here in some sync with the byte-compiled versions
     * in tclExecute.c (INST_STR_EQ, INST_STR_NEQ and INST_STR_CMP as well as
     * the expr string comparison in INST_EQ/INST_NEQ/INST_LT/...).
     */

    char *string1, *string2;
    int length1, length2, i, match, length, nocase = 0, reqlength = -1;
    typedef int (*strCmpFn_t)(const char *, const char *, unsigned int);
    strCmpFn_t strCmpFn;

    if (objc < 3 || objc > 6) {
    str_cmp_args:
	Tcl_WrongNumArgs(interp, 1, objv,
		"?-nocase? ?-length int? string1 string2");
	return TCL_ERROR;
    }

    for (i = 1; i < objc-2; i++) {
	string2 = TclGetStringFromObj(objv[i], &length2);
	if ((length2 > 1) && !strncmp(string2, "-nocase", (size_t)length2)) {
	    nocase = 1;
	} else if ((length2 > 1)
		&& !strncmp(string2, "-length", (size_t)length2)) {
	    if (i+1 >= objc-2) {
		goto str_cmp_args;
	    }
	    ++i;
	    if (TclGetIntFromObj(interp, objv[i], &reqlength) != TCL_OK) {
		return TCL_ERROR;
	    }
	} else {
	    Tcl_AppendResult(interp, "bad option \"", string2,
		    "\": must be -nocase or -length", NULL);
	    return TCL_ERROR;
	}
    }

    /*
     * From now on, we only access the two objects at the end of the argument
     * array.
     */

    objv += objc-2;

    if ((reqlength == 0) || (objv[0] == objv[1])) {
	/*
	 * Always match at 0 chars of if it is the same obj.
	 */

	Tcl_SetObjResult(interp, Tcl_NewBooleanObj(1));
	return TCL_OK;
    }

    if (!nocase && objv[0]->typePtr == &tclByteArrayType &&
	    objv[1]->typePtr == &tclByteArrayType) {
	/*
	 * Use binary versions of comparisons since that won't cause undue
	 * type conversions and it is much faster. Only do this if we're
	 * case-sensitive (which is all that really makes sense with byte
	 * arrays anyway, and we have no memcasecmp() for some reason... :^)
	 */

	string1 = (char *) Tcl_GetByteArrayFromObj(objv[0], &length1);
	string2 = (char *) Tcl_GetByteArrayFromObj(objv[1], &length2);
	strCmpFn = (strCmpFn_t) memcmp;
    } else if ((objv[0]->typePtr == &tclStringType)
	    && (objv[1]->typePtr == &tclStringType)) {
	/*
	 * Do a unicode-specific comparison if both of the args are of String
	 * type. In benchmark testing this proved the most efficient check
	 * between the unicode and string comparison operations.
	 */

	string1 = (char *) Tcl_GetUnicodeFromObj(objv[0], &length1);
	string2 = (char *) Tcl_GetUnicodeFromObj(objv[1], &length2);
	strCmpFn = (strCmpFn_t)
		(nocase ? Tcl_UniCharNcasecmp : Tcl_UniCharNcmp);
    } else {
	/*
	 * As a catch-all we will work with UTF-8. We cannot use memcmp() as
	 * that is unsafe with any string containing NUL (\xC0\x80 in Tcl's
	 * utf rep). We can use the more efficient TclpUtfNcmp2 if we are
	 * case-sensitive and no specific length was requested.
	 */

	string1 = (char *) TclGetStringFromObj(objv[0], &length1);
	string2 = (char *) TclGetStringFromObj(objv[1], &length2);
	if ((reqlength < 0) && !nocase) {
	    strCmpFn = (strCmpFn_t) TclpUtfNcmp2;
	} else {
	    length1 = Tcl_NumUtfChars(string1, length1);
	    length2 = Tcl_NumUtfChars(string2, length2);
	    strCmpFn = (strCmpFn_t) (nocase ? Tcl_UtfNcasecmp : Tcl_UtfNcmp);
	}
    }

    if ((reqlength < 0) && (length1 != length2)) {
	match = 1;		/* This will be reversed below. */
    } else {
	length = (length1 < length2) ? length1 : length2;
	if (reqlength > 0 && reqlength < length) {
	    length = reqlength;
	} else if (reqlength < 0) {
	    /*
	     * The requested length is negative, so we ignore it by setting it
	     * to length + 1 so we correct the match var.
	     */

	    reqlength = length + 1;
	}

	match = strCmpFn(string1, string2, (unsigned) length);
	if ((match == 0) && (reqlength > length)) {
	    match = length1 - length2;
	}
    }

    Tcl_SetObjResult(interp, Tcl_NewBooleanObj(match ? 0 : 1));
    return TCL_OK;
}

/*
 *----------------------------------------------------------------------
 *
 * StringCmpCmd --
 *
 *	This procedure is invoked to process the "string compare" Tcl command.
 *	See the user documentation for details on what it does. Note that this
 *	command only functions correctly on properly formed Tcl UTF strings.
 *
 * Results:
 *	A standard Tcl result.
 *
 * Side effects:
 *	See the user documentation.
 *
 *----------------------------------------------------------------------
 */

static int
StringCmpCmd(
    ClientData dummy,		/* Not used. */
    Tcl_Interp *interp,		/* Current interpreter. */
    int objc,			/* Number of arguments. */
    Tcl_Obj *const objv[])	/* Argument objects. */
{
    /*
     * Remember to keep code here in some sync with the byte-compiled versions
     * in tclExecute.c (INST_STR_EQ, INST_STR_NEQ and INST_STR_CMP as well as
     * the expr string comparison in INST_EQ/INST_NEQ/INST_LT/...).
     */

    char *string1, *string2;
    int length1, length2, i, match, length, nocase = 0, reqlength = -1;
    typedef int (*strCmpFn_t)(const char *, const char *, unsigned int);
    strCmpFn_t strCmpFn;

    if (objc < 3 || objc > 6) {
    str_cmp_args:
	Tcl_WrongNumArgs(interp, 1, objv,
		"?-nocase? ?-length int? string1 string2");
	return TCL_ERROR;
    }

    for (i = 1; i < objc-2; i++) {
	string2 = TclGetStringFromObj(objv[i], &length2);
	if ((length2 > 1) && !strncmp(string2, "-nocase", (size_t)length2)) {
	    nocase = 1;
	} else if ((length2 > 1)
		&& !strncmp(string2, "-length", (size_t)length2)) {
	    if (i+1 >= objc-2) {
		goto str_cmp_args;
	    }
	    ++i;
	    if (TclGetIntFromObj(interp, objv[i], &reqlength) != TCL_OK) {
		return TCL_ERROR;
	    }
	} else {
	    Tcl_AppendResult(interp, "bad option \"", string2,
		    "\": must be -nocase or -length", NULL);
	    return TCL_ERROR;
	}
    }

    /*
     * From now on, we only access the two objects at the end of the argument
     * array.
     */

    objv += objc-2;

    if ((reqlength == 0) || (objv[0] == objv[1])) {
	/*
	 * Always match at 0 chars of if it is the same obj.
	 */

	Tcl_SetObjResult(interp, Tcl_NewBooleanObj(0));
	return TCL_OK;
    }

    if (!nocase && objv[0]->typePtr == &tclByteArrayType &&
	    objv[1]->typePtr == &tclByteArrayType) {
	/*
	 * Use binary versions of comparisons since that won't cause undue
	 * type conversions and it is much faster. Only do this if we're
	 * case-sensitive (which is all that really makes sense with byte
	 * arrays anyway, and we have no memcasecmp() for some reason... :^)
	 */

	string1 = (char *) Tcl_GetByteArrayFromObj(objv[0], &length1);
	string2 = (char *) Tcl_GetByteArrayFromObj(objv[1], &length2);
	strCmpFn = (strCmpFn_t) memcmp;
    } else if ((objv[0]->typePtr == &tclStringType)
	    && (objv[1]->typePtr == &tclStringType)) {
	/*
	 * Do a unicode-specific comparison if both of the args are of String
	 * type. In benchmark testing this proved the most efficient check
	 * between the unicode and string comparison operations.
	 */

	string1 = (char *) Tcl_GetUnicodeFromObj(objv[0], &length1);
	string2 = (char *) Tcl_GetUnicodeFromObj(objv[1], &length2);
	strCmpFn = (strCmpFn_t)
		(nocase ? Tcl_UniCharNcasecmp : Tcl_UniCharNcmp);
    } else {
	/*
	 * As a catch-all we will work with UTF-8. We cannot use memcmp() as
	 * that is unsafe with any string containing NUL (\xC0\x80 in Tcl's
	 * utf rep). We can use the more efficient TclpUtfNcmp2 if we are
	 * case-sensitive and no specific length was requested.
	 */

	string1 = (char *) TclGetStringFromObj(objv[0], &length1);
	string2 = (char *) TclGetStringFromObj(objv[1], &length2);
	if ((reqlength < 0) && !nocase) {
	    strCmpFn = (strCmpFn_t) TclpUtfNcmp2;
	} else {
	    length1 = Tcl_NumUtfChars(string1, length1);
	    length2 = Tcl_NumUtfChars(string2, length2);
	    strCmpFn = (strCmpFn_t) (nocase ? Tcl_UtfNcasecmp : Tcl_UtfNcmp);
	}
    }

    length = (length1 < length2) ? length1 : length2;
    if (reqlength > 0 && reqlength < length) {
	length = reqlength;
    } else if (reqlength < 0) {
	/*
	 * The requested length is negative, so we ignore it by setting it to
	 * length + 1 so we correct the match var.
	 */

	reqlength = length + 1;
    }

    match = strCmpFn(string1, string2, (unsigned) length);
    if ((match == 0) && (reqlength > length)) {
	match = length1 - length2;
    }

    Tcl_SetObjResult(interp,
	    Tcl_NewIntObj((match > 0) ? 1 : (match < 0) ? -1 : 0));
    return TCL_OK;
}

/*
 *----------------------------------------------------------------------
 *
 * StringBytesCmd --
 *
 *	This procedure is invoked to process the "string bytelength" Tcl
 *	command. See the user documentation for details on what it does. Note
 *	that this command only functions correctly on properly formed Tcl UTF
 *	strings.
 *
 * Results:
 *	A standard Tcl result.
 *
 * Side effects:
 *	See the user documentation.
 *
 *----------------------------------------------------------------------
 */

static int
StringBytesCmd(
    ClientData dummy,		/* Not used. */
    Tcl_Interp *interp,		/* Current interpreter. */
    int objc,			/* Number of arguments. */
    Tcl_Obj *const objv[])	/* Argument objects. */
{
    int length;

    if (objc != 2) {
	Tcl_WrongNumArgs(interp, 1, objv, "string");
	return TCL_ERROR;
    }

    (void) TclGetStringFromObj(objv[1], &length);
    Tcl_SetObjResult(interp, Tcl_NewIntObj(length));
    return TCL_OK;
}

/*
 *----------------------------------------------------------------------
 *
 * StringLenCmd --
 *
 *	This procedure is invoked to process the "string length" Tcl command.
 *	See the user documentation for details on what it does. Note that this
 *	command only functions correctly on properly formed Tcl UTF strings.
 *
 * Results:
 *	A standard Tcl result.
 *
 * Side effects:
 *	See the user documentation.
 *
 *----------------------------------------------------------------------
 */

static int
StringLenCmd(
    ClientData dummy,		/* Not used. */
    Tcl_Interp *interp,		/* Current interpreter. */
    int objc,			/* Number of arguments. */
    Tcl_Obj *const objv[])	/* Argument objects. */
{
    int length;

    if (objc != 2) {
	Tcl_WrongNumArgs(interp, 1, objv, "string");
	return TCL_ERROR;
    }

    /*
     * If we have a ByteArray object, avoid recomputing the string since the
     * byte array contains one byte per character. Otherwise, use the Unicode
     * string rep to calculate the length.
     */

    if (objv[1]->typePtr == &tclByteArrayType) {
	(void) Tcl_GetByteArrayFromObj(objv[1], &length);
    } else {
	length = Tcl_GetCharLength(objv[1]);
    }
    Tcl_SetObjResult(interp, Tcl_NewIntObj(length));
    return TCL_OK;
}

/*
 *----------------------------------------------------------------------
 *
 * StringLowerCmd --
 *
 *	This procedure is invoked to process the "string tolower" Tcl command.
 *	See the user documentation for details on what it does. Note that this
 *	command only functions correctly on properly formed Tcl UTF strings.
 *
 * Results:
 *	A standard Tcl result.
 *
 * Side effects:
 *	See the user documentation.
 *
 *----------------------------------------------------------------------
 */

static int
StringLowerCmd(
    ClientData dummy,		/* Not used. */
    Tcl_Interp *interp,		/* Current interpreter. */
    int objc,			/* Number of arguments. */
    Tcl_Obj *const objv[])	/* Argument objects. */
{
    int length1, length2;
    char *string1, *string2;

    if (objc < 2 || objc > 4) {
	Tcl_WrongNumArgs(interp, 1, objv, "string ?first? ?last?");
	return TCL_ERROR;
    }

    string1 = TclGetStringFromObj(objv[1], &length1);

    if (objc == 2) {
	Tcl_Obj *resultPtr = Tcl_NewStringObj(string1, length1);

	length1 = Tcl_UtfToLower(TclGetString(resultPtr));
	Tcl_SetObjLength(resultPtr, length1);
	Tcl_SetObjResult(interp, resultPtr);
    } else {
	int first, last;
	const char *start, *end;
	Tcl_Obj *resultPtr;

	length1 = Tcl_NumUtfChars(string1, length1) - 1;
	if (TclGetIntForIndexM(interp,objv[2],length1, &first) != TCL_OK) {
	    return TCL_ERROR;
	}
	if (first < 0) {
	    first = 0;
	}
	last = first;

	if ((objc == 4) && (TclGetIntForIndexM(interp, objv[3], length1,
		&last) != TCL_OK)) {
	    return TCL_ERROR;
	}

	if (last >= length1) {
	    last = length1;
	}
	if (last < first) {
	    Tcl_SetObjResult(interp, objv[1]);
	    return TCL_OK;
	}

	string1 = TclGetStringFromObj(objv[1], &length1);
	start = Tcl_UtfAtIndex(string1, first);
	end = Tcl_UtfAtIndex(start, last - first + 1);
	resultPtr = Tcl_NewStringObj(string1, end - string1);
	string2 = TclGetString(resultPtr) + (start - string1);

	length2 = Tcl_UtfToLower(string2);
	Tcl_SetObjLength(resultPtr, length2 + (start - string1));

	Tcl_AppendToObj(resultPtr, end, -1);
	Tcl_SetObjResult(interp, resultPtr);
    }

    return TCL_OK;
}

/*
 *----------------------------------------------------------------------
 *
 * StringUpperCmd --
 *
 *	This procedure is invoked to process the "string toupper" Tcl command.
 *	See the user documentation for details on what it does. Note that this
 *	command only functions correctly on properly formed Tcl UTF strings.
 *
 * Results:
 *	A standard Tcl result.
 *
 * Side effects:
 *	See the user documentation.
 *
 *----------------------------------------------------------------------
 */

static int
StringUpperCmd(
    ClientData dummy,		/* Not used. */
    Tcl_Interp *interp,		/* Current interpreter. */
    int objc,			/* Number of arguments. */
    Tcl_Obj *const objv[])	/* Argument objects. */
{
    int length1, length2;
    char *string1, *string2;

    if (objc < 2 || objc > 4) {
	Tcl_WrongNumArgs(interp, 1, objv, "string ?first? ?last?");
	return TCL_ERROR;
    }

    string1 = TclGetStringFromObj(objv[1], &length1);

    if (objc == 2) {
	Tcl_Obj *resultPtr = Tcl_NewStringObj(string1, length1);

	length1 = Tcl_UtfToUpper(TclGetString(resultPtr));
	Tcl_SetObjLength(resultPtr, length1);
	Tcl_SetObjResult(interp, resultPtr);
    } else {
	int first, last;
	const char *start, *end;
	Tcl_Obj *resultPtr;

	length1 = Tcl_NumUtfChars(string1, length1) - 1;
	if (TclGetIntForIndexM(interp,objv[2],length1, &first) != TCL_OK) {
	    return TCL_ERROR;
	}
	if (first < 0) {
	    first = 0;
	}
	last = first;

	if ((objc == 4) && (TclGetIntForIndexM(interp, objv[3], length1,
		&last) != TCL_OK)) {
	    return TCL_ERROR;
	}

	if (last >= length1) {
	    last = length1;
	}
	if (last < first) {
	    Tcl_SetObjResult(interp, objv[1]);
	    return TCL_OK;
	}

	string1 = TclGetStringFromObj(objv[1], &length1);
	start = Tcl_UtfAtIndex(string1, first);
	end = Tcl_UtfAtIndex(start, last - first + 1);
	resultPtr = Tcl_NewStringObj(string1, end - string1);
	string2 = TclGetString(resultPtr) + (start - string1);

	length2 = Tcl_UtfToUpper(string2);
	Tcl_SetObjLength(resultPtr, length2 + (start - string1));

	Tcl_AppendToObj(resultPtr, end, -1);
	Tcl_SetObjResult(interp, resultPtr);
    }

    return TCL_OK;
}

/*
 *----------------------------------------------------------------------
 *
 * StringTitleCmd --
 *
 *	This procedure is invoked to process the "string totitle" Tcl command.
 *	See the user documentation for details on what it does. Note that this
 *	command only functions correctly on properly formed Tcl UTF strings.
 *
 * Results:
 *	A standard Tcl result.
 *
 * Side effects:
 *	See the user documentation.
 *
 *----------------------------------------------------------------------
 */

static int
StringTitleCmd(
    ClientData dummy,		/* Not used. */
    Tcl_Interp *interp,		/* Current interpreter. */
    int objc,			/* Number of arguments. */
    Tcl_Obj *const objv[])	/* Argument objects. */
{
    int length1, length2;
    char *string1, *string2;

    if (objc < 2 || objc > 4) {
	Tcl_WrongNumArgs(interp, 1, objv, "string ?first? ?last?");
	return TCL_ERROR;
    }

    string1 = TclGetStringFromObj(objv[1], &length1);

    if (objc == 2) {
	Tcl_Obj *resultPtr = Tcl_NewStringObj(string1, length1);

	length1 = Tcl_UtfToTitle(TclGetString(resultPtr));
	Tcl_SetObjLength(resultPtr, length1);
	Tcl_SetObjResult(interp, resultPtr);
    } else {
	int first, last;
	const char *start, *end;
	Tcl_Obj *resultPtr;

	length1 = Tcl_NumUtfChars(string1, length1) - 1;
	if (TclGetIntForIndexM(interp,objv[2],length1, &first) != TCL_OK) {
	    return TCL_ERROR;
	}
	if (first < 0) {
	    first = 0;
	}
	last = first;

	if ((objc == 4) && (TclGetIntForIndexM(interp, objv[3], length1,
		&last) != TCL_OK)) {
	    return TCL_ERROR;
	}

	if (last >= length1) {
	    last = length1;
	}
	if (last < first) {
	    Tcl_SetObjResult(interp, objv[1]);
	    return TCL_OK;
	}

	string1 = TclGetStringFromObj(objv[1], &length1);
	start = Tcl_UtfAtIndex(string1, first);
	end = Tcl_UtfAtIndex(start, last - first + 1);
	resultPtr = Tcl_NewStringObj(string1, end - string1);
	string2 = TclGetString(resultPtr) + (start - string1);

	length2 = Tcl_UtfToTitle(string2);
	Tcl_SetObjLength(resultPtr, length2 + (start - string1));

	Tcl_AppendToObj(resultPtr, end, -1);
	Tcl_SetObjResult(interp, resultPtr);
    }

    return TCL_OK;
}

/*
 *----------------------------------------------------------------------
 *
 * StringTrimCmd --
 *
 *	This procedure is invoked to process the "string trim" Tcl command.
 *	See the user documentation for details on what it does. Note that this
 *	command only functions correctly on properly formed Tcl UTF strings.
 *
 * Results:
 *	A standard Tcl result.
 *
 * Side effects:
 *	See the user documentation.
 *
 *----------------------------------------------------------------------
 */

static int
StringTrimCmd(
    ClientData dummy,		/* Not used. */
    Tcl_Interp *interp,		/* Current interpreter. */
    int objc,			/* Number of arguments. */
    Tcl_Obj *const objv[])	/* Argument objects. */
{
    Tcl_UniChar ch, trim;
    register const char *p, *end;
    const char *check, *checkEnd, *string1, *string2;
    int offset, length1, length2;

    if (objc == 3) {
	string2 = TclGetStringFromObj(objv[2], &length2);
    } else if (objc == 2) {
	string2 = " \t\n\r";
	length2 = strlen(string2);
    } else {
	Tcl_WrongNumArgs(interp, 1, objv, "string ?chars?");
	return TCL_ERROR;
    }
    string1 = TclGetStringFromObj(objv[1], &length1);
    checkEnd = string2 + length2;

    /*
     * The outer loop iterates over the string. The inner loop iterates over
     * the trim characters. The loops terminate as soon as a non-trim
     * character is discovered and string1 is left pointing at the first
     * non-trim character.
     */

    end = string1 + length1;
    for (p = string1; p < end; p += offset) {
	offset = TclUtfToUniChar(p, &ch);

	for (check = string2; ; ) {
	    if (check >= checkEnd) {
		p = end;
		break;
	    }
	    check += TclUtfToUniChar(check, &trim);
	    if (ch == trim) {
		length1 -= offset;
		string1 += offset;
		break;
	    }
	}
    }

    /*
     * The outer loop iterates over the string. The inner loop iterates over
     * the trim characters. The loops terminate as soon as a non-trim
     * character is discovered and length1 marks the last non-trim character.
     */

    end = string1;
    for (p = string1 + length1; p > end; ) {
	p = Tcl_UtfPrev(p, string1);
	offset = TclUtfToUniChar(p, &ch);
	check = string2;
	while (1) {
	    if (check >= checkEnd) {
		p = end;
		break;
	    }
	    check += TclUtfToUniChar(check, &trim);
	    if (ch == trim) {
		length1 -= offset;
		break;
	    }
	}
    }

    Tcl_SetObjResult(interp, Tcl_NewStringObj(string1, length1));
    return TCL_OK;
}

/*
 *----------------------------------------------------------------------
 *
 * StringTrimLCmd --
 *
 *	This procedure is invoked to process the "string trimleft" Tcl
 *	command. See the user documentation for details on what it does. Note
 *	that this command only functions correctly on properly formed Tcl UTF
 *	strings.
 *
 * Results:
 *	A standard Tcl result.
 *
 * Side effects:
 *	See the user documentation.
 *
 *----------------------------------------------------------------------
 */

static int
StringTrimLCmd(
    ClientData dummy,		/* Not used. */
    Tcl_Interp *interp,		/* Current interpreter. */
    int objc,			/* Number of arguments. */
    Tcl_Obj *const objv[])	/* Argument objects. */
{
    Tcl_UniChar ch, trim;
    register const char *p, *end;
    const char *check, *checkEnd, *string1, *string2;
    int offset, length1, length2;

    if (objc == 3) {
	string2 = TclGetStringFromObj(objv[2], &length2);
    } else if (objc == 2) {
	string2 = " \t\n\r";
	length2 = strlen(string2);
    } else {
	Tcl_WrongNumArgs(interp, 1, objv, "string ?chars?");
	return TCL_ERROR;
    }
    string1 = TclGetStringFromObj(objv[1], &length1);
    checkEnd = string2 + length2;

    /*
     * The outer loop iterates over the string. The inner loop iterates over
     * the trim characters. The loops terminate as soon as a non-trim
     * character is discovered and string1 is left pointing at the first
     * non-trim character.
     */

    end = string1 + length1;
    for (p = string1; p < end; p += offset) {
	offset = TclUtfToUniChar(p, &ch);

	for (check = string2; ; ) {
	    if (check >= checkEnd) {
		p = end;
		break;
	    }
	    check += TclUtfToUniChar(check, &trim);
	    if (ch == trim) {
		length1 -= offset;
		string1 += offset;
		break;
	    }
	}
    }

    Tcl_SetObjResult(interp, Tcl_NewStringObj(string1, length1));
    return TCL_OK;
}

/*
 *----------------------------------------------------------------------
 *
 * StringTrimRCmd --
 *
 *	This procedure is invoked to process the "string trimright" Tcl
 *	command. See the user documentation for details on what it does. Note
 *	that this command only functions correctly on properly formed Tcl UTF
 *	strings.
 *
 * Results:
 *	A standard Tcl result.
 *
 * Side effects:
 *	See the user documentation.
 *
 *----------------------------------------------------------------------
 */

static int
StringTrimRCmd(
    ClientData dummy,		/* Not used. */
    Tcl_Interp *interp,		/* Current interpreter. */
    int objc,			/* Number of arguments. */
    Tcl_Obj *const objv[])	/* Argument objects. */
{
    Tcl_UniChar ch, trim;
    register const char *p, *end;
    const char *check, *checkEnd, *string1, *string2;
    int offset, length1, length2;

    if (objc == 3) {
	string2 = TclGetStringFromObj(objv[2], &length2);
    } else if (objc == 2) {
	string2 = " \t\n\r";
	length2 = strlen(string2);
    } else {
	Tcl_WrongNumArgs(interp, 1, objv, "string ?chars?");
	return TCL_ERROR;
    }
    string1 = TclGetStringFromObj(objv[1], &length1);
    checkEnd = string2 + length2;

    /*
     * The outer loop iterates over the string. The inner loop iterates over
     * the trim characters. The loops terminate as soon as a non-trim
     * character is discovered and length1 marks the last non-trim character.
     */

    end = string1;
    for (p = string1 + length1; p > end; ) {
	p = Tcl_UtfPrev(p, string1);
	offset = TclUtfToUniChar(p, &ch);
	check = string2;
	while (1) {
	    if (check >= checkEnd) {
		p = end;
		break;
	    }
	    check += TclUtfToUniChar(check, &trim);
	    if (ch == trim) {
		length1 -= offset;
		break;
	    }
	}
    }

    Tcl_SetObjResult(interp, Tcl_NewStringObj(string1, length1));
    return TCL_OK;
}

/*
 *----------------------------------------------------------------------
 *
 * TclInitStringCmd --
 *
 *	This procedure creates the "string" Tcl command. See the user
 *	documentation for details on what it does. Note that this command only
 *	functions correctly on properly formed Tcl UTF strings.
 *
 *	Also note that the primary methods here (equal, compare, match, ...)
 *	have bytecode equivalents. You will find the code for those in
 *	tclExecute.c. The code here will only be used in the non-bc case (like
 *	in an 'eval').
 *
 * Results:
 *	A standard Tcl result.
 *
 * Side effects:
 *	See the user documentation.
 *
 *----------------------------------------------------------------------
 */

Tcl_Command
TclInitStringCmd(
    Tcl_Interp *interp)		/* Current interpreter. */
{
    static const EnsembleImplMap stringImplMap[] = {
	{"bytelength",	StringBytesCmd,	NULL},
	{"compare",	StringCmpCmd,	TclCompileStringCmpCmd},
	{"equal",	StringEqualCmd,	TclCompileStringEqualCmd},
	{"first",	StringFirstCmd,	NULL},
	{"index",	StringIndexCmd,	TclCompileStringIndexCmd},
	{"is",		StringIsCmd,	NULL},
	{"last",	StringLastCmd,	NULL},
	{"length",	StringLenCmd,	TclCompileStringLenCmd},
	{"map",		StringMapCmd,	NULL},
	{"match",	StringMatchCmd,	TclCompileStringMatchCmd},
	{"range",	StringRangeCmd,	NULL},
	{"repeat",	StringReptCmd,	NULL},
	{"replace",	StringRplcCmd,	NULL},
	{"reverse",	StringRevCmd,	NULL},
	{"tolower",	StringLowerCmd,	NULL},
	{"toupper",	StringUpperCmd,	NULL},
	{"totitle",	StringTitleCmd,	NULL},
	{"trim",	StringTrimCmd,	NULL},
	{"trimleft",	StringTrimLCmd,	NULL},
	{"trimright",	StringTrimRCmd,	NULL},
	{"wordend",	StringEndCmd,	NULL},
	{"wordstart",	StringStartCmd,	NULL},
	{NULL}
    };

    return TclMakeEnsemble(interp, "string", stringImplMap);
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_SubstObjCmd --
 *
 *	This procedure is invoked to process the "subst" Tcl command. See the
 *	user documentation for details on what it does. This command relies on
 *	Tcl_SubstObj() for its implementation.
 *
 * Results:
 *	A standard Tcl result.
 *
 * Side effects:
 *	See the user documentation.
 *
 *----------------------------------------------------------------------
 */

int
Tcl_SubstObjCmd(
    ClientData dummy,		/* Not used. */
    Tcl_Interp *interp,		/* Current interpreter. */
    int objc,			/* Number of arguments. */
    Tcl_Obj *CONST objv[])	/* Argument objects. */
{
    static CONST char *substOptions[] = {
	"-nobackslashes", "-nocommands", "-novariables", NULL
    };
    enum substOptions {
	SUBST_NOBACKSLASHES, SUBST_NOCOMMANDS, SUBST_NOVARS
    };
    Tcl_Obj *resultPtr;
    int flags, i;

    /*
     * Parse command-line options.
     */

    flags = TCL_SUBST_ALL;
    for (i = 1; i < (objc-1); i++) {
	int optionIndex;

	if (Tcl_GetIndexFromObj(interp, objv[i], substOptions, "switch", 0,
		&optionIndex) != TCL_OK) {
	    return TCL_ERROR;
	}
	switch (optionIndex) {
	case SUBST_NOBACKSLASHES:
	    flags &= ~TCL_SUBST_BACKSLASHES;
	    break;
	case SUBST_NOCOMMANDS:
	    flags &= ~TCL_SUBST_COMMANDS;
	    break;
	case SUBST_NOVARS:
	    flags &= ~TCL_SUBST_VARIABLES;
	    break;
	default:
	    Tcl_Panic("Tcl_SubstObjCmd: bad option index to SubstOptions");
	}
    }
    if (i != objc-1) {
	Tcl_WrongNumArgs(interp, 1, objv,
		"?-nobackslashes? ?-nocommands? ?-novariables? string");
	return TCL_ERROR;
    }

    /*
     * Perform the substitution.
     */

    resultPtr = Tcl_SubstObj(interp, objv[i], flags);

    if (resultPtr == NULL) {
	return TCL_ERROR;
    }
    Tcl_SetObjResult(interp, resultPtr);
    return TCL_OK;
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_SwitchObjCmd --
 *
 *	This object-based procedure is invoked to process the "switch" Tcl
 *	command. See the user documentation for details on what it does.
 *
 * Results:
 *	A standard Tcl object result.
 *
 * Side effects:
 *	See the user documentation.
 *
 *----------------------------------------------------------------------
 */

int
Tcl_SwitchObjCmd(
    ClientData dummy,		/* Not used. */
    Tcl_Interp *interp,		/* Current interpreter. */
    int objc,			/* Number of arguments. */
    Tcl_Obj *CONST objv[])	/* Argument objects. */
{
    int i,j, index, mode, foundmode, result, splitObjs, numMatchesSaved;
    int noCase, patternLength;
    char *pattern;
    Tcl_Obj *stringObj, *indexVarObj, *matchVarObj;
    Tcl_Obj *CONST *savedObjv = objv;
    Tcl_RegExp regExpr = NULL;
    Interp *iPtr = (Interp *) interp;
    int pc = 0;
    int bidx = 0;		/* Index of body argument. */
    Tcl_Obj *blist = NULL;	/* List obj which is the body */
    CmdFrame *ctxPtr;		/* Copy of the topmost cmdframe, to allow us
				 * to mess with the line information */

    /*
     * If you add options that make -e and -g not unique prefixes of -exact or
     * -glob, you *must* fix TclCompileSwitchCmd's option parser as well.
     */

    static CONST char *options[] = {
	"-exact", "-glob", "-indexvar", "-matchvar", "-nocase", "-regexp",
	"--", NULL
    };
    enum options {
	OPT_EXACT, OPT_GLOB, OPT_INDEXV, OPT_MATCHV, OPT_NOCASE, OPT_REGEXP,
	OPT_LAST
    };
    typedef int (*strCmpFn_t)(const char *, const char *);
    strCmpFn_t strCmpFn = strcmp;

    mode = OPT_EXACT;
    foundmode = 0;
    indexVarObj = NULL;
    matchVarObj = NULL;
    numMatchesSaved = 0;
    noCase = 0;
    for (i = 1; i < objc-2; i++) {
	if (TclGetString(objv[i])[0] != '-') {
	    break;
	}
	if (Tcl_GetIndexFromObj(interp, objv[i], options, "option", 0,
		&index) != TCL_OK) {
	    return TCL_ERROR;
	}
	switch ((enum options) index) {
	    /*
	     * General options.
	     */

	case OPT_LAST:
	    i++;
	    goto finishedOptions;
	case OPT_NOCASE:
	    strCmpFn = strcasecmp;
	    noCase = 1;
	    break;

	    /*
	     * Handle the different switch mode options.
	     */

	default:
	    if (foundmode) {
		/*
		 * Mode already set via -exact, -glob, or -regexp.
		 */

		Tcl_AppendResult(interp, "bad option \"",
			TclGetString(objv[i]), "\": ", options[mode],
			" option already found", NULL);
		return TCL_ERROR;
	    } else {
		foundmode = 1;
		mode = index;
		break;
	    }

	    /*
	     * Check for TIP#75 options specifying the variables to write
	     * regexp information into.
	     */

	case OPT_INDEXV:
	    i++;
	    if (i >= objc-2) {
		Tcl_AppendResult(interp, "missing variable name argument to ",
			"-indexvar", " option", NULL);
		return TCL_ERROR;
	    }
	    indexVarObj = objv[i];
	    numMatchesSaved = -1;
	    break;
	case OPT_MATCHV:
	    i++;
	    if (i >= objc-2) {
		Tcl_AppendResult(interp, "missing variable name argument to ",
			"-matchvar", " option", NULL);
		return TCL_ERROR;
	    }
	    matchVarObj = objv[i];
	    numMatchesSaved = -1;
	    break;
	}
    }

  finishedOptions:
    if (objc - i < 2) {
	Tcl_WrongNumArgs(interp, 1, objv,
		"?switches? string pattern body ... ?default body?");
	return TCL_ERROR;
    }
    if (indexVarObj != NULL && mode != OPT_REGEXP) {
	Tcl_AppendResult(interp,
		"-indexvar option requires -regexp option", NULL);
	return TCL_ERROR;
    }
    if (matchVarObj != NULL && mode != OPT_REGEXP) {
	Tcl_AppendResult(interp,
		"-matchvar option requires -regexp option", NULL);
	return TCL_ERROR;
    }

    stringObj = objv[i];
    objc -= i + 1;
    objv += i + 1;
    bidx = i + 1;		/* First after the match string. */

    /*
     * If all of the pattern/command pairs are lumped into a single argument,
     * split them out again.
     *
     * TIP #280: Determine the lines the words in the list start at, based on
     * the same data for the list word itself. The cmdFramePtr line
     * information is manipulated directly.
     */

    splitObjs = 0;
    if (objc == 1) {
	Tcl_Obj **listv;
	blist = objv[0];

	if (TclListObjGetElements(interp, objv[0], &objc, &listv) != TCL_OK){
	    return TCL_ERROR;
	}

	/*
	 * Ensure that the list is non-empty.
	 */

	if (objc < 1) {
	    Tcl_WrongNumArgs(interp, 1, savedObjv,
		    "?switches? string {pattern body ... ?default body?}");
	    return TCL_ERROR;
	}
	objv = listv;
	splitObjs = 1;
    }

    /*
     * Complain if there is an odd number of words in the list of patterns and
     * bodies.
     */

    if (objc % 2) {
	Tcl_ResetResult(interp);
	Tcl_AppendResult(interp, "extra switch pattern with no body", NULL);

	/*
	 * Check if this can be due to a badly placed comment in the switch
	 * block.
	 *
	 * The following is an heuristic to detect the infamous "comment in
	 * switch" error: just check if a pattern begins with '#'.
	 */

	if (splitObjs) {
	    for (i=0 ; i<objc ; i+=2) {
		if (TclGetString(objv[i])[0] == '#') {
		    Tcl_AppendResult(interp, ", this may be due to a "
			    "comment incorrectly placed outside of a "
			    "switch body - see the \"switch\" "
			    "documentation", NULL);
		    break;
		}
	    }
	}

	return TCL_ERROR;
    }

    /*
     * Complain if the last body is a continuation. Note that this check
     * assumes that the list is non-empty!
     */

    if (strcmp(TclGetString(objv[objc-1]), "-") == 0) {
	Tcl_ResetResult(interp);
	Tcl_AppendResult(interp, "no body specified for pattern \"",
		TclGetString(objv[objc-2]), "\"", NULL);
	return TCL_ERROR;
    }

    for (i = 0; i < objc; i += 2) {
	/*
	 * See if the pattern matches the string.
	 */

	pattern = TclGetStringFromObj(objv[i], &patternLength);

	if ((i == objc - 2) && (*pattern == 'd')
		&& (strcmp(pattern, "default") == 0)) {
	    Tcl_Obj *emptyObj = NULL;

	    /*
	     * If either indexVarObj or matchVarObj are non-NULL, we're in
	     * REGEXP mode but have reached the default clause anyway. TIP#75
	     * specifies that we set the variables to empty lists (== empty
	     * objects) in that case.
	     */

	    if (indexVarObj != NULL) {
		TclNewObj(emptyObj);
		if (Tcl_ObjSetVar2(interp, indexVarObj, NULL, emptyObj,
			TCL_LEAVE_ERR_MSG) == NULL) {
		    return TCL_ERROR;
		}
	    }
	    if (matchVarObj != NULL) {
		if (emptyObj == NULL) {
		    TclNewObj(emptyObj);
		}
		if (Tcl_ObjSetVar2(interp, matchVarObj, NULL, emptyObj,
			TCL_LEAVE_ERR_MSG) == NULL) {
		    return TCL_ERROR;
		}
	    }
	    goto matchFound;
	} else {
	    switch (mode) {
	    case OPT_EXACT:
		if (strCmpFn(TclGetString(stringObj), pattern) == 0) {
		    goto matchFound;
		}
		break;
	    case OPT_GLOB:
		if (Tcl_StringCaseMatch(TclGetString(stringObj), pattern,
			noCase)) {
		    goto matchFound;
		}
		break;
	    case OPT_REGEXP:
		regExpr = Tcl_GetRegExpFromObj(interp, objv[i],
			TCL_REG_ADVANCED | (noCase ? TCL_REG_NOCASE : 0));
		if (regExpr == NULL) {
		    return TCL_ERROR;
		} else {
		    int matched = Tcl_RegExpExecObj(interp, regExpr,
			    stringObj, 0, numMatchesSaved, 0);

		    if (matched < 0) {
			return TCL_ERROR;
		    } else if (matched) {
			goto matchFoundRegexp;
		    }
		}
		break;
	    }
	}
    }
    return TCL_OK;

  matchFoundRegexp:
    /*
     * We are operating in REGEXP mode and we need to store information about
     * what we matched in some user-nominated arrays. So build the lists of
     * values and indices to write here. [TIP#75]
     */

    if (numMatchesSaved) {
	Tcl_RegExpInfo info;
	Tcl_Obj *matchesObj, *indicesObj = NULL;

	Tcl_RegExpGetInfo(regExpr, &info);
	if (matchVarObj != NULL) {
	    TclNewObj(matchesObj);
	} else {
	    matchesObj = NULL;
	}
	if (indexVarObj != NULL) {
	    TclNewObj(indicesObj);
	}

	for (j=0 ; j<=info.nsubs ; j++) {
	    if (indexVarObj != NULL) {
		Tcl_Obj *rangeObjAry[2];

		rangeObjAry[0] = Tcl_NewLongObj(info.matches[j].start);
		rangeObjAry[1] = Tcl_NewLongObj(info.matches[j].end);

		/*
		 * Never fails; the object is always clean at this point.
		 */

		Tcl_ListObjAppendElement(NULL, indicesObj,
			Tcl_NewListObj(2, rangeObjAry));
	    }

	    if (matchVarObj != NULL) {
		Tcl_Obj *substringObj;

		substringObj = Tcl_GetRange(stringObj,
			info.matches[j].start, info.matches[j].end-1);

		/*
		 * Never fails; the object is always clean at this point.
		 */

		Tcl_ListObjAppendElement(NULL, matchesObj, substringObj);
	    }
	}

	if (indexVarObj != NULL) {
	    if (Tcl_ObjSetVar2(interp, indexVarObj, NULL, indicesObj,
		    TCL_LEAVE_ERR_MSG) == NULL) {
		/*
		 * Careful! Check to see if we have allocated the list of
		 * matched strings; if so (but there was an error assigning
		 * the indices list) we have a potential memory leak because
		 * the match list has not been written to a variable. Except
		 * that we'll clean that up right now.
		 */

		if (matchesObj != NULL) {
		    Tcl_DecrRefCount(matchesObj);
		}
		return TCL_ERROR;
	    }
	}
	if (matchVarObj != NULL) {
	    if (Tcl_ObjSetVar2(interp, matchVarObj, NULL, matchesObj,
		    TCL_LEAVE_ERR_MSG) == NULL) {
		/*
		 * Unlike above, if indicesObj is non-NULL at this point, it
		 * will have been written to a variable already and will hence
		 * not be leaked.
		 */

		return TCL_ERROR;
	    }
	}
    }

    /*
     * We've got a match. Find a body to execute, skipping bodies that are
     * "-".
     */

  matchFound:
    ctxPtr = (CmdFrame *) TclStackAlloc(interp, sizeof(CmdFrame));
    *ctxPtr = *iPtr->cmdFramePtr;

    if (splitObjs) {
	/*
	 * We have to perform the GetSrc and other type dependent handling of
	 * the frame here because we are munging with the line numbers,
	 * something the other commands like if, etc. are not doing. Them are
	 * fine with simply passing the CmdFrame through and having the
	 * special handling done in 'info frame', or the bc compiler
	 */

	if (ctxPtr->type == TCL_LOCATION_BC) {
	    /*
	     * Type BC => ctxPtr->data.eval.path    is not used.
	     *            ctxPtr->data.tebc.codePtr is used instead.
	     */

	    TclGetSrcInfoForPc(ctxPtr);
	    pc = 1;

	    /*
	     * The line information in the cmdFrame is now a copy we do not
	     * own.
	     */
	}

	if (ctxPtr->type == TCL_LOCATION_SOURCE && ctxPtr->line[bidx] >= 0) {
	    int bline = ctxPtr->line[bidx];

	    ctxPtr->line = (int *) ckalloc(objc * sizeof(int));
	    ctxPtr->nline = objc;
	    TclListLines(TclGetString(blist), bline, objc, ctxPtr->line);
	} else {
	    /*
	     * This is either a dynamic code word, when all elements are
	     * relative to themselves, or something else less expected and
	     * where we have no information. The result is the same in both
	     * cases; tell the code to come that it doesn't know where it is,
	     * which triggers reversion to the old behavior.
	     */

	    int k;

	    ctxPtr->line = (int *) ckalloc(objc * sizeof(int));
	    ctxPtr->nline = objc;
	    for (k=0; k < objc; k++) {
		ctxPtr->line[k] = -1;
	    }
	}
    }

    for (j = i + 1; ; j += 2) {
	if (j >= objc) {
	    /*
	     * This shouldn't happen since we've checked that the last body is
	     * not a continuation...
	     */

	    Tcl_Panic("fall-out when searching for body to match pattern");
	}
	if (strcmp(TclGetString(objv[j]), "-") != 0) {
	    break;
	}
    }

    /*
     * TIP #280: Make invoking context available to switch branch.
     */

    result = TclEvalObjEx(interp, objv[j], 0, ctxPtr, j);
    if (splitObjs) {
	ckfree((char *) ctxPtr->line);
	if (pc && (ctxPtr->type == TCL_LOCATION_SOURCE)) {
	    /*
	     * Death of SrcInfo reference.
	     */

	    Tcl_DecrRefCount(ctxPtr->data.eval.path);
	}
    }

    /*
     * Generate an error message if necessary.
     */

    if (result == TCL_ERROR) {
	int limit = 50;
	int overflow = (patternLength > limit);

	Tcl_AppendObjToErrorInfo(interp, Tcl_ObjPrintf(
		"\n    (\"%.*s%s\" arm line %d)",
		(overflow ? limit : patternLength), pattern,
		(overflow ? "..." : ""), interp->errorLine));
    }
    TclStackFree(interp, ctxPtr);
    return result;
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_TimeObjCmd --
 *
 *	This object-based procedure is invoked to process the "time" Tcl
 *	command. See the user documentation for details on what it does.
 *
 * Results:
 *	A standard Tcl object result.
 *
 * Side effects:
 *	See the user documentation.
 *
 *----------------------------------------------------------------------
 */

int
Tcl_TimeObjCmd(
    ClientData dummy,		/* Not used. */
    Tcl_Interp *interp,		/* Current interpreter. */
    int objc,			/* Number of arguments. */
    Tcl_Obj *CONST objv[])	/* Argument objects. */
{
    register Tcl_Obj *objPtr;
    Tcl_Obj *objs[4];
    register int i, result;
    int count;
    double totalMicroSec;
#ifndef TCL_WIDE_CLICKS
    Tcl_Time start, stop;
#else
    Tcl_WideInt start, stop;
#endif

    if (objc == 2) {
	count = 1;
    } else if (objc == 3) {
	result = TclGetIntFromObj(interp, objv[2], &count);
	if (result != TCL_OK) {
	    return result;
	}
    } else {
	Tcl_WrongNumArgs(interp, 1, objv, "command ?count?");
	return TCL_ERROR;
    }

    objPtr = objv[1];
    i = count;
#ifndef TCL_WIDE_CLICKS
    Tcl_GetTime(&start);
#else
    start = TclpGetWideClicks();
#endif
    while (i-- > 0) {
	result = Tcl_EvalObjEx(interp, objPtr, 0);
	if (result != TCL_OK) {
	    return result;
	}
    }
#ifndef TCL_WIDE_CLICKS
    Tcl_GetTime(&stop);
    totalMicroSec = ((double) (stop.sec - start.sec)) * 1.0e6
	    + (stop.usec - start.usec);
#else
    stop = TclpGetWideClicks();
    totalMicroSec = ((double) TclpWideClicksToNanoseconds(stop - start))/1.0e3;
#endif

    if (count <= 1) {
	/*
	 * Use int obj since we know time is not fractional. [Bug 1202178]
	 */

	objs[0] = Tcl_NewIntObj((count <= 0) ? 0 : (int) totalMicroSec);
    } else {
	objs[0] = Tcl_NewDoubleObj(totalMicroSec/count);
    }

    /*
     * Construct the result as a list because many programs have always parsed
     * as such (extracting the first element, typically).
     */

    TclNewLiteralStringObj(objs[1], "microseconds");
    TclNewLiteralStringObj(objs[2], "per");
    TclNewLiteralStringObj(objs[3], "iteration");
    Tcl_SetObjResult(interp, Tcl_NewListObj(4, objs));

    return TCL_OK;
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_WhileObjCmd --
 *
 *	This procedure is invoked to process the "while" Tcl command. See the
 *	user documentation for details on what it does.
 *
 *	With the bytecode compiler, this procedure is only called when a
 *	command name is computed at runtime, and is "while" or the name to
 *	which "while" was renamed: e.g., "set z while; $z {$i<100} {}"
 *
 * Results:
 *	A standard Tcl result.
 *
 * Side effects:
 *	See the user documentation.
 *
 *----------------------------------------------------------------------
 */

int
Tcl_WhileObjCmd(
    ClientData dummy,		/* Not used. */
    Tcl_Interp *interp,		/* Current interpreter. */
    int objc,			/* Number of arguments. */
    Tcl_Obj *CONST objv[])	/* Argument objects. */
{
    int result, value;
    Interp *iPtr = (Interp *) interp;

    if (objc != 3) {
	Tcl_WrongNumArgs(interp, 1, objv, "test command");
	return TCL_ERROR;
    }

    while (1) {
	result = Tcl_ExprBooleanObj(interp, objv[1], &value);
	if (result != TCL_OK) {
	    return result;
	}
	if (!value) {
	    break;
	}

	/* TIP #280. */
        result = TclEvalObjEx(interp, objv[2], 0, iPtr->cmdFramePtr, 2);
	if ((result != TCL_OK) && (result != TCL_CONTINUE)) {
	    if (result == TCL_ERROR) {
		Tcl_AppendObjToErrorInfo(interp, Tcl_ObjPrintf(
			"\n    (\"while\" body line %d)", interp->errorLine));
	    }
	    break;
	}
    }
    if (result == TCL_BREAK) {
	result = TCL_OK;
    }
    if (result == TCL_OK) {
	Tcl_ResetResult(interp);
    }
    return result;
}

/*
 *----------------------------------------------------------------------
 *
 * TclListLines --
 *
 *	???
 *
 * Results:
 *	Filled in array of line numbers?
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */

void
TclListLines(
    CONST char *listStr,	/* Pointer to string with list structure.
				 * Assumed to be valid. Assumed to contain n
				 * elements. */
    int line,			/* Line the list as a whole starts on. */
    int n,			/* #elements in lines */
    int *lines)			/* Array of line numbers, to fill. */
{
    int i, length = strlen(listStr);
    CONST char *element = NULL, *next = NULL;

    for (i = 0; i < n; i++) {
	TclFindElement(NULL, listStr, length, &element, &next, NULL, NULL);

	TclAdvanceLines(&line, listStr, element);
				/* Leading whitespace */
	lines[i] = line;
	length -= (next - listStr);
	TclAdvanceLines(&line, element, next);
				/* Element */
	listStr = next;

	if (*element == 0) {
	    /* ASSERT i == n */
	    break;
	}
    }
}

/*
 * Local Variables:
 * mode: c
 * c-basic-offset: 4
 * fill-column: 78
 * End:
 */
