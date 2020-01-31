/*
 * tclStringObj.c --
 *
 *	This file contains functions that implement string operations on Tcl
 *	objects. Some string operations work with UTF strings and others
 *	require Unicode format. Functions that require knowledge of the width
 *	of each character, such as indexing, operate on Unicode data.
 *
 *	A Unicode string is an internationalized string. Conceptually, a
 *	Unicode string is an array of 16-bit quantities organized as a
 *	sequence of properly formed UTF-8 characters. There is a one-to-one
 *	map between Unicode and UTF characters. Because Unicode characters
 *	have a fixed width, operations such as indexing operate on Unicode
 *	data. The String object is optimized for the case where each UTF char
 *	in a string is only one byte. In this case, we store the value of
 *	numChars, but we don't store the Unicode data (unless Tcl_GetUnicode
 *	is explicitly called).
 *
 *	The String object type stores one or both formats. The default
 *	behavior is to store UTF. Once Unicode is calculated by a function, it
 *	is stored in the internal rep for future access (without an additional
 *	O(n) cost).
 *
 *	To allow many appends to be done to an object without constantly
 *	reallocating the space for the string or Unicode representation, we
 *	allocate double the space for the string or Unicode and use the
 *	internal representation to keep track of how much space is used vs.
 *	allocated.
 *
 * Copyright (c) 1995-1997 Sun Microsystems, Inc.
 * Copyright (c) 1999 by Scriptics Corporation.
 *
 * See the file "license.terms" for information on usage and redistribution of
 * this file, and for a DISCLAIMER OF ALL WARRANTIES.
 *
 * RCS: @(#) $Id: tclStringObj.c,v 1.70.2.1 2008/04/07 16:07:00 dgp Exp $ */

#include "tclInt.h"
#include "tommath.h"

/*
 * Prototypes for functions defined later in this file:
 */

static void		AppendUnicodeToUnicodeRep(Tcl_Obj *objPtr,
			    const Tcl_UniChar *unicode, int appendNumChars);
static void		AppendUnicodeToUtfRep(Tcl_Obj *objPtr,
			    const Tcl_UniChar *unicode, int numChars);
static void		AppendUtfToUnicodeRep(Tcl_Obj *objPtr,
			    const char *bytes, int numBytes);
static void		AppendUtfToUtfRep(Tcl_Obj *objPtr,
			    const char *bytes, int numBytes);
static void		FillUnicodeRep(Tcl_Obj *objPtr);
static void		AppendPrintfToObjVA(Tcl_Obj *objPtr,
			    const char *format, va_list argList);
static void		FreeStringInternalRep(Tcl_Obj *objPtr);
static void		DupStringInternalRep(Tcl_Obj *objPtr,
			    Tcl_Obj *copyPtr);
static int		SetStringFromAny(Tcl_Interp *interp, Tcl_Obj *objPtr);
static void		UpdateStringOfString(Tcl_Obj *objPtr);

/*
 * The structure below defines the string Tcl object type by means of
 * functions that can be invoked by generic object code.
 */

Tcl_ObjType tclStringType = {
    "string",			/* name */
    FreeStringInternalRep,	/* freeIntRepPro */
    DupStringInternalRep,	/* dupIntRepProc */
    UpdateStringOfString,	/* updateStringProc */
    SetStringFromAny		/* setFromAnyProc */
};

/*
 * The following structure is the internal rep for a String object. It keeps
 * track of how much memory has been used and how much has been allocated for
 * the Unicode and UTF string to enable growing and shrinking of the UTF and
 * Unicode reps of the String object with fewer mallocs. To optimize string
 * length and indexing operations, this structure also stores the number of
 * characters (same of UTF and Unicode!) once that value has been computed.
 *
 * Under normal configurations, what Tcl calls "Unicode" is actually UTF-16
 * restricted to the Basic Multilingual Plane (i.e. U+00000 to U+0FFFF). This
 * can be officially modified by altering the definition of Tcl_UniChar in
 * tcl.h, but do not do that unless you are sure what you're doing!
 */

typedef struct String {
    int numChars;		/* The number of chars in the string. -1 means
				 * this value has not been calculated. >= 0
				 * means that there is a valid Unicode rep, or
				 * that the number of UTF bytes == the number
				 * of chars. */
    size_t allocated;		/* The amount of space actually allocated for
				 * the UTF string (minus 1 byte for the
				 * termination char). */
    size_t uallocated;		/* The amount of space actually allocated for
				 * the Unicode string (minus 2 bytes for the
				 * termination char). */
    int hasUnicode;		/* Boolean determining whether the string has
				 * a Unicode representation. */
    Tcl_UniChar unicode[2];	/* The array of Unicode chars. The actual size
				 * of this field depends on the 'uallocated'
				 * field above. */
} String;

#define STRING_UALLOC(numChars)	\
	(numChars * sizeof(Tcl_UniChar))
#define STRING_SIZE(ualloc) \
	((unsigned) ((ualloc) \
                 ? sizeof(String) - sizeof(Tcl_UniChar) + (ualloc) \
                 : sizeof(String)))
#define GET_STRING(objPtr) \
	((String *) (objPtr)->internalRep.otherValuePtr)
#define SET_STRING(objPtr, stringPtr) \
	((objPtr)->internalRep.otherValuePtr = (void *) (stringPtr))

/*
 * TCL STRING GROWTH ALGORITHM
 *
 * When growing strings (during an append, for example), the following growth
 * algorithm is used:
 *
 *   Attempt to allocate 2 * (originalLength + appendLength)
 *   On failure:
 *	attempt to allocate originalLength + 2*appendLength +
 *			TCL_GROWTH_MIN_ALLOC
 *
 * This algorithm allows very good performance, as it rapidly increases the
 * memory allocated for a given string, which minimizes the number of
 * reallocations that must be performed. However, using only the doubling
 * algorithm can lead to a significant waste of memory. In particular, it may
 * fail even when there is sufficient memory available to complete the append
 * request (but there is not 2*totalLength memory available). So when the
 * doubling fails (because there is not enough memory available), the
 * algorithm requests a smaller amount of memory, which is still enough to
 * cover the request, but which hopefully will be less than the total
 * available memory.
 *
 * The addition of TCL_GROWTH_MIN_ALLOC allows for efficient handling of very
 * small appends. Without this extra slush factor, a sequence of several small
 * appends would cause several memory allocations. As long as
 * TCL_GROWTH_MIN_ALLOC is a reasonable size, we can avoid that behavior.
 *
 * The growth algorithm can be tuned by adjusting the following parameters:
 *
 * TCL_GROWTH_MIN_ALLOC		Additional space, in bytes, to allocate when
 *				the double allocation has failed. Default is
 *				1024 (1 kilobyte).
 */

#ifndef TCL_GROWTH_MIN_ALLOC
#define TCL_GROWTH_MIN_ALLOC	1024
#endif

/*
 *----------------------------------------------------------------------
 *
 * Tcl_NewStringObj --
 *
 *	This function is normally called when not debugging: i.e., when
 *	TCL_MEM_DEBUG is not defined. It creates a new string object and
 *	initializes it from the byte pointer and length arguments.
 *
 *	When TCL_MEM_DEBUG is defined, this function just returns the result
 *	of calling the debugging version Tcl_DbNewStringObj.
 *
 * Results:
 *	A newly created string object is returned that has ref count zero.
 *
 * Side effects:
 *	The new object's internal string representation will be set to a copy
 *	of the length bytes starting at "bytes". If "length" is negative, use
 *	bytes up to the first NUL byte; i.e., assume "bytes" points to a
 *	C-style NUL-terminated string. The object's type is set to NULL. An
 *	extra NUL is added to the end of the new object's byte array.
 *
 *----------------------------------------------------------------------
 */

#ifdef TCL_MEM_DEBUG
#undef Tcl_NewStringObj
Tcl_Obj *
Tcl_NewStringObj(
    const char *bytes,		/* Points to the first of the length bytes
				 * used to initialize the new object. */
    int length)			/* The number of bytes to copy from "bytes"
				 * when initializing the new object. If
				 * negative, use bytes up to the first NUL
				 * byte. */
{
    return Tcl_DbNewStringObj(bytes, length, "unknown", 0);
}
#else /* if not TCL_MEM_DEBUG */
Tcl_Obj *
Tcl_NewStringObj(
    const char *bytes,		/* Points to the first of the length bytes
				 * used to initialize the new object. */
    int length)			/* The number of bytes to copy from "bytes"
				 * when initializing the new object. If
				 * negative, use bytes up to the first NUL
				 * byte. */
{
    register Tcl_Obj *objPtr;

    if (length < 0) {
	length = (bytes? strlen(bytes) : 0);
    }
    TclNewStringObj(objPtr, bytes, length);
    return objPtr;
}
#endif /* TCL_MEM_DEBUG */

/*
 *----------------------------------------------------------------------
 *
 * Tcl_DbNewStringObj --
 *
 *	This function is normally called when debugging: i.e., when
 *	TCL_MEM_DEBUG is defined. It creates new string objects. It is the
 *	same as the Tcl_NewStringObj function above except that it calls
 *	Tcl_DbCkalloc directly with the file name and line number from its
 *	caller. This simplifies debugging since then the [memory active]
 *	command will report the correct file name and line number when
 *	reporting objects that haven't been freed.
 *
 *	When TCL_MEM_DEBUG is not defined, this function just returns the
 *	result of calling Tcl_NewStringObj.
 *
 * Results:
 *	A newly created string object is returned that has ref count zero.
 *
 * Side effects:
 *	The new object's internal string representation will be set to a copy
 *	of the length bytes starting at "bytes". If "length" is negative, use
 *	bytes up to the first NUL byte; i.e., assume "bytes" points to a
 *	C-style NUL-terminated string. The object's type is set to NULL. An
 *	extra NUL is added to the end of the new object's byte array.
 *
 *----------------------------------------------------------------------
 */

#ifdef TCL_MEM_DEBUG
Tcl_Obj *
Tcl_DbNewStringObj(
    const char *bytes,		/* Points to the first of the length bytes
				 * used to initialize the new object. */
    int length,			/* The number of bytes to copy from "bytes"
				 * when initializing the new object. If
				 * negative, use bytes up to the first NUL
				 * byte. */
    const char *file,		/* The name of the source file calling this
				 * function; used for debugging. */
    int line)			/* Line number in the source file; used for
				 * debugging. */
{
    register Tcl_Obj *objPtr;

    if (length < 0) {
	length = (bytes? strlen(bytes) : 0);
    }
    TclDbNewObj(objPtr, file, line);
    TclInitStringRep(objPtr, bytes, length);
    return objPtr;
}
#else /* if not TCL_MEM_DEBUG */
Tcl_Obj *
Tcl_DbNewStringObj(
    const char *bytes,		/* Points to the first of the length bytes
				 * used to initialize the new object. */
    register int length,	/* The number of bytes to copy from "bytes"
				 * when initializing the new object. If
				 * negative, use bytes up to the first NUL
				 * byte. */
    const char *file,		/* The name of the source file calling this
				 * function; used for debugging. */
    int line)			/* Line number in the source file; used for
				 * debugging. */
{
    return Tcl_NewStringObj(bytes, length);
}
#endif /* TCL_MEM_DEBUG */

/*
 *---------------------------------------------------------------------------
 *
 * Tcl_NewUnicodeObj --
 *
 *	This function is creates a new String object and initializes it from
 *	the given Unicode String. If the Utf String is the same size as the
 *	Unicode string, don't duplicate the data.
 *
 * Results:
 *	The newly created object is returned. This object will have no initial
 *	string representation. The returned object has a ref count of 0.
 *
 * Side effects:
 *	Memory allocated for new object and copy of Unicode argument.
 *
 *---------------------------------------------------------------------------
 */

Tcl_Obj *
Tcl_NewUnicodeObj(
    const Tcl_UniChar *unicode,	/* The unicode string used to initialize the
				 * new object. */
    int numChars)		/* Number of characters in the unicode
				 * string. */
{
    Tcl_Obj *objPtr;
    String *stringPtr;
    size_t uallocated;

    if (numChars < 0) {
	numChars = 0;
	if (unicode) {
	    while (unicode[numChars] != 0) {
		numChars++;
	    }
	}
    }
    uallocated = STRING_UALLOC(numChars);

    /*
     * Create a new obj with an invalid string rep.
     */

    TclNewObj(objPtr);
    Tcl_InvalidateStringRep(objPtr);
    objPtr->typePtr = &tclStringType;

    stringPtr = (String *) ckalloc(STRING_SIZE(uallocated));
    stringPtr->numChars = numChars;
    stringPtr->uallocated = uallocated;
    stringPtr->hasUnicode = (numChars > 0);
    stringPtr->allocated = 0;
    memcpy(stringPtr->unicode, unicode, uallocated);
    stringPtr->unicode[numChars] = 0;
    SET_STRING(objPtr, stringPtr);
    return objPtr;
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_GetCharLength --
 *
 *	Get the length of the Unicode string from the Tcl object.
 *
 * Results:
 *	Pointer to unicode string representing the unicode object.
 *
 * Side effects:
 *	Frees old internal rep. Allocates memory for new "String" internal
 *	rep.
 *
 *----------------------------------------------------------------------
 */

int
Tcl_GetCharLength(
    Tcl_Obj *objPtr)		/* The String object to get the num chars
				 * of. */
{
    String *stringPtr;

    SetStringFromAny(NULL, objPtr);
    stringPtr = GET_STRING(objPtr);

    /*
     * If numChars is unknown, then calculate the number of characaters while
     * populating the Unicode string.
     */

    if (stringPtr->numChars == -1) {
	register int i = objPtr->length;
	register unsigned char *str = (unsigned char *) objPtr->bytes;

	/*
	 * This is a speed sensitive function, so run specially over the
	 * string to count continuous ascii characters before resorting to the
	 * Tcl_NumUtfChars call. This is a long form of:
	 stringPtr->numChars = Tcl_NumUtfChars(objPtr->bytes,objPtr->length);
	 *
	 * TODO: Consider macro-izing this.
	 */

	while (i && (*str < 0xC0)) {
	    i--;
	    str++;
	}
	stringPtr->numChars = objPtr->length - i;
	if (i) {
	    stringPtr->numChars += Tcl_NumUtfChars(objPtr->bytes
		    + (objPtr->length - i), i);
	}

	if (stringPtr->numChars == objPtr->length) {
	    /*
	     * Since we've just calculated the number of chars, and all UTF
	     * chars are 1-byte long, we don't need to store the unicode
	     * string.
	     */

	    stringPtr->hasUnicode = 0;
	} else {
	    /*
	     * Since we've just calucalated the number of chars, and not all
	     * UTF chars are 1-byte long, go ahead and populate the unicode
	     * string.
	     */

	    FillUnicodeRep(objPtr);

	    /*
	     * We need to fetch the pointer again because we have just
	     * reallocated the structure to make room for the Unicode data.
	     */

	    stringPtr = GET_STRING(objPtr);
	}
    }
    return stringPtr->numChars;
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_GetUniChar --
 *
 *	Get the index'th Unicode character from the String object. The index
 *	is assumed to be in the appropriate range.
 *
 * Results:
 *	Returns the index'th Unicode character in the Object.
 *
 * Side effects:
 *	Fills unichar with the index'th Unicode character.
 *
 *----------------------------------------------------------------------
 */

Tcl_UniChar
Tcl_GetUniChar(
    Tcl_Obj *objPtr,		/* The object to get the Unicode charater
				 * from. */
    int index)			/* Get the index'th Unicode character. */
{
    Tcl_UniChar unichar;
    String *stringPtr;

    SetStringFromAny(NULL, objPtr);
    stringPtr = GET_STRING(objPtr);

    if (stringPtr->numChars == -1) {
	/*
	 * We haven't yet calculated the length, so we don't have the Unicode
	 * str. We need to know the number of chars before we can do indexing.
	 */

	Tcl_GetCharLength(objPtr);

	/*
	 * We need to fetch the pointer again because we may have just
	 * reallocated the structure.
	 */

	stringPtr = GET_STRING(objPtr);
    }
    if (stringPtr->hasUnicode == 0) {
	/*
	 * All of the characters in the Utf string are 1 byte chars, so we
	 * don't store the unicode char. We get the Utf string and convert the
	 * index'th byte to a Unicode character.
	 */

	unichar = (Tcl_UniChar) objPtr->bytes[index];
    } else {
	unichar = stringPtr->unicode[index];
    }
    return unichar;
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_GetUnicode --
 *
 *	Get the Unicode form of the String object. If the object is not
 *	already a String object, it will be converted to one. If the String
 *	object does not have a Unicode rep, then one is create from the UTF
 *	string format.
 *
 * Results:
 *	Returns a pointer to the object's internal Unicode string.
 *
 * Side effects:
 *	Converts the object to have the String internal rep.
 *
 *----------------------------------------------------------------------
 */

Tcl_UniChar *
Tcl_GetUnicode(
    Tcl_Obj *objPtr)		/* The object to find the unicode string
				 * for. */
{
    String *stringPtr;

    SetStringFromAny(NULL, objPtr);
    stringPtr = GET_STRING(objPtr);

    if ((stringPtr->numChars == -1) || (stringPtr->hasUnicode == 0)) {
	/*
	 * We haven't yet calculated the length, or all of the characters in
	 * the Utf string are 1 byte chars (so we didn't store the unicode
	 * str). Since this function must return a unicode string, and one has
	 * not yet been stored, force the Unicode to be calculated and stored
	 * now.
	 */

	FillUnicodeRep(objPtr);

	/*
	 * We need to fetch the pointer again because we have just reallocated
	 * the structure to make room for the Unicode data.
	 */

	stringPtr = GET_STRING(objPtr);
    }
    return stringPtr->unicode;
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_GetUnicodeFromObj --
 *
 *	Get the Unicode form of the String object with length. If the object
 *	is not already a String object, it will be converted to one. If the
 *	String object does not have a Unicode rep, then one is create from the
 *	UTF string format.
 *
 * Results:
 *	Returns a pointer to the object's internal Unicode string.
 *
 * Side effects:
 *	Converts the object to have the String internal rep.
 *
 *----------------------------------------------------------------------
 */

Tcl_UniChar *
Tcl_GetUnicodeFromObj(
    Tcl_Obj *objPtr,		/* The object to find the unicode string
				 * for. */
    int *lengthPtr)		/* If non-NULL, the location where the string
				 * rep's unichar length should be stored. If
				 * NULL, no length is stored. */
{
    String *stringPtr;

    SetStringFromAny(NULL, objPtr);
    stringPtr = GET_STRING(objPtr);

    if ((stringPtr->numChars == -1) || (stringPtr->hasUnicode == 0)) {
	/*
	 * We haven't yet calculated the length, or all of the characters in
	 * the Utf string are 1 byte chars (so we didn't store the unicode
	 * str). Since this function must return a unicode string, and one has
	 * not yet been stored, force the Unicode to be calculated and stored
	 * now.
	 */

	FillUnicodeRep(objPtr);

	/*
	 * We need to fetch the pointer again because we have just reallocated
	 * the structure to make room for the Unicode data.
	 */

	stringPtr = GET_STRING(objPtr);
    }

    if (lengthPtr != NULL) {
	*lengthPtr = stringPtr->numChars;
    }
    return stringPtr->unicode;
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_GetRange --
 *
 *	Create a Tcl Object that contains the chars between first and last of
 *	the object indicated by "objPtr". If the object is not already a
 *	String object, convert it to one. The first and last indices are
 *	assumed to be in the appropriate range.
 *
 * Results:
 *	Returns a new Tcl Object of the String type.
 *
 * Side effects:
 *	Changes the internal rep of "objPtr" to the String type.
 *
 *----------------------------------------------------------------------
 */

Tcl_Obj *
Tcl_GetRange(
    Tcl_Obj *objPtr,		/* The Tcl object to find the range of. */
    int first,			/* First index of the range. */
    int last)			/* Last index of the range. */
{
    Tcl_Obj *newObjPtr;		/* The Tcl object to find the range of. */
    String *stringPtr;

    SetStringFromAny(NULL, objPtr);
    stringPtr = GET_STRING(objPtr);

    if (stringPtr->numChars == -1) {
	/*
	 * We haven't yet calculated the length, so we don't have the Unicode
	 * str. We need to know the number of chars before we can do indexing.
	 */

	Tcl_GetCharLength(objPtr);

	/*
	 * We need to fetch the pointer again because we may have just
	 * reallocated the structure.
	 */

	stringPtr = GET_STRING(objPtr);
    }

    if (objPtr->bytes && (stringPtr->numChars == objPtr->length)) {
	char *str = TclGetString(objPtr);

	/*
	 * All of the characters in the Utf string are 1 byte chars, so we
	 * don't store the unicode char. Create a new string object containing
	 * the specified range of chars.
	 */

	newObjPtr = Tcl_NewStringObj(&str[first], last-first+1);

	/*
	 * Since we know the new string only has 1-byte chars, we can set it's
	 * numChars field.
	 */

	SetStringFromAny(NULL, newObjPtr);
	stringPtr = GET_STRING(newObjPtr);
	stringPtr->numChars = last-first+1;
    } else {
	newObjPtr = Tcl_NewUnicodeObj(stringPtr->unicode + first,
		last-first+1);
    }
    return newObjPtr;
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_SetStringObj --
 *
 *	Modify an object to hold a string that is a copy of the bytes
 *	indicated by the byte pointer and length arguments.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	The object's string representation will be set to a copy of the
 *	"length" bytes starting at "bytes". If "length" is negative, use bytes
 *	up to the first NUL byte; i.e., assume "bytes" points to a C-style
 *	NUL-terminated string. The object's old string and internal
 *	representations are freed and the object's type is set NULL.
 *
 *----------------------------------------------------------------------
 */

void
Tcl_SetStringObj(
    register Tcl_Obj *objPtr,	/* Object whose internal rep to init. */
    const char *bytes,		/* Points to the first of the length bytes
				 * used to initialize the object. */
    register int length)	/* The number of bytes to copy from "bytes"
				 * when initializing the object. If negative,
				 * use bytes up to the first NUL byte.*/
{
    /*
     * Free any old string rep, then set the string rep to a copy of the
     * length bytes starting at "bytes".
     */

    if (Tcl_IsShared(objPtr)) {
	Tcl_Panic("%s called with shared object", "Tcl_SetStringObj");
    }

    /*
     * Set the type to NULL and free any internal rep for the old type.
     */

    TclFreeIntRep(objPtr);
    objPtr->typePtr = NULL;

    Tcl_InvalidateStringRep(objPtr);
    if (length < 0) {
	length = (bytes? strlen(bytes) : 0);
    }
    TclInitStringRep(objPtr, bytes, length);
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_SetObjLength --
 *
 *	This function changes the length of the string representation of an
 *	object.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	If the size of objPtr's string representation is greater than length,
 *	then it is reduced to length and a new terminating null byte is stored
 *	in the strength. If the length of the string representation is greater
 *	than length, the storage space is reallocated to the given length; a
 *	null byte is stored at the end, but other bytes past the end of the
 *	original string representation are undefined. The object's internal
 *	representation is changed to "expendable string".
 *
 *----------------------------------------------------------------------
 */

void
Tcl_SetObjLength(
    register Tcl_Obj *objPtr,	/* Pointer to object. This object must not
				 * currently be shared. */
    register int length)	/* Number of bytes desired for string
				 * representation of object, not including
				 * terminating null byte. */
{
    String *stringPtr;

    if (Tcl_IsShared(objPtr)) {
	Tcl_Panic("%s called with shared object", "Tcl_SetObjLength");
    }
    SetStringFromAny(NULL, objPtr);

    stringPtr = GET_STRING(objPtr);

    /*
     * Check that we're not extending a pure unicode string.
     */

    if (length > (int) stringPtr->allocated &&
	    (objPtr->bytes != NULL || stringPtr->hasUnicode == 0)) {
	/*
	 * Not enough space in current string. Reallocate the string space and
	 * free the old string.
	 */

	if (objPtr->bytes != tclEmptyStringRep) {
	    objPtr->bytes = ckrealloc((char *) objPtr->bytes,
		    (unsigned) (length + 1));
	} else {
	    char *newBytes = ckalloc((unsigned) (length+1));

	    if (objPtr->bytes != NULL && objPtr->length != 0) {
		memcpy(newBytes, objPtr->bytes, (size_t) objPtr->length);
		Tcl_InvalidateStringRep(objPtr);
	    }
	    objPtr->bytes = newBytes;
	}
	stringPtr->allocated = length;

	/*
	 * Invalidate the unicode data.
	 */

	stringPtr->hasUnicode = 0;
    }

    if (objPtr->bytes != NULL) {
	objPtr->length = length;
	if (objPtr->bytes != tclEmptyStringRep) {
	    /*
	     * Ensure the string is NUL-terminated.
	     */

	    objPtr->bytes[length] = 0;
	}

	/*
	 * Invalidate the unicode data.
	 */

	stringPtr->numChars = -1;
	stringPtr->hasUnicode = 0;
    } else {
	/*
	 * Changing length of pure unicode string.
	 */

	size_t uallocated = STRING_UALLOC(length);

	if (uallocated > stringPtr->uallocated) {
	    stringPtr = (String *) ckrealloc((char*) stringPtr,
		    STRING_SIZE(uallocated));
	    SET_STRING(objPtr, stringPtr);
	    stringPtr->uallocated = uallocated;
	}
	stringPtr->numChars = length;
	stringPtr->hasUnicode = (length > 0);

	/*
	 * Ensure the string is NUL-terminated.
	 */

	stringPtr->unicode[length] = 0;
	stringPtr->allocated = 0;
	objPtr->length = 0;
    }
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_AttemptSetObjLength --
 *
 *	This function changes the length of the string representation of an
 *	object. It uses the attempt* (non-panic'ing) memory allocators.
 *
 * Results:
 *	1 if the requested memory was allocated, 0 otherwise.
 *
 * Side effects:
 *	If the size of objPtr's string representation is greater than length,
 *	then it is reduced to length and a new terminating null byte is stored
 *	in the strength. If the length of the string representation is greater
 *	than length, the storage space is reallocated to the given length; a
 *	null byte is stored at the end, but other bytes past the end of the
 *	original string representation are undefined. The object's internal
 *	representation is changed to "expendable string".
 *
 *----------------------------------------------------------------------
 */

int
Tcl_AttemptSetObjLength(
    register Tcl_Obj *objPtr,	/* Pointer to object. This object must not
				 * currently be shared. */
    register int length)	/* Number of bytes desired for string
				 * representation of object, not including
				 * terminating null byte. */
{
    String *stringPtr;

    if (Tcl_IsShared(objPtr)) {
	Tcl_Panic("%s called with shared object", "Tcl_AttemptSetObjLength");
    }
    SetStringFromAny(NULL, objPtr);

    stringPtr = GET_STRING(objPtr);

    /*
     * Check that we're not extending a pure unicode string.
     */

    if (length > (int) stringPtr->allocated &&
	    (objPtr->bytes != NULL || stringPtr->hasUnicode == 0)) {
	char *newBytes;

	/*
	 * Not enough space in current string. Reallocate the string space and
	 * free the old string.
	 */

	if (objPtr->bytes != tclEmptyStringRep) {
	    newBytes = attemptckrealloc(objPtr->bytes,
		    (unsigned)(length + 1));
	    if (newBytes == NULL) {
		return 0;
	    }
	} else {
	    newBytes = attemptckalloc((unsigned) (length + 1));
	    if (newBytes == NULL) {
		return 0;
	    }
	    if (objPtr->bytes != NULL && objPtr->length != 0) {
		memcpy(newBytes, objPtr->bytes, (size_t) objPtr->length);
		Tcl_InvalidateStringRep(objPtr);
	    }
	}
	objPtr->bytes = newBytes;
	stringPtr->allocated = length;

	/*
	 * Invalidate the unicode data.
	 */

	stringPtr->hasUnicode = 0;
    }

    if (objPtr->bytes != NULL) {
	objPtr->length = length;
	if (objPtr->bytes != tclEmptyStringRep) {
	    /*
	     * Ensure the string is NULL-terminated.
	     */

	    objPtr->bytes[length] = 0;
	}

	/*
	 * Invalidate the unicode data.
	 */

	stringPtr->numChars = -1;
	stringPtr->hasUnicode = 0;
    } else {
	/*
	 * Changing length of pure unicode string.
	 */

	size_t uallocated = STRING_UALLOC(length);

	if (uallocated > stringPtr->uallocated) {
	    stringPtr = (String *) attemptckrealloc((char*) stringPtr,
		    STRING_SIZE(uallocated));
	    if (stringPtr == NULL) {
		return 0;
	    }
	    SET_STRING(objPtr, stringPtr);
	    stringPtr->uallocated = uallocated;
	}
	stringPtr->numChars = length;
	stringPtr->hasUnicode = (length > 0);

	/*
	 * Ensure the string is NUL-terminated.
	 */

	stringPtr->unicode[length] = 0;
	stringPtr->allocated = 0;
	objPtr->length = 0;
    }
    return 1;
}

/*
 *---------------------------------------------------------------------------
 *
 * TclSetUnicodeObj --
 *
 *	Modify an object to hold the Unicode string indicated by "unicode".
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	Memory allocated for new "String" internal rep.
 *
 *---------------------------------------------------------------------------
 */

void
Tcl_SetUnicodeObj(
    Tcl_Obj *objPtr,		/* The object to set the string of. */
    const Tcl_UniChar *unicode,	/* The unicode string used to initialize the
				 * object. */
    int numChars)		/* Number of characters in the unicode
				 * string. */
{
    String *stringPtr;
    size_t uallocated;

    if (numChars < 0) {
	numChars = 0;
	if (unicode) {
	    while (unicode[numChars] != 0) {
		numChars++;
	    }
	}
    }
    uallocated = STRING_UALLOC(numChars);

    /*
     * Free the internal rep if one exists, and invalidate the string rep.
     */

    TclFreeIntRep(objPtr);
    objPtr->typePtr = &tclStringType;

    /*
     * Allocate enough space for the String structure + Unicode string.
     */

    stringPtr = (String *) ckalloc(STRING_SIZE(uallocated));
    stringPtr->numChars = numChars;
    stringPtr->uallocated = uallocated;
    stringPtr->hasUnicode = (numChars > 0);
    stringPtr->allocated = 0;
    memcpy(stringPtr->unicode, unicode, uallocated);
    stringPtr->unicode[numChars] = 0;

    SET_STRING(objPtr, stringPtr);
    Tcl_InvalidateStringRep(objPtr);
    return;
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_AppendLimitedToObj --
 *
 *	This function appends a limited number of bytes from a sequence of
 *	bytes to an object, marking any limitation with an ellipsis.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	The bytes at *bytes are appended to the string representation of
 *	objPtr.
 *
 *----------------------------------------------------------------------
 */

void
Tcl_AppendLimitedToObj(
    register Tcl_Obj *objPtr,	/* Points to the object to append to. */
    const char *bytes,		/* Points to the bytes to append to the
				 * object. */
    register int length,	/* The number of bytes available to be
				 * appended from "bytes". If < 0, then all
				 * bytes up to a NUL byte are available. */
    register int limit,		/* The maximum number of bytes to append to
				 * the object. */
    const char *ellipsis)	/* Ellipsis marker string, appended to the
				 * object to indicate not all available bytes
				 * at "bytes" were appended. */
{
    String *stringPtr;
    int toCopy = 0;

    if (Tcl_IsShared(objPtr)) {
	Tcl_Panic("%s called with shared object", "Tcl_AppendLimitedToObj");
    }

    SetStringFromAny(NULL, objPtr);

    if (length < 0) {
	length = (bytes ? strlen(bytes) : 0);
    }
    if (length == 0) {
	return;
    }

    if (length <= limit) {
	toCopy = length;
    } else {
	if (ellipsis == NULL) {
	    ellipsis = "...";
	}
	toCopy = Tcl_UtfPrev(bytes+limit+1-strlen(ellipsis), bytes) - bytes;
    }

    /*
     * If objPtr has a valid Unicode rep, then append the Unicode conversion
     * of "bytes" to the objPtr's Unicode rep, otherwise append "bytes" to
     * objPtr's string rep.
     */

    stringPtr = GET_STRING(objPtr);
    if (stringPtr->hasUnicode != 0) {
	AppendUtfToUnicodeRep(objPtr, bytes, toCopy);
    } else {
	AppendUtfToUtfRep(objPtr, bytes, toCopy);
    }

    if (length <= limit) {
	return;
    }

    stringPtr = GET_STRING(objPtr);
    if (stringPtr->hasUnicode != 0) {
	AppendUtfToUnicodeRep(objPtr, ellipsis, -1);
    } else {
	AppendUtfToUtfRep(objPtr, ellipsis, -1);
    }
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_AppendToObj --
 *
 *	This function appends a sequence of bytes to an object.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	The bytes at *bytes are appended to the string representation of
 *	objPtr.
 *
 *----------------------------------------------------------------------
 */

void
Tcl_AppendToObj(
    register Tcl_Obj *objPtr,	/* Points to the object to append to. */
    const char *bytes,		/* Points to the bytes to append to the
				 * object. */
    register int length)	/* The number of bytes to append from "bytes".
				 * If < 0, then append all bytes up to NUL
				 * byte. */
{
    Tcl_AppendLimitedToObj(objPtr, bytes, length, INT_MAX, NULL);
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_AppendUnicodeToObj --
 *
 *	This function appends a Unicode string to an object in the most
 *	efficient manner possible. Length must be >= 0.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	Invalidates the string rep and creates a new Unicode string.
 *
 *----------------------------------------------------------------------
 */

void
Tcl_AppendUnicodeToObj(
    register Tcl_Obj *objPtr,	/* Points to the object to append to. */
    const Tcl_UniChar *unicode,	/* The unicode string to append to the
				 * object. */
    int length)			/* Number of chars in "unicode". */
{
    String *stringPtr;

    if (Tcl_IsShared(objPtr)) {
	Tcl_Panic("%s called with shared object", "Tcl_AppendUnicodeToObj");
    }

    if (length == 0) {
	return;
    }

    SetStringFromAny(NULL, objPtr);
    stringPtr = GET_STRING(objPtr);

    /*
     * If objPtr has a valid Unicode rep, then append the "unicode" to the
     * objPtr's Unicode rep, otherwise the UTF conversion of "unicode" to
     * objPtr's string rep.
     */

    if (stringPtr->hasUnicode != 0) {
	AppendUnicodeToUnicodeRep(objPtr, unicode, length);
    } else {
	AppendUnicodeToUtfRep(objPtr, unicode, length);
    }
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_AppendObjToObj --
 *
 *	This function appends the string rep of one object to another.
 *	"objPtr" cannot be a shared object.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	The string rep of appendObjPtr is appended to the string
 *	representation of objPtr.
 *
 *----------------------------------------------------------------------
 */

void
Tcl_AppendObjToObj(
    Tcl_Obj *objPtr,		/* Points to the object to append to. */
    Tcl_Obj *appendObjPtr)	/* Object to append. */
{
    String *stringPtr;
    int length, numChars, allOneByteChars;
    char *bytes;

    SetStringFromAny(NULL, objPtr);

    /*
     * If objPtr has a valid Unicode rep, then get a Unicode string from
     * appendObjPtr and append it.
     */

    stringPtr = GET_STRING(objPtr);
    if (stringPtr->hasUnicode != 0) {
	/*
	 * If appendObjPtr is not of the "String" type, don't convert it.
	 */

	if (appendObjPtr->typePtr == &tclStringType) {
	    stringPtr = GET_STRING(appendObjPtr);
	    if ((stringPtr->numChars == -1) || (stringPtr->hasUnicode == 0)) {
		/*
		 * If appendObjPtr is a string obj with no valid Unicode rep,
		 * then fill its unicode rep.
		 */

		FillUnicodeRep(appendObjPtr);
		stringPtr = GET_STRING(appendObjPtr);
	    }
	    AppendUnicodeToUnicodeRep(objPtr, stringPtr->unicode,
		    stringPtr->numChars);
	} else {
	    bytes = TclGetStringFromObj(appendObjPtr, &length);
	    AppendUtfToUnicodeRep(objPtr, bytes, length);
	}
	return;
    }

    /*
     * Append to objPtr's UTF string rep. If we know the number of characters
     * in both objects before appending, then set the combined number of
     * characters in the final (appended-to) object.
     */

    bytes = TclGetStringFromObj(appendObjPtr, &length);

    allOneByteChars = 0;
    numChars = stringPtr->numChars;
    if ((numChars >= 0) && (appendObjPtr->typePtr == &tclStringType)) {
	stringPtr = GET_STRING(appendObjPtr);
	if ((stringPtr->numChars >= 0) && (stringPtr->numChars == length)) {
	    numChars += stringPtr->numChars;
	    allOneByteChars = 1;
	}
    }

    AppendUtfToUtfRep(objPtr, bytes, length);

    if (allOneByteChars) {
	stringPtr = GET_STRING(objPtr);
	stringPtr->numChars = numChars;
    }
}

/*
 *----------------------------------------------------------------------
 *
 * AppendUnicodeToUnicodeRep --
 *
 *	This function appends the contents of "unicode" to the Unicode rep of
 *	"objPtr". objPtr must already have a valid Unicode rep.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	objPtr's internal rep is reallocated.
 *
 *----------------------------------------------------------------------
 */

static void
AppendUnicodeToUnicodeRep(
    Tcl_Obj *objPtr,		/* Points to the object to append to. */
    const Tcl_UniChar *unicode,	/* String to append. */
    int appendNumChars)		/* Number of chars of "unicode" to append. */
{
    String *stringPtr, *tmpString;
    size_t numChars;

    if (appendNumChars < 0) {
	appendNumChars = 0;
	if (unicode) {
	    while (unicode[appendNumChars] != 0) {
		appendNumChars++;
	    }
	}
    }
    if (appendNumChars == 0) {
	return;
    }

    SetStringFromAny(NULL, objPtr);
    stringPtr = GET_STRING(objPtr);

    /*
     * If not enough space has been allocated for the unicode rep, reallocate
     * the internal rep object with additional space. First try to double the
     * required allocation; if that fails, try a more modest increase. See the
     * "TCL STRING GROWTH ALGORITHM" comment at the top of this file for an
     * explanation of this growth algorithm.
     */

    numChars = stringPtr->numChars + appendNumChars;

    if (STRING_UALLOC(numChars) >= stringPtr->uallocated) {
	stringPtr->uallocated = STRING_UALLOC(2 * numChars);
	tmpString = (String *) attemptckrealloc((char *)stringPtr,
		STRING_SIZE(stringPtr->uallocated));
	if (tmpString == NULL) {
	    stringPtr->uallocated =
		    STRING_UALLOC(numChars + appendNumChars)
		    + TCL_GROWTH_MIN_ALLOC;
	    tmpString = (String *) ckrealloc((char *)stringPtr,
		    STRING_SIZE(stringPtr->uallocated));
	}
	stringPtr = tmpString;
	SET_STRING(objPtr, stringPtr);
    }

    /*
     * Copy the new string onto the end of the old string, then add the
     * trailing null.
     */

    memcpy(stringPtr->unicode + stringPtr->numChars, unicode,
	    appendNumChars * sizeof(Tcl_UniChar));
    stringPtr->unicode[numChars] = 0;
    stringPtr->numChars = numChars;

    Tcl_InvalidateStringRep(objPtr);
}

/*
 *----------------------------------------------------------------------
 *
 * AppendUnicodeToUtfRep --
 *
 *	This function converts the contents of "unicode" to UTF and appends
 *	the UTF to the string rep of "objPtr".
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	objPtr's internal rep is reallocated.
 *
 *----------------------------------------------------------------------
 */

static void
AppendUnicodeToUtfRep(
    Tcl_Obj *objPtr,		/* Points to the object to append to. */
    const Tcl_UniChar *unicode,	/* String to convert to UTF. */
    int numChars)		/* Number of chars of "unicode" to convert. */
{
    Tcl_DString dsPtr;
    const char *bytes;

    if (numChars < 0) {
	numChars = 0;
	if (unicode) {
	    while (unicode[numChars] != 0) {
		numChars++;
	    }
	}
    }
    if (numChars == 0) {
	return;
    }

    Tcl_DStringInit(&dsPtr);
    bytes = Tcl_UniCharToUtfDString(unicode, numChars, &dsPtr);
    AppendUtfToUtfRep(objPtr, bytes, Tcl_DStringLength(&dsPtr));
    Tcl_DStringFree(&dsPtr);
}

/*
 *----------------------------------------------------------------------
 *
 * AppendUtfToUnicodeRep --
 *
 *	This function converts the contents of "bytes" to Unicode and appends
 *	the Unicode to the Unicode rep of "objPtr". objPtr must already have a
 *	valid Unicode rep.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	objPtr's internal rep is reallocated.
 *
 *----------------------------------------------------------------------
 */

static void
AppendUtfToUnicodeRep(
    Tcl_Obj *objPtr,		/* Points to the object to append to. */
    const char *bytes,		/* String to convert to Unicode. */
    int numBytes)		/* Number of bytes of "bytes" to convert. */
{
    Tcl_DString dsPtr;
    int numChars;
    Tcl_UniChar *unicode;

    if (numBytes < 0) {
	numBytes = (bytes ? strlen(bytes) : 0);
    }
    if (numBytes == 0) {
	return;
    }

    Tcl_DStringInit(&dsPtr);
    numChars = Tcl_NumUtfChars(bytes, numBytes);
    unicode = (Tcl_UniChar *)Tcl_UtfToUniCharDString(bytes, numBytes, &dsPtr);
    AppendUnicodeToUnicodeRep(objPtr, unicode, numChars);
    Tcl_DStringFree(&dsPtr);
}

/*
 *----------------------------------------------------------------------
 *
 * AppendUtfToUtfRep --
 *
 *	This function appends "numBytes" bytes of "bytes" to the UTF string
 *	rep of "objPtr". objPtr must already have a valid String rep.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	objPtr's internal rep is reallocated.
 *
 *----------------------------------------------------------------------
 */

static void
AppendUtfToUtfRep(
    Tcl_Obj *objPtr,		/* Points to the object to append to. */
    const char *bytes,		/* String to append. */
    int numBytes)		/* Number of bytes of "bytes" to append. */
{
    String *stringPtr;
    int newLength, oldLength;

    if (numBytes < 0) {
	numBytes = (bytes ? strlen(bytes) : 0);
    }
    if (numBytes == 0) {
	return;
    }

    /*
     * Copy the new string onto the end of the old string, then add the
     * trailing null.
     */

    oldLength = objPtr->length;
    newLength = numBytes + oldLength;

    stringPtr = GET_STRING(objPtr);
    if (newLength > (int) stringPtr->allocated) {
	/*
	 * There isn't currently enough space in the string representation so
	 * allocate additional space. First, try to double the length
	 * required. If that fails, try a more modest allocation. See the "TCL
	 * STRING GROWTH ALGORITHM" comment at the top of this file for an
	 * explanation of this growth algorithm.
	 */

	if (Tcl_AttemptSetObjLength(objPtr, 2 * newLength) == 0) {
	    Tcl_SetObjLength(objPtr,
		    newLength + numBytes + TCL_GROWTH_MIN_ALLOC);
	}
    }

    /*
     * Invalidate the unicode data.
     */

    stringPtr->numChars = -1;
    stringPtr->hasUnicode = 0;

    memcpy(objPtr->bytes + oldLength, bytes, (size_t) numBytes);
    objPtr->bytes[newLength] = 0;
    objPtr->length = newLength;
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_AppendStringsToObjVA --
 *
 *	This function appends one or more null-terminated strings to an
 *	object.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	The contents of all the string arguments are appended to the string
 *	representation of objPtr.
 *
 *----------------------------------------------------------------------
 */

void
Tcl_AppendStringsToObjVA(
    Tcl_Obj *objPtr,		/* Points to the object to append to. */
    va_list argList)		/* Variable argument list. */
{
#define STATIC_LIST_SIZE 16
    String *stringPtr;
    int newLength, oldLength, attemptLength;
    register char *string, *dst;
    char *static_list[STATIC_LIST_SIZE];
    char **args = static_list;
    int nargs_space = STATIC_LIST_SIZE;
    int nargs, i;

    if (Tcl_IsShared(objPtr)) {
	Tcl_Panic("%s called with shared object", "Tcl_AppendStringsToObj");
    }

    SetStringFromAny(NULL, objPtr);

    /*
     * Figure out how much space is needed for all the strings, and expand the
     * string representation if it isn't big enough. If no bytes would be
     * appended, just return. Note that on some platforms (notably OS/390) the
     * argList is an array so we need to use memcpy.
     */

    nargs = 0;
    newLength = 0;
    oldLength = objPtr->length;
    while (1) {
	string = va_arg(argList, char *);
	if (string == NULL) {
	    break;
	}
	if (nargs >= nargs_space) {
	    /*
	     * Expand the args buffer.
	     */

	    nargs_space += STATIC_LIST_SIZE;
	    if (args == static_list) {
		args = (void *) ckalloc(nargs_space * sizeof(char *));
		for (i = 0; i < nargs; ++i) {
		    args[i] = static_list[i];
		}
	    } else {
		args = (void *) ckrealloc((void *) args,
			nargs_space * sizeof(char *));
	    }
	}
	newLength += strlen(string);
	args[nargs++] = string;
    }
    if (newLength == 0) {
	goto done;
    }

    stringPtr = GET_STRING(objPtr);
    if (oldLength + newLength > (int) stringPtr->allocated) {
	/*
	 * There isn't currently enough space in the string representation, so
	 * allocate additional space. If the current string representation
	 * isn't empty (i.e. it looks like we're doing a series of appends)
	 * then try to allocate extra space to accomodate future growth: first
	 * try to double the required memory; if that fails, try a more modest
	 * allocation. See the "TCL STRING GROWTH ALGORITHM" comment at the
	 * top of this file for an explanation of this growth algorithm.
	 * Otherwise, if the current string representation is empty, exactly
	 * enough memory is allocated.
	 */

	if (oldLength == 0) {
	    Tcl_SetObjLength(objPtr, newLength);
	} else {
	    attemptLength = 2 * (oldLength + newLength);
	    if (Tcl_AttemptSetObjLength(objPtr, attemptLength) == 0) {
		attemptLength = oldLength + (2 * newLength) +
			TCL_GROWTH_MIN_ALLOC;
		Tcl_SetObjLength(objPtr, attemptLength);
	    }
	}
    }

    /*
     * Make a second pass through the arguments, appending all the strings to
     * the object.
     */

    dst = objPtr->bytes + oldLength;
    for (i = 0; i < nargs; ++i) {
	string = args[i];
	if (string == NULL) {
	    break;
	}
	while (*string != 0) {
	    *dst = *string;
	    dst++;
	    string++;
	}
    }

    /*
     * Add a null byte to terminate the string. However, be careful: it's
     * possible that the object is totally empty (if it was empty originally
     * and there was nothing to append). In this case dst is NULL; just leave
     * everything alone.
     */

    if (dst != NULL) {
	*dst = 0;
    }
    objPtr->length = oldLength + newLength;

  done:
    /*
     * If we had to allocate a buffer from the heap, free it now.
     */

    if (args != static_list) {
	ckfree((void *) args);
    }
#undef STATIC_LIST_SIZE
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_AppendStringsToObj --
 *
 *	This function appends one or more null-terminated strings to an
 *	object.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	The contents of all the string arguments are appended to the string
 *	representation of objPtr.
 *
 *----------------------------------------------------------------------
 */

void
Tcl_AppendStringsToObj(
    Tcl_Obj *objPtr,
    ...)
{
    va_list argList;

    va_start(argList, objPtr);
    Tcl_AppendStringsToObjVA(objPtr, argList);
    va_end(argList);
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_AppendFormatToObj --
 *
 *	This function appends a list of Tcl_Obj's to a Tcl_Obj according to
 *	the formatting instructions embedded in the format string. The
 *	formatting instructions are inspired by sprintf(). Returns TCL_OK when
 *	successful. If there's an error in the arguments, TCL_ERROR is
 *	returned, and an error message is written to the interp, if non-NULL.
 *
 * Results:
 *	A standard Tcl result.
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */

int
Tcl_AppendFormatToObj(
    Tcl_Interp *interp,
    Tcl_Obj *appendObj,
    const char *format,
    int objc,
    Tcl_Obj *const objv[])
{
    const char *span = format, *msg;
    int numBytes = 0, objIndex = 0, gotXpg = 0, gotSequential = 0;
    int originalLength;
    static const char *mixedXPG =
	    "cannot mix \"%\" and \"%n$\" conversion specifiers";
    static const char *badIndex[2] = {
	"not enough arguments for all format specifiers",
	"\"%n$\" argument index out of range"
    };

    if (Tcl_IsShared(appendObj)) {
	Tcl_Panic("%s called with shared object", "Tcl_AppendFormatToObj");
    }
    TclGetStringFromObj(appendObj, &originalLength);

    /*
     * Format string is NUL-terminated.
     */

    while (*format != '\0') {
	char *end;
	int gotMinus, gotHash, gotZero, gotSpace, gotPlus, sawFlag;
	int width, gotPrecision, precision, useShort, useWide, useBig;
	int newXpg, numChars, allocSegment = 0;
	Tcl_Obj *segment;
	Tcl_UniChar ch;
	int step = Tcl_UtfToUniChar(format, &ch);

	format += step;
	if (ch != '%') {
	    numBytes += step;
	    continue;
	}
	if (numBytes) {
	    Tcl_AppendToObj(appendObj, span, numBytes);
	    numBytes = 0;
	}

	/*
	 * Saw a % : process the format specifier.
	 *
	 * Step 0. Handle special case of escaped format marker (i.e., %%).
	 */

	step = Tcl_UtfToUniChar(format, &ch);
	if (ch == '%') {
	    span = format;
	    numBytes = step;
	    format += step;
	    continue;
	}

	/*
	 * Step 1. XPG3 position specifier
	 */

	newXpg = 0;
	if (isdigit(UCHAR(ch))) {
	    int position = strtoul(format, &end, 10);
	    if (*end == '$') {
		newXpg = 1;
		objIndex = position - 1;
		format = end + 1;
		step = Tcl_UtfToUniChar(format, &ch);
	    }
	}
	if (newXpg) {
	    if (gotSequential) {
		msg = mixedXPG;
		goto errorMsg;
	    }
	    gotXpg = 1;
	} else {
	    if (gotXpg) {
		msg = mixedXPG;
		goto errorMsg;
	    }
	    gotSequential = 1;
	}
	if ((objIndex < 0) || (objIndex >= objc)) {
	    msg = badIndex[gotXpg];
	    goto errorMsg;
	}

	/*
	 * Step 2. Set of flags.
	 */

	gotMinus = gotHash = gotZero = gotSpace = gotPlus = 0;
	sawFlag = 1;
	do {
	    switch (ch) {
	    case '-':
		gotMinus = 1;
		break;
	    case '#':
		gotHash = 1;
		break;
	    case '0':
		gotZero = 1;
		break;
	    case ' ':
		gotSpace = 1;
		break;
	    case '+':
		gotPlus = 1;
		break;
	    default:
		sawFlag = 0;
	    }
	    if (sawFlag) {
		format += step;
		step = Tcl_UtfToUniChar(format, &ch);
	    }
	} while (sawFlag);

	/*
	 * Step 3. Minimum field width.
	 */

	width = 0;
	if (isdigit(UCHAR(ch))) {
	    width = strtoul(format, &end, 10);
	    format = end;
	    step = Tcl_UtfToUniChar(format, &ch);
	} else if (ch == '*') {
	    if (objIndex >= objc - 1) {
		msg = badIndex[gotXpg];
		goto errorMsg;
	    }
	    if (TclGetIntFromObj(interp, objv[objIndex], &width) != TCL_OK) {
		goto error;
	    }
	    if (width < 0) {
		width = -width;
		gotMinus = 1;
	    }
	    objIndex++;
	    format += step;
	    step = Tcl_UtfToUniChar(format, &ch);
	}

	/*
	 * Step 4. Precision.
	 */

	gotPrecision = precision = 0;
	if (ch == '.') {
	    gotPrecision = 1;
	    format += step;
	    step = Tcl_UtfToUniChar(format, &ch);
	}
	if (isdigit(UCHAR(ch))) {
	    precision = strtoul(format, &end, 10);
	    format = end;
	    step = Tcl_UtfToUniChar(format, &ch);
	} else if (ch == '*') {
	    if (objIndex >= objc - 1) {
		msg = badIndex[gotXpg];
		goto errorMsg;
	    }
	    if (TclGetIntFromObj(interp, objv[objIndex], &precision)
		    != TCL_OK) {
		goto error;
	    }

	    /*
	     * TODO: Check this truncation logic.
	     */

	    if (precision < 0) {
		precision = 0;
	    }
	    objIndex++;
	    format += step;
	    step = Tcl_UtfToUniChar(format, &ch);
	}

	/*
	 * Step 5. Length modifier.
	 */

	useShort = useWide = useBig = 0;
	if (ch == 'h') {
	    useShort = 1;
	    format += step;
	    step = Tcl_UtfToUniChar(format, &ch);
	} else if (ch == 'l') {
	    format += step;
	    step = Tcl_UtfToUniChar(format, &ch);
	    if (ch == 'l') {
		useBig = 1;
		format += step;
		step = Tcl_UtfToUniChar(format, &ch);
	    } else {
#ifndef TCL_WIDE_INT_IS_LONG
		useWide = 1;
#endif
	    }
	}

	format += step;
	span = format;

	/*
	 * Step 6. The actual conversion character.
	 */

	segment = objv[objIndex];
	if (ch == 'i') {
	    ch = 'd';
	}
	switch (ch) {
	case '\0':
	    msg = "format string ended in middle of field specifier";
	    goto errorMsg;
	case 's': {
	    numChars = Tcl_GetCharLength(segment);
	    if (gotPrecision && (precision < numChars)) {
		segment = Tcl_GetRange(segment, 0, precision - 1);
		Tcl_IncrRefCount(segment);
		allocSegment = 1;
	    }
	    break;
	}
	case 'c': {
	    char buf[TCL_UTF_MAX];
	    int code, length;

	    if (TclGetIntFromObj(interp, segment, &code) != TCL_OK) {
		goto error;
	    }
	    length = Tcl_UniCharToUtf(code, buf);
	    segment = Tcl_NewStringObj(buf, length);
	    Tcl_IncrRefCount(segment);
	    allocSegment = 1;
	    break;
	}

	case 'u':
	    if (useBig) {
		msg = "unsigned bignum format is invalid";
		goto errorMsg;
	    }
	case 'd':
	case 'o':
	case 'x':
	case 'X': {
	    short int s = 0;	/* Silence compiler warning; only defined and
				 * used when useShort is true. */
	    long l;
	    Tcl_WideInt w;
	    mp_int big;
	    int isNegative = 0;

	    if (useBig) {
		if (Tcl_GetBignumFromObj(interp, segment, &big) != TCL_OK) {
		    goto error;
		}
		isNegative = (mp_cmp_d(&big, 0) == MP_LT);
	    } else if (useWide) {
		if (Tcl_GetWideIntFromObj(NULL, segment, &w) != TCL_OK) {
		    Tcl_Obj *objPtr;

		    if (Tcl_GetBignumFromObj(interp,segment,&big) != TCL_OK) {
			goto error;
		    }
		    mp_mod_2d(&big, (int) CHAR_BIT*sizeof(Tcl_WideInt), &big);
		    objPtr = Tcl_NewBignumObj(&big);
		    Tcl_IncrRefCount(objPtr);
		    Tcl_GetWideIntFromObj(NULL, objPtr, &w);
		    Tcl_DecrRefCount(objPtr);
		}
		isNegative = (w < (Tcl_WideInt)0);
	    } else if (TclGetLongFromObj(NULL, segment, &l) != TCL_OK) {
		if (Tcl_GetWideIntFromObj(NULL, segment, &w) != TCL_OK) {
		    Tcl_Obj *objPtr;

		    if (Tcl_GetBignumFromObj(interp,segment,&big) != TCL_OK) {
			goto error;
		    }
		    mp_mod_2d(&big, (int) CHAR_BIT * sizeof(long), &big);
		    objPtr = Tcl_NewBignumObj(&big);
		    Tcl_IncrRefCount(objPtr);
		    TclGetLongFromObj(NULL, objPtr, &l);
		    Tcl_DecrRefCount(objPtr);
		} else {
		    l = Tcl_WideAsLong(w);
		}
		if (useShort) {
		    s = (short int) l;
		    isNegative = (s < (short int)0);
		} else {
		    isNegative = (l < (long)0);
		}
	    } else if (useShort) {
		s = (short int) l;
		isNegative = (s < (short int)0);
	    } else {
		isNegative = (l < (long)0);
	    }

	    segment = Tcl_NewObj();
	    allocSegment = 1;
	    Tcl_IncrRefCount(segment);

	    if ((isNegative || gotPlus || gotSpace) && (useBig || (ch == 'd'))) {
		Tcl_AppendToObj(segment, (isNegative ? "-" : gotPlus ? "+" : " "), 1);
	    }

	    if (gotHash) {
		switch (ch) {
		case 'o':
		    Tcl_AppendToObj(segment, "0", 1);
		    precision--;
		    break;
		case 'x':
		case 'X':
		    Tcl_AppendToObj(segment, "0x", 2);
		    break;
		}
	    }

	    switch (ch) {
	    case 'd': {
		int length;
		Tcl_Obj *pure;
		const char *bytes;

		if (useShort) {
		    pure = Tcl_NewIntObj((int)(s));
		} else if (useWide) {
		    pure = Tcl_NewWideIntObj(w);
		} else if (useBig) {
		    pure = Tcl_NewBignumObj(&big);
		} else {
		    pure = Tcl_NewLongObj(l);
		}
		Tcl_IncrRefCount(pure);
		bytes = TclGetStringFromObj(pure, &length);

		/*
		 * Already did the sign above.
		 */

		if (*bytes == '-') {
		    length--;
		    bytes++;
		}

		/*
		 * Canonical decimal string reps for integers are composed
		 * entirely of one-byte encoded characters, so "length" is the
		 * number of chars.
		 */

		if (gotPrecision) {
		    while (length < precision) {
			Tcl_AppendToObj(segment, "0", 1);
			length++;
		    }
		    gotZero = 0;
		}
		if (gotZero) {
		    length += Tcl_GetCharLength(segment);
		    while (length < width) {
			Tcl_AppendToObj(segment, "0", 1);
			length++;
		    }
		}
		Tcl_AppendToObj(segment, bytes, -1);
		Tcl_DecrRefCount(pure);
		break;
	    }

	    case 'u':
	    case 'o':
	    case 'x':
	    case 'X': {
		Tcl_WideUInt bits = (Tcl_WideUInt)0;
		int length, numBits = 4, numDigits = 0, base = 16;
		int index = 0, shift = 0;
		Tcl_Obj *pure;
		char *bytes;

		if (ch == 'u') {
		    base = 10;
		}
		if (ch == 'o') {
		    base = 8;
		    numBits = 3;
		}
		if (useShort) {
		    unsigned short int us = (unsigned short int) s;

		    bits = (Tcl_WideUInt) us;
		    while (us) {
			numDigits++;
			us /= base;
		    }
		} else if (useWide) {
		    Tcl_WideUInt uw = (Tcl_WideUInt) w;

		    bits = uw;
		    while (uw) {
			numDigits++;
			uw /= base;
		    }
		} else if (useBig && big.used) {
		    int leftover = (big.used * DIGIT_BIT) % numBits;
		    mp_digit mask = (~(mp_digit)0) << (DIGIT_BIT-leftover);

		    numDigits = 1 + ((big.used * DIGIT_BIT) / numBits);
		    while ((mask & big.dp[big.used-1]) == 0) {
			numDigits--;
			mask >>= numBits;
		    }
		} else if (!useBig) {
		    unsigned long int ul = (unsigned long int) l;

		    bits = (Tcl_WideUInt) ul;
		    while (ul) {
			numDigits++;
			ul /= base;
		    }
		}

		/*
		 * Need to be sure zero becomes "0", not "".
		 */

		if ((numDigits == 0) && !((ch == 'o') && gotHash)) {
		    numDigits = 1;
		}
		pure = Tcl_NewObj();
		Tcl_SetObjLength(pure, numDigits);
		bytes = TclGetString(pure);
		length = numDigits;
		while (numDigits--) {
		    int digitOffset;

		    if (useBig && big.used) {
			if ((size_t) shift <
				CHAR_BIT*sizeof(Tcl_WideUInt) - DIGIT_BIT) {
			    bits |= (((Tcl_WideUInt)big.dp[index++]) <<shift);
			    shift += DIGIT_BIT;
			}
			shift -= numBits;
		    }
		    digitOffset = (int) (bits % base);
		    if (digitOffset > 9) {
			bytes[numDigits] = 'a' + digitOffset - 10;
		    } else {
			bytes[numDigits] = '0' + digitOffset;
		    }
		    bits /= base;
		}
		if (useBig) {
		    mp_clear(&big);
		}
		if (gotPrecision) {
		    while (length < precision) {
			Tcl_AppendToObj(segment, "0", 1);
			length++;
		    }
		    gotZero = 0;
		}
		if (gotZero) {
		    length += Tcl_GetCharLength(segment);
		    while (length < width) {
			Tcl_AppendToObj(segment, "0", 1);
			length++;
		    }
		}
		Tcl_AppendObjToObj(segment, pure);
		Tcl_DecrRefCount(pure);
		break;
	    }

	    }
	    break;
	}

	case 'e':
	case 'E':
	case 'f':
	case 'g':
	case 'G': {
#define MAX_FLOAT_SIZE 320
	    char spec[2*TCL_INTEGER_SPACE + 9], *p = spec;
	    double d;
	    int length = MAX_FLOAT_SIZE;
	    char *bytes;

	    if (Tcl_GetDoubleFromObj(interp, segment, &d) != TCL_OK) {
		/* TODO: Figure out ACCEPT_NAN here */
		goto error;
	    }
	    *p++ = '%';
	    if (gotMinus) {
		*p++ = '-';
	    }
	    if (gotHash) {
		*p++ = '#';
	    }
	    if (gotZero) {
		*p++ = '0';
	    }
	    if (gotSpace) {
		*p++ = ' ';
	    }
	    if (gotPlus) {
		*p++ = '+';
	    }
	    if (width) {
		p += sprintf(p, "%d", width);
	    }
	    if (gotPrecision) {
		*p++ = '.';
		p += sprintf(p, "%d", precision);
		length += precision;
	    }

	    /*
	     * Don't pass length modifiers!
	     */

	    *p++ = (char) ch;
	    *p = '\0';

	    segment = Tcl_NewObj();
	    allocSegment = 1;
	    Tcl_SetObjLength(segment, length);
	    bytes = TclGetString(segment);
	    Tcl_SetObjLength(segment, sprintf(bytes, spec, d));
	    break;
	}
	default:
	    if (interp != NULL) {
		char buf[40];

		sprintf(buf, "bad field specifier \"%c\"", ch);
		Tcl_SetObjResult(interp, Tcl_NewStringObj(buf, -1));
	    }
	    goto error;
	}

	switch (ch) {
	case 'E':
	case 'G':
	case 'X': {
	    Tcl_SetObjLength(segment, Tcl_UtfToUpper(TclGetString(segment)));
	}
	}

	numChars = Tcl_GetCharLength(segment);
	if (!gotMinus) {
	    while (numChars < width) {
		Tcl_AppendToObj(appendObj, (gotZero ? "0" : " "), 1);
		numChars++;
	    }
	}
	Tcl_AppendObjToObj(appendObj, segment);
	if (allocSegment) {
	    Tcl_DecrRefCount(segment);
	}
	while (numChars < width) {
	    Tcl_AppendToObj(appendObj, (gotZero ? "0" : " "), 1);
	    numChars++;
	}

	objIndex += gotSequential;
    }
    if (numBytes) {
	Tcl_AppendToObj(appendObj, span, numBytes);
	numBytes = 0;
    }

    return TCL_OK;

  errorMsg:
    if (interp != NULL) {
	Tcl_SetObjResult(interp, Tcl_NewStringObj(msg, -1));
    }
  error:
    Tcl_SetObjLength(appendObj, originalLength);
    return TCL_ERROR;
}

/*
 *---------------------------------------------------------------------------
 *
 * Tcl_Format--
 *
 * Results:
 *	A refcount zero Tcl_Obj.
 *
 * Side effects:
 * 	None.
 *
 *---------------------------------------------------------------------------
 */

Tcl_Obj *
Tcl_Format(
    Tcl_Interp *interp,
    const char *format,
    int objc,
    Tcl_Obj *const objv[])
{
    int result;
    Tcl_Obj *objPtr = Tcl_NewObj();
    result = Tcl_AppendFormatToObj(interp, objPtr, format, objc, objv);
    if (result != TCL_OK) {
	Tcl_DecrRefCount(objPtr);
	return NULL;
    }
    return objPtr;
}

/*
 *---------------------------------------------------------------------------
 *
 * AppendPrintfToObjVA --
 *
 * Results:
 *
 * Side effects:
 *
 *---------------------------------------------------------------------------
 */

static void
AppendPrintfToObjVA(
    Tcl_Obj *objPtr,
    const char *format,
    va_list argList)
{
    int code, objc;
    Tcl_Obj **objv, *list = Tcl_NewObj();
    const char *p;
    char *end;

    p = format;
    Tcl_IncrRefCount(list);
    while (*p != '\0') {
	int size = 0, seekingConversion = 1, gotPrecision = 0;
	int lastNum = -1;

	if (*p++ != '%') {
	    continue;
	}
	if (*p == '%') {
	    p++;
	    continue;
	}
	do {
	    switch (*p) {

	    case '\0':
		seekingConversion = 0;
		break;
	    case 's': {
		const char *q, *end, *bytes = va_arg(argList, char *);
		seekingConversion = 0;

		/*
		 * The buffer to copy characters from starts at bytes and ends
		 * at either the first NUL byte, or after lastNum bytes, when
		 * caller has indicated a limit.
		 */

		end = bytes;
		while ((!gotPrecision || lastNum--) && (*end != '\0')) {
		    end++;
		}

		/*
		 * Within that buffer, we trim both ends if needed so that we
		 * copy only whole characters, and avoid copying any partial
		 * multi-byte characters.
		 */

		q = Tcl_UtfPrev(end, bytes);
		if (!Tcl_UtfCharComplete(q, (int)(end - q))) {
		    end = q;
		}

		q = bytes + TCL_UTF_MAX;
		while ((bytes < end) && (bytes < q)
			&& ((*bytes & 0xC0) == 0x80)) {
		    bytes++;
		}

		Tcl_ListObjAppendElement(NULL, list,
			Tcl_NewStringObj(bytes , (int)(end - bytes)));

		break;
	    }
	    case 'c':
	    case 'i':
	    case 'u':
	    case 'd':
	    case 'o':
	    case 'x':
	    case 'X':
		seekingConversion = 0;
		switch (size) {
		case -1:
		case 0:
		    Tcl_ListObjAppendElement(NULL, list, Tcl_NewLongObj(
			    (long int)va_arg(argList, int)));
		    break;
		case 1:
		    Tcl_ListObjAppendElement(NULL, list, Tcl_NewLongObj(
			    va_arg(argList, long int)));
		    break;
		}
		break;
	    case 'e':
	    case 'E':
	    case 'f':
	    case 'g':
	    case 'G':
		Tcl_ListObjAppendElement(NULL, list, Tcl_NewDoubleObj(
			va_arg(argList, double)));
		seekingConversion = 0;
		break;
	    case '*':
		lastNum = (int)va_arg(argList, int);
		Tcl_ListObjAppendElement(NULL, list, Tcl_NewIntObj(lastNum));
		p++;
		break;
	    case '0': case '1': case '2': case '3': case '4':
	    case '5': case '6': case '7': case '8': case '9':
		lastNum = (int) strtoul(p, &end, 10);
		p = end;
		break;
	    case '.':
		gotPrecision = 1;
		p++;
		break;
	    /* TODO: support for wide (and bignum?) arguments */
	    case 'l':
		size = 1;
		p++;
		break;
	    case 'h':
		size = -1;
	    default:
		p++;
	    }
	} while (seekingConversion);
    }
    TclListObjGetElements(NULL, list, &objc, &objv);
    code = Tcl_AppendFormatToObj(NULL, objPtr, format, objc, objv);
    if (code != TCL_OK) {
	Tcl_AppendPrintfToObj(objPtr,
		"Unable to format \"%s\" with supplied arguments: %s",
		format, Tcl_GetString(list));
    }
    Tcl_DecrRefCount(list);
}

/*
 *---------------------------------------------------------------------------
 *
 * Tcl_AppendPrintfToObj --
 *
 * Results:
 *	A standard Tcl result.
 *
 * Side effects:
 * 	None.
 *
 *---------------------------------------------------------------------------
 */

void
Tcl_AppendPrintfToObj(
    Tcl_Obj *objPtr,
    const char *format,
    ...)
{
    va_list argList;

    va_start(argList, format);
    AppendPrintfToObjVA(objPtr, format, argList);
    va_end(argList);
}

/*
 *---------------------------------------------------------------------------
 *
 * Tcl_ObjPrintf --
 *
 * Results:
 *	A refcount zero Tcl_Obj.
 *
 * Side effects:
 * 	None.
 *
 *---------------------------------------------------------------------------
 */

Tcl_Obj *
Tcl_ObjPrintf(
    const char *format,
    ...)
{
    va_list argList;
    Tcl_Obj *objPtr = Tcl_NewObj();

    va_start(argList, format);
    AppendPrintfToObjVA(objPtr, format, argList);
    va_end(argList);
    return objPtr;
}

/*
 *---------------------------------------------------------------------------
 *
 * TclStringObjReverse --
 *
 *	Implements the [string reverse] operation.
 *
 * Results:
 *	An unshared Tcl value which is the [string reverse] of the argument
 *	supplied.  When sharing rules permit, the returned value might be
 *	the argument with modifications done in place.
 *
 * Side effects:
 *	May allocate a new Tcl_Obj.
 *
 *---------------------------------------------------------------------------
 */

Tcl_Obj *
TclStringObjReverse(
    Tcl_Obj *objPtr)
{
    String *stringPtr;
    int numChars = Tcl_GetCharLength(objPtr);
    int i = 0, lastCharIdx = numChars - 1;
    char *bytes;

    if (numChars <= 1) {
	return objPtr;
    }

    stringPtr = GET_STRING(objPtr);
    if (stringPtr->hasUnicode) {
	Tcl_UniChar *source = stringPtr->unicode;

	if (Tcl_IsShared(objPtr)) {
	    Tcl_UniChar *dest, ch = 0;

	    /*
	     * Create a non-empty, pure unicode value, so we can coax
	     * Tcl_SetObjLength into growing the unicode rep buffer.
	     */

	    Tcl_Obj *resultPtr = Tcl_NewUnicodeObj(&ch, 1);
	    Tcl_SetObjLength(resultPtr, numChars);
	    dest = Tcl_GetUnicode(resultPtr);

	    while (i < numChars) {
		dest[i++] = source[lastCharIdx--];
	    }
	    return resultPtr;
	}

	while (i < lastCharIdx) {
	    Tcl_UniChar tmp = source[lastCharIdx];
	    source[lastCharIdx--] = source[i];
	    source[i++] = tmp;
	}
	Tcl_InvalidateStringRep(objPtr);
	return objPtr;
    }

    bytes = TclGetString(objPtr);
    if (Tcl_IsShared(objPtr)) {
	char *dest;
	Tcl_Obj *resultPtr = Tcl_NewObj();
	Tcl_SetObjLength(resultPtr, numChars);
	dest = TclGetString(resultPtr);
	while (i < numChars) {
	    dest[i++] = bytes[lastCharIdx--];
	}
	return resultPtr;
    }

    while (i < lastCharIdx) {
	char tmp = bytes[lastCharIdx];
	bytes[lastCharIdx--] = bytes[i];
	bytes[i++] = tmp;
    }
    return objPtr;
}

/*
 *---------------------------------------------------------------------------
 *
 * FillUnicodeRep --
 *
 *	Populate the Unicode internal rep with the Unicode form of its string
 *	rep. The object must alread have a "String" internal rep.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	Reallocates the String internal rep.
 *
 *---------------------------------------------------------------------------
 */

static void
FillUnicodeRep(
    Tcl_Obj *objPtr)		/* The object in which to fill the unicode
				 * rep. */
{
    String *stringPtr;
    size_t uallocated;
    char *srcEnd, *src = objPtr->bytes;
    Tcl_UniChar *dst;

    stringPtr = GET_STRING(objPtr);
    if (stringPtr->numChars == -1) {
	stringPtr->numChars = Tcl_NumUtfChars(src, objPtr->length);
    }
    stringPtr->hasUnicode = (stringPtr->numChars > 0);

    uallocated = STRING_UALLOC(stringPtr->numChars);
    if (uallocated > stringPtr->uallocated) {
	/*
	 * If not enough space has been allocated for the unicode rep,
	 * reallocate the internal rep object.
	 *
	 * There isn't currently enough space in the Unicode representation so
	 * allocate additional space. If the current Unicode representation
	 * isn't empty (i.e. it looks like we've done some appends) then
	 * overallocate the space so that we won't have to do as much
	 * reallocation in the future.
	 */

	if (stringPtr->uallocated > 0) {
	    uallocated *= 2;
	}
	stringPtr = (String *) ckrealloc((char*) stringPtr,
		STRING_SIZE(uallocated));
	stringPtr->uallocated = uallocated;
    }

    /*
     * Convert src to Unicode and store the coverted data in "unicode".
     */

    srcEnd = src + objPtr->length;
    for (dst = stringPtr->unicode; src < srcEnd; dst++) {
	src += TclUtfToUniChar(src, dst);
    }
    *dst = 0;

    SET_STRING(objPtr, stringPtr);
}

/*
 *----------------------------------------------------------------------
 *
 * DupStringInternalRep --
 *
 *	Initialize the internal representation of a new Tcl_Obj to a copy of
 *	the internal representation of an existing string object.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	copyPtr's internal rep is set to a copy of srcPtr's internal
 *	representation.
 *
 *----------------------------------------------------------------------
 */

static void
DupStringInternalRep(
    register Tcl_Obj *srcPtr,	/* Object with internal rep to copy. Must have
				 * an internal rep of type "String". */
    register Tcl_Obj *copyPtr)	/* Object with internal rep to set. Must not
				 * currently have an internal rep.*/
{
    String *srcStringPtr = GET_STRING(srcPtr);
    String *copyStringPtr = NULL;

    /*
     * If the src obj is a string of 1-byte Utf chars, then copy the string
     * rep of the source object and create an "empty" Unicode internal rep for
     * the new object. Otherwise, copy Unicode internal rep, and invalidate
     * the string rep of the new object.
     */

    if (srcStringPtr->hasUnicode == 0) {
	copyStringPtr = (String *) ckalloc(STRING_SIZE(STRING_UALLOC(0)));
	copyStringPtr->uallocated = STRING_UALLOC(0);
    } else {
	copyStringPtr = (String *) ckalloc(
		STRING_SIZE(srcStringPtr->uallocated));
	copyStringPtr->uallocated = srcStringPtr->uallocated;

	memcpy(copyStringPtr->unicode, srcStringPtr->unicode,
		(size_t) srcStringPtr->numChars * sizeof(Tcl_UniChar));
	copyStringPtr->unicode[srcStringPtr->numChars] = 0;
    }
    copyStringPtr->numChars = srcStringPtr->numChars;
    copyStringPtr->hasUnicode = srcStringPtr->hasUnicode;
    copyStringPtr->allocated = srcStringPtr->allocated;

    /*
     * Tricky point: the string value was copied by generic object management
     * code, so it doesn't contain any extra bytes that might exist in the
     * source object.
     */

    copyStringPtr->allocated = copyPtr->length;

    SET_STRING(copyPtr, copyStringPtr);
    copyPtr->typePtr = &tclStringType;
}

/*
 *----------------------------------------------------------------------
 *
 * SetStringFromAny --
 *
 *	Create an internal representation of type "String" for an object.
 *
 * Results:
 *	This operation always succeeds and returns TCL_OK.
 *
 * Side effects:
 *	Any old internal reputation for objPtr is freed and the internal
 *	representation is set to "String".
 *
 *----------------------------------------------------------------------
 */

static int
SetStringFromAny(
    Tcl_Interp *interp,		/* Used for error reporting if not NULL. */
    register Tcl_Obj *objPtr)	/* The object to convert. */
{
    /*
     * The Unicode object is optimized for the case where each UTF char in a
     * string is only one byte. In this case, we store the value of numChars,
     * but we don't copy the bytes to the unicodeObj->unicode.
     */

    if (objPtr->typePtr != &tclStringType) {
	String *stringPtr;

	if (objPtr->typePtr != NULL) {
	    if (objPtr->bytes == NULL) {
		objPtr->typePtr->updateStringProc(objPtr);
	    }
	    TclFreeIntRep(objPtr);
	}
	objPtr->typePtr = &tclStringType;

	/*
	 * Allocate enough space for the basic String structure.
	 */

	stringPtr = (String *) ckalloc(STRING_SIZE(STRING_UALLOC(0)));
	stringPtr->numChars = -1;
	stringPtr->uallocated = STRING_UALLOC(0);
	stringPtr->hasUnicode = 0;

	if (objPtr->bytes != NULL) {
	    stringPtr->allocated = objPtr->length;
	    objPtr->bytes[objPtr->length] = 0;
	} else {
	    objPtr->length = 0;
	}
	SET_STRING(objPtr, stringPtr);
    }
    return TCL_OK;
}

/*
 *----------------------------------------------------------------------
 *
 * UpdateStringOfString --
 *
 *	Update the string representation for an object whose internal
 *	representation is "String".
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	The object's string may be set by converting its Unicode represention
 *	to UTF format.
 *
 *----------------------------------------------------------------------
 */

static void
UpdateStringOfString(
    Tcl_Obj *objPtr)		/* Object with string rep to update. */
{
    int i, size;
    Tcl_UniChar *unicode;
    char dummy[TCL_UTF_MAX];
    char *dst;
    String *stringPtr;

    stringPtr = GET_STRING(objPtr);
    if ((objPtr->bytes == NULL) || (stringPtr->allocated == 0)) {
	if (stringPtr->numChars <= 0) {
	    /*
	     * If there is no Unicode rep, or the string has 0 chars, then set
	     * the string rep to an empty string.
	     */

	    objPtr->bytes = tclEmptyStringRep;
	    objPtr->length = 0;
	    return;
	}

	unicode = stringPtr->unicode;

	/*
	 * Translate the Unicode string to UTF. "size" will hold the amount of
	 * space the UTF string needs.
	 */

	size = 0;
	for (i = 0; i < stringPtr->numChars; i++) {
	    size += Tcl_UniCharToUtf((int) unicode[i], dummy);
	}

	dst = (char *) ckalloc((unsigned) (size + 1));
	objPtr->bytes = dst;
	objPtr->length = size;
	stringPtr->allocated = size;

	for (i = 0; i < stringPtr->numChars; i++) {
	    dst += Tcl_UniCharToUtf(unicode[i], dst);
	}
	*dst = '\0';
    }
    return;
}

/*
 *----------------------------------------------------------------------
 *
 * FreeStringInternalRep --
 *
 *	Deallocate the storage associated with a String data object's internal
 *	representation.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	Frees memory.
 *
 *----------------------------------------------------------------------
 */

static void
FreeStringInternalRep(
    Tcl_Obj *objPtr)		/* Object with internal rep to free. */
{
    ckfree((char *) GET_STRING(objPtr));
}

/*
 * Local Variables:
 * mode: c
 * c-basic-offset: 4
 * fill-column: 78
 * End:
 */
