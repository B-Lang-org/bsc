/*
 * tclBinary.c --
 *
 *	This file contains the implementation of the "binary" Tcl built-in
 *	command and the Tcl binary data object.
 *
 * Copyright (c) 1997 by Sun Microsystems, Inc.
 * Copyright (c) 1998-1999 by Scriptics Corporation.
 *
 * See the file "license.terms" for information on usage and redistribution of
 * this file, and for a DISCLAIMER OF ALL WARRANTIES.
 *
 * RCS: @(#) $Id: tclBinary.c,v 1.41 2008/03/24 03:10:06 patthoyts Exp $
 */

#include "tclInt.h"
#include "tommath.h"

#include <math.h>

/*
 * The following constants are used by GetFormatSpec to indicate various
 * special conditions in the parsing of a format specifier.
 */

#define BINARY_ALL -1		/* Use all elements in the argument. */
#define BINARY_NOCOUNT -2	/* No count was specified in format. */

/*
 * The following flags may be ORed together and returned by GetFormatSpec
 */

#define BINARY_SIGNED 0		/* Field to be read as signed data */
#define BINARY_UNSIGNED 1	/* Field to be read as unsigned data */

/*
 * The following defines the maximum number of different (integer) numbers
 * placed in the object cache by 'binary scan' before it bails out and
 * switches back to Plan A (creating a new object for each value.)
 * Theoretically, it would be possible to keep the cache about for the values
 * that are already in it, but that makes the code slower in practise when
 * overflow happens, and makes little odds the rest of the time (as measured
 * on my machine.) It is also slower (on the sample I tried at least) to grow
 * the cache to hold all items we might want to put in it; presumably the
 * extra cost of managing the memory for the enlarged table outweighs the
 * benefit from allocating fewer objects. This is probably because as the
 * number of objects increases, the likelihood of reuse of any particular one
 * drops, and there is very little gain from larger maximum cache sizes (the
 * value below is chosen to allow caching to work in full with conversion of
 * bytes.) - DKF
 */

#define BINARY_SCAN_MAX_CACHE	260

/*
 * Prototypes for local procedures defined in this file:
 */

static void		DupByteArrayInternalRep(Tcl_Obj *srcPtr,
			    Tcl_Obj *copyPtr);
static int		FormatNumber(Tcl_Interp *interp, int type,
			    Tcl_Obj *src, unsigned char **cursorPtr);
static void		FreeByteArrayInternalRep(Tcl_Obj *objPtr);
static int		GetFormatSpec(char **formatPtr, char *cmdPtr,
			    int *countPtr, int *flagsPtr);
static Tcl_Obj *	ScanNumber(unsigned char *buffer, int type,
			    int flags, Tcl_HashTable **numberCachePtr);
static int		SetByteArrayFromAny(Tcl_Interp *interp,
			    Tcl_Obj *objPtr);
static void		UpdateStringOfByteArray(Tcl_Obj *listPtr);
static void		DeleteScanNumberCache(Tcl_HashTable *numberCachePtr);
static int		NeedReversing(int format);
static void		CopyNumber(const void *from, void *to,
			    unsigned int length, int type);

/*
 * The following object type represents an array of bytes. An array of bytes
 * is not equivalent to an internationalized string. Conceptually, a string is
 * an array of 16-bit quantities organized as a sequence of properly formed
 * UTF-8 characters, while a ByteArray is an array of 8-bit quantities.
 * Accessor functions are provided to convert a ByteArray to a String or a
 * String to a ByteArray. Two or more consecutive bytes in an array of bytes
 * may look like a single UTF-8 character if the array is casually treated as
 * a string. But obtaining the String from a ByteArray is guaranteed to
 * produced properly formed UTF-8 sequences so that there is a one-to-one map
 * between bytes and characters.
 *
 * Converting a ByteArray to a String proceeds by casting each byte in the
 * array to a 16-bit quantity, treating that number as a Unicode character,
 * and storing the UTF-8 version of that Unicode character in the String. For
 * ByteArrays consisting entirely of values 1..127, the corresponding String
 * representation is the same as the ByteArray representation.
 *
 * Converting a String to a ByteArray proceeds by getting the Unicode
 * representation of each character in the String, casting it to a byte by
 * truncating the upper 8 bits, and then storing the byte in the ByteArray.
 * Converting from ByteArray to String and back to ByteArray is not lossy, but
 * converting an arbitrary String to a ByteArray may be.
 */

Tcl_ObjType tclByteArrayType = {
    "bytearray",
    FreeByteArrayInternalRep,
    DupByteArrayInternalRep,
    UpdateStringOfByteArray,
    SetByteArrayFromAny
};

/*
 * The following structure is the internal rep for a ByteArray object. Keeps
 * track of how much memory has been used and how much has been allocated for
 * the byte array to enable growing and shrinking of the ByteArray object with
 * fewer mallocs.
 */

typedef struct ByteArray {
    int used;			/* The number of bytes used in the byte
				 * array. */
    int allocated;		/* The amount of space actually allocated
				 * minus 1 byte. */
    unsigned char bytes[4];	/* The array of bytes. The actual size of this
				 * field depends on the 'allocated' field
				 * above. */
} ByteArray;

#define BYTEARRAY_SIZE(len) \
		((unsigned) (sizeof(ByteArray) - 4 + (len)))
#define GET_BYTEARRAY(objPtr) \
		((ByteArray *) (objPtr)->internalRep.otherValuePtr)
#define SET_BYTEARRAY(objPtr, baPtr) \
		(objPtr)->internalRep.otherValuePtr = (VOID *) (baPtr)


/*
 *----------------------------------------------------------------------
 *
 * Tcl_NewByteArrayObj --
 *
 *	This procedure is creates a new ByteArray object and initializes it
 *	from the given array of bytes.
 *
 * Results:
 *	The newly create object is returned. This object will have no initial
 *	string representation. The returned object has a ref count of 0.
 *
 * Side effects:
 *	Memory allocated for new object and copy of byte array argument.
 *
 *----------------------------------------------------------------------
 */

#ifdef TCL_MEM_DEBUG
#undef Tcl_NewByteArrayObj

Tcl_Obj *
Tcl_NewByteArrayObj(
    const unsigned char *bytes,	/* The array of bytes used to initialize the
				 * new object. */
    int length)			/* Length of the array of bytes, which must be
				 * >= 0. */
{
    return Tcl_DbNewByteArrayObj(bytes, length, "unknown", 0);
}

#else /* if not TCL_MEM_DEBUG */

Tcl_Obj *
Tcl_NewByteArrayObj(
    const unsigned char *bytes,	/* The array of bytes used to initialize the
				 * new object. */
    int length)			/* Length of the array of bytes, which must be
				 * >= 0. */
{
    Tcl_Obj *objPtr;

    TclNewObj(objPtr);
    Tcl_SetByteArrayObj(objPtr, bytes, length);
    return objPtr;
}
#endif /* TCL_MEM_DEBUG */

/*
 *----------------------------------------------------------------------
 *
 * Tcl_DbNewByteArrayObj --
 *
 *	This procedure is normally called when debugging: i.e., when
 *	TCL_MEM_DEBUG is defined. It is the same as the Tcl_NewByteArrayObj
 *	above except that it calls Tcl_DbCkalloc directly with the file name
 *	and line number from its caller. This simplifies debugging since then
 *	the [memory active] command will report the correct file name and line
 *	number when reporting objects that haven't been freed.
 *
 *	When TCL_MEM_DEBUG is not defined, this procedure just returns the
 *	result of calling Tcl_NewByteArrayObj.
 *
 * Results:
 *	The newly create object is returned. This object will have no initial
 *	string representation. The returned object has a ref count of 0.
 *
 * Side effects:
 *	Memory allocated for new object and copy of byte array argument.
 *
 *----------------------------------------------------------------------
 */

#ifdef TCL_MEM_DEBUG

Tcl_Obj *
Tcl_DbNewByteArrayObj(
    const unsigned char *bytes,	/* The array of bytes used to initialize the
				 * new object. */
    int length,			/* Length of the array of bytes, which must be
				 * >= 0. */
    const char *file,		/* The name of the source file calling this
				 * procedure; used for debugging. */
    int line)			/* Line number in the source file; used for
				 * debugging. */
{
    Tcl_Obj *objPtr;

    TclDbNewObj(objPtr, file, line);
    Tcl_SetByteArrayObj(objPtr, bytes, length);
    return objPtr;
}

#else /* if not TCL_MEM_DEBUG */

Tcl_Obj *
Tcl_DbNewByteArrayObj(
    const unsigned char *bytes,	/* The array of bytes used to initialize the
				 * new object. */
    int length,			/* Length of the array of bytes, which must be
				 * >= 0. */
    const char *file,		/* The name of the source file calling this
				 * procedure; used for debugging. */
    int line)			/* Line number in the source file; used for
				 * debugging. */
{
    return Tcl_NewByteArrayObj(bytes, length);
}
#endif /* TCL_MEM_DEBUG */

/*
 *---------------------------------------------------------------------------
 *
 * Tcl_SetByteArrayObj --
 *
 *	Modify an object to be a ByteArray object and to have the specified
 *	array of bytes as its value.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	The object's old string rep and internal rep is freed. Memory
 *	allocated for copy of byte array argument.
 *
 *----------------------------------------------------------------------
 */

void
Tcl_SetByteArrayObj(
    Tcl_Obj *objPtr,		/* Object to initialize as a ByteArray. */
    const unsigned char *bytes,	/* The array of bytes to use as the new
				 * value. */
    int length)			/* Length of the array of bytes, which must be
				 * >= 0. */
{
    ByteArray *byteArrayPtr;

    if (Tcl_IsShared(objPtr)) {
	Tcl_Panic("%s called with shared object", "Tcl_SetByteArrayObj");
    }
    TclFreeIntRep(objPtr);
    Tcl_InvalidateStringRep(objPtr);

    byteArrayPtr = (ByteArray *) ckalloc(BYTEARRAY_SIZE(length));
    byteArrayPtr->used = length;
    byteArrayPtr->allocated = length;
    memcpy(byteArrayPtr->bytes, bytes, (size_t) length);

    objPtr->typePtr = &tclByteArrayType;
    SET_BYTEARRAY(objPtr, byteArrayPtr);
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_GetByteArrayFromObj --
 *
 *	Attempt to get the array of bytes from the Tcl object. If the object
 *	is not already a ByteArray object, an attempt will be made to convert
 *	it to one.
 *
 * Results:
 *	Pointer to array of bytes representing the ByteArray object.
 *
 * Side effects:
 *	Frees old internal rep. Allocates memory for new internal rep.
 *
 *----------------------------------------------------------------------
 */

unsigned char *
Tcl_GetByteArrayFromObj(
    Tcl_Obj *objPtr,		/* The ByteArray object. */
    int *lengthPtr)		/* If non-NULL, filled with length of the
				 * array of bytes in the ByteArray object. */
{
    ByteArray *baPtr;

    if (objPtr->typePtr != &tclByteArrayType) {
	SetByteArrayFromAny(NULL, objPtr);
    }
    baPtr = GET_BYTEARRAY(objPtr);

    if (lengthPtr != NULL) {
	*lengthPtr = baPtr->used;
    }
    return (unsigned char *) baPtr->bytes;
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_SetByteArrayLength --
 *
 *	This procedure changes the length of the byte array for this object.
 *	Once the caller has set the length of the array, it is acceptable to
 *	directly modify the bytes in the array up until Tcl_GetStringFromObj()
 *	has been called on this object.
 *
 * Results:
 *	The new byte array of the specified length.
 *
 * Side effects:
 *	Allocates enough memory for an array of bytes of the requested size.
 *	When growing the array, the old array is copied to the new array; new
 *	bytes are undefined. When shrinking, the old array is truncated to the
 *	specified length.
 *
 *----------------------------------------------------------------------
 */

unsigned char *
Tcl_SetByteArrayLength(
    Tcl_Obj *objPtr,		/* The ByteArray object. */
    int length)			/* New length for internal byte array. */
{
    ByteArray *byteArrayPtr;

    if (Tcl_IsShared(objPtr)) {
	Tcl_Panic("%s called with shared object", "Tcl_SetByteArrayLength");
    }
    if (objPtr->typePtr != &tclByteArrayType) {
	SetByteArrayFromAny(NULL, objPtr);
    }

    byteArrayPtr = GET_BYTEARRAY(objPtr);
    if (length > byteArrayPtr->allocated) {
	byteArrayPtr = (ByteArray *) ckrealloc(
		(char *) byteArrayPtr, BYTEARRAY_SIZE(length));
	byteArrayPtr->allocated = length;
	SET_BYTEARRAY(objPtr, byteArrayPtr);
    }
    Tcl_InvalidateStringRep(objPtr);
    byteArrayPtr->used = length;
    return byteArrayPtr->bytes;
}

/*
 *----------------------------------------------------------------------
 *
 * SetByteArrayFromAny --
 *
 *	Generate the ByteArray internal rep from the string rep.
 *
 * Results:
 *	The return value is always TCL_OK.
 *
 * Side effects:
 *	A ByteArray object is stored as the internal rep of objPtr.
 *
 *----------------------------------------------------------------------
 */

static int
SetByteArrayFromAny(
    Tcl_Interp *interp,		/* Not used. */
    Tcl_Obj *objPtr)		/* The object to convert to type ByteArray. */
{
    int length;
    char *src, *srcEnd;
    unsigned char *dst;
    ByteArray *byteArrayPtr;
    Tcl_UniChar ch;

    if (objPtr->typePtr != &tclByteArrayType) {
	src = TclGetStringFromObj(objPtr, &length);
	srcEnd = src + length;

	byteArrayPtr = (ByteArray *) ckalloc(BYTEARRAY_SIZE(length));
	for (dst = byteArrayPtr->bytes; src < srcEnd; ) {
	    src += Tcl_UtfToUniChar(src, &ch);
	    *dst++ = (unsigned char) ch;
	}

	byteArrayPtr->used = dst - byteArrayPtr->bytes;
	byteArrayPtr->allocated = length;

	TclFreeIntRep(objPtr);
	objPtr->typePtr = &tclByteArrayType;
	SET_BYTEARRAY(objPtr, byteArrayPtr);
    }
    return TCL_OK;
}

/*
 *----------------------------------------------------------------------
 *
 * FreeByteArrayInternalRep --
 *
 *	Deallocate the storage associated with a ByteArray data object's
 *	internal representation.
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
FreeByteArrayInternalRep(
    Tcl_Obj *objPtr)		/* Object with internal rep to free. */
{
    ckfree((char *) GET_BYTEARRAY(objPtr));
}

/*
 *----------------------------------------------------------------------
 *
 * DupByteArrayInternalRep --
 *
 *	Initialize the internal representation of a ByteArray Tcl_Obj to a
 *	copy of the internal representation of an existing ByteArray object.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	Allocates memory.
 *
 *----------------------------------------------------------------------
 */

static void
DupByteArrayInternalRep(
    Tcl_Obj *srcPtr,		/* Object with internal rep to copy. */
    Tcl_Obj *copyPtr)		/* Object with internal rep to set. */
{
    int length;
    ByteArray *srcArrayPtr, *copyArrayPtr;

    srcArrayPtr = GET_BYTEARRAY(srcPtr);
    length = srcArrayPtr->used;

    copyArrayPtr = (ByteArray *) ckalloc(BYTEARRAY_SIZE(length));
    copyArrayPtr->used = length;
    copyArrayPtr->allocated = length;
    memcpy(copyArrayPtr->bytes, srcArrayPtr->bytes, (size_t) length);
    SET_BYTEARRAY(copyPtr, copyArrayPtr);

    copyPtr->typePtr = &tclByteArrayType;
}

/*
 *----------------------------------------------------------------------
 *
 * UpdateStringOfByteArray --
 *
 *	Update the string representation for a ByteArray data object. Note:
 *	This procedure does not invalidate an existing old string rep so
 *	storage will be lost if this has not already been done.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	The object's string is set to a valid string that results from the
 *	ByteArray-to-string conversion.
 *
 *	The object becomes a string object -- the internal rep is discarded
 *	and the typePtr becomes NULL.
 *
 *----------------------------------------------------------------------
 */

static void
UpdateStringOfByteArray(
    Tcl_Obj *objPtr)		/* ByteArray object whose string rep to
				 * update. */
{
    int i, length, size;
    unsigned char *src;
    char *dst;
    ByteArray *byteArrayPtr;

    byteArrayPtr = GET_BYTEARRAY(objPtr);
    src = byteArrayPtr->bytes;
    length = byteArrayPtr->used;

    /*
     * How much space will string rep need?
     */

    size = length;
    for (i = 0; i < length; i++) {
	if ((src[i] == 0) || (src[i] > 127)) {
	    size++;
	}
    }

    dst = (char *) ckalloc((unsigned) (size + 1));
    objPtr->bytes = dst;
    objPtr->length = size;

    if (size == length) {
	memcpy(dst, src, (size_t) size);
	dst[size] = '\0';
    } else {
	for (i = 0; i < length; i++) {
	    dst += Tcl_UniCharToUtf(src[i], dst);
	}
	*dst = '\0';
    }
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_BinaryObjCmd --
 *
 *	This procedure implements the "binary" Tcl command.
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
Tcl_BinaryObjCmd(
    ClientData dummy,		/* Not used. */
    Tcl_Interp *interp,		/* Current interpreter. */
    int objc,			/* Number of arguments. */
    Tcl_Obj *const objv[])	/* Argument objects. */
{
    int arg;			/* Index of next argument to consume. */
    int value = 0;		/* Current integer value to be packed.
				 * Initialized to avoid compiler warning. */
    char cmd;			/* Current format character. */
    int count;			/* Count associated with current format
				 * character. */
    int flags;			/* Format field flags */
    char *format;		/* Pointer to current position in format
				 * string. */
    Tcl_Obj *resultPtr = NULL;	/* Object holding result buffer. */
    unsigned char *buffer;	/* Start of result buffer. */
    unsigned char *cursor;	/* Current position within result buffer. */
    unsigned char *maxPos;	/* Greatest position within result buffer that
				 * cursor has visited.*/
    const char *errorString;
    char *errorValue, *str;
    int offset, size, length, index;
    static const char *options[] = {
	"format",	"scan",		NULL
    };
    enum options {
	BINARY_FORMAT,	BINARY_SCAN
    };

    if (objc < 2) {
    	Tcl_WrongNumArgs(interp, 1, objv, "option ?arg arg ...?");
	return TCL_ERROR;
    }

    if (Tcl_GetIndexFromObj(interp, objv[1], options, "option", 0,
	    &index) != TCL_OK) {
    	return TCL_ERROR;
    }

    switch ((enum options) index) {
    case BINARY_FORMAT:
	if (objc < 3) {
	    Tcl_WrongNumArgs(interp, 2, objv, "formatString ?arg arg ...?");
	    return TCL_ERROR;
	}

	/*
	 * To avoid copying the data, we format the string in two passes. The
	 * first pass computes the size of the output buffer. The second pass
	 * places the formatted data into the buffer.
	 */

	format = TclGetString(objv[2]);
	arg = 3;
	offset = 0;
	length = 0;
	while (*format != '\0') {
	    str = format;
	    flags = 0;
	    if (!GetFormatSpec(&format, &cmd, &count, &flags)) {
		break;
	    }
	    switch (cmd) {
	    case 'a':
	    case 'A':
	    case 'b':
	    case 'B':
	    case 'h':
	    case 'H':
		/*
		 * For string-type specifiers, the count corresponds to the
		 * number of bytes in a single argument.
		 */

		if (arg >= objc) {
		    goto badIndex;
		}
		if (count == BINARY_ALL) {
		    Tcl_GetByteArrayFromObj(objv[arg], &count);
		} else if (count == BINARY_NOCOUNT) {
		    count = 1;
		}
		arg++;
		if (cmd == 'a' || cmd == 'A') {
		    offset += count;
		} else if (cmd == 'b' || cmd == 'B') {
		    offset += (count + 7) / 8;
		} else {
		    offset += (count + 1) / 2;
		}
		break;
	    case 'c':
		size = 1;
		goto doNumbers;
	    case 't':
	    case 's':
	    case 'S':
		size = 2;
		goto doNumbers;
	    case 'n':
	    case 'i':
	    case 'I':
		size = 4;
		goto doNumbers;
	    case 'm':
	    case 'w':
	    case 'W':
		size = 8;
		goto doNumbers;
	    case 'r':
	    case 'R':
	    case 'f':
		size = sizeof(float);
		goto doNumbers;
	    case 'q':
	    case 'Q':
	    case 'd':
		size = sizeof(double);

	    doNumbers:
		if (arg >= objc) {
		    goto badIndex;
		}

		/*
		 * For number-type specifiers, the count corresponds to the
		 * number of elements in the list stored in a single argument.
		 * If no count is specified, then the argument is taken as a
		 * single non-list value.
		 */

		if (count == BINARY_NOCOUNT) {
		    arg++;
		    count = 1;
		} else {
		    int listc;
		    Tcl_Obj **listv;

		    /* The macro evals its args more than once: avoid arg++ */		    
		    if (TclListObjGetElements(interp, objv[arg], &listc,
			    &listv) != TCL_OK) {
			return TCL_ERROR;
		    }
		    arg++;
		    
		    if (count == BINARY_ALL) {
			count = listc;
		    } else if (count > listc) {
			Tcl_AppendResult(interp,
				"number of elements in list does not match count",
				NULL);
			return TCL_ERROR;
		    }
		}
		offset += count*size;
		break;

	    case 'x':
		if (count == BINARY_ALL) {
		    Tcl_AppendResult(interp,
			    "cannot use \"*\" in format string with \"x\"",
			    NULL);
		    return TCL_ERROR;
		} else if (count == BINARY_NOCOUNT) {
		    count = 1;
		}
		offset += count;
		break;
	    case 'X':
		if (count == BINARY_NOCOUNT) {
		    count = 1;
		}
		if ((count > offset) || (count == BINARY_ALL)) {
		    count = offset;
		}
		if (offset > length) {
		    length = offset;
		}
		offset -= count;
		break;
	    case '@':
		if (offset > length) {
		    length = offset;
		}
		if (count == BINARY_ALL) {
		    offset = length;
		} else if (count == BINARY_NOCOUNT) {
		    goto badCount;
		} else {
		    offset = count;
		}
		break;
	    default:
		errorString = str;
		goto badField;
	    }
	}
	if (offset > length) {
	    length = offset;
	}
	if (length == 0) {
	    return TCL_OK;
	}

	/*
	 * Prepare the result object by preallocating the caclulated number of
	 * bytes and filling with nulls.
	 */

	resultPtr = Tcl_NewObj();
	buffer = Tcl_SetByteArrayLength(resultPtr, length);
	memset(buffer, 0, (size_t) length);

	/*
	 * Pack the data into the result object. Note that we can skip the
	 * error checking during this pass, since we have already parsed the
	 * string once.
	 */

	arg = 3;
	format = TclGetString(objv[2]);
	cursor = buffer;
	maxPos = cursor;
	while (*format != 0) {
	    flags = 0;
	    if (!GetFormatSpec(&format, &cmd, &count, &flags)) {
		break;
	    }
	    if ((count == 0) && (cmd != '@')) {
		if (cmd != 'x') {
		    arg++;
		}
		continue;
	    }
	    switch (cmd) {
	    case 'a':
	    case 'A': {
		char pad = (char) (cmd == 'a' ? '\0' : ' ');
		unsigned char *bytes;

		bytes = Tcl_GetByteArrayFromObj(objv[arg++], &length);

		if (count == BINARY_ALL) {
		    count = length;
		} else if (count == BINARY_NOCOUNT) {
		    count = 1;
		}
		if (length >= count) {
		    memcpy(cursor, bytes, (size_t) count);
		} else {
		    memcpy(cursor, bytes, (size_t) length);
		    memset(cursor + length, pad, (size_t) (count - length));
		}
		cursor += count;
		break;
	    }
	    case 'b':
	    case 'B': {
		unsigned char *last;

		str = TclGetStringFromObj(objv[arg], &length);
		arg++;
		if (count == BINARY_ALL) {
		    count = length;
		} else if (count == BINARY_NOCOUNT) {
		    count = 1;
		}
		last = cursor + ((count + 7) / 8);
		if (count > length) {
		    count = length;
		}
		value = 0;
		errorString = "binary";
		if (cmd == 'B') {
		    for (offset = 0; offset < count; offset++) {
			value <<= 1;
			if (str[offset] == '1') {
			    value |= 1;
			} else if (str[offset] != '0') {
			    errorValue = str;
			    Tcl_DecrRefCount(resultPtr);
			    goto badValue;
			}
			if (((offset + 1) % 8) == 0) {
			    *cursor++ = (unsigned char) value;
			    value = 0;
			}
		    }
		} else {
		    for (offset = 0; offset < count; offset++) {
			value >>= 1;
			if (str[offset] == '1') {
			    value |= 128;
			} else if (str[offset] != '0') {
			    errorValue = str;
			    Tcl_DecrRefCount(resultPtr);
			    goto badValue;
			}
			if (!((offset + 1) % 8)) {
			    *cursor++ = (unsigned char) value;
			    value = 0;
			}
		    }
		}
		if ((offset % 8) != 0) {
		    if (cmd == 'B') {
			value <<= 8 - (offset % 8);
		    } else {
			value >>= 8 - (offset % 8);
		    }
		    *cursor++ = (unsigned char) value;
		}
		while (cursor < last) {
		    *cursor++ = '\0';
		}
		break;
	    }
	    case 'h':
	    case 'H': {
		unsigned char *last;
		int c;

		str = TclGetStringFromObj(objv[arg], &length);
		arg++;
		if (count == BINARY_ALL) {
		    count = length;
		} else if (count == BINARY_NOCOUNT) {
		    count = 1;
		}
		last = cursor + ((count + 1) / 2);
		if (count > length) {
		    count = length;
		}
		value = 0;
		errorString = "hexadecimal";
		if (cmd == 'H') {
		    for (offset = 0; offset < count; offset++) {
			value <<= 4;
			if (!isxdigit(UCHAR(str[offset]))) { /* INTL: digit */
			    errorValue = str;
			    Tcl_DecrRefCount(resultPtr);
			    goto badValue;
			}
			c = str[offset] - '0';
			if (c > 9) {
			    c += ('0' - 'A') + 10;
			}
			if (c > 16) {
			    c += ('A' - 'a');
			}
			value |= (c & 0xf);
			if (offset % 2) {
			    *cursor++ = (char) value;
			    value = 0;
			}
		    }
		} else {
		    for (offset = 0; offset < count; offset++) {
			value >>= 4;

			if (!isxdigit(UCHAR(str[offset]))) { /* INTL: digit */
			    errorValue = str;
			    Tcl_DecrRefCount(resultPtr);
			    goto badValue;
			}
			c = str[offset] - '0';
			if (c > 9) {
			    c += ('0' - 'A') + 10;
			}
			if (c > 16) {
			    c += ('A' - 'a');
			}
			value |= ((c << 4) & 0xf0);
			if (offset % 2) {
			    *cursor++ = (unsigned char)(value & 0xff);
			    value = 0;
			}
		    }
		}
		if (offset % 2) {
		    if (cmd == 'H') {
			value <<= 4;
		    } else {
			value >>= 4;
		    }
		    *cursor++ = (unsigned char) value;
		}

		while (cursor < last) {
		    *cursor++ = '\0';
		}
		break;
	    }
	    case 'c':
	    case 't':
	    case 's':
	    case 'S':
	    case 'n':
	    case 'i':
	    case 'I':
	    case 'm':
	    case 'w':
	    case 'W':
	    case 'r':
	    case 'R':
	    case 'd':
	    case 'q':
	    case 'Q':
	    case 'f': {
		int listc, i;
		Tcl_Obj **listv;

		if (count == BINARY_NOCOUNT) {
		    /*
		     * Note that we are casting away the const-ness of objv,
		     * but this is safe since we aren't going to modify the
		     * array.
		     */

		    listv = (Tcl_Obj**)(objv + arg);
		    listc = 1;
		    count = 1;
		} else {
		    TclListObjGetElements(interp, objv[arg], &listc, &listv);
		    if (count == BINARY_ALL) {
			count = listc;
		    }
		}
		arg++;
		for (i = 0; i < count; i++) {
		    if (FormatNumber(interp, cmd, listv[i], &cursor)!=TCL_OK) {
			Tcl_DecrRefCount(resultPtr);
			return TCL_ERROR;
		    }
		}
		break;
	    }
	    case 'x':
		if (count == BINARY_NOCOUNT) {
		    count = 1;
		}
		memset(cursor, 0, (size_t) count);
		cursor += count;
		break;
	    case 'X':
		if (cursor > maxPos) {
		    maxPos = cursor;
		}
		if (count == BINARY_NOCOUNT) {
		    count = 1;
		}
		if ((count == BINARY_ALL) || (count > (cursor - buffer))) {
		    cursor = buffer;
		} else {
		    cursor -= count;
		}
		break;
	    case '@':
		if (cursor > maxPos) {
		    maxPos = cursor;
		}
		if (count == BINARY_ALL) {
		    cursor = maxPos;
		} else {
		    cursor = buffer + count;
		}
		break;
	    }
	}
	Tcl_SetObjResult(interp, resultPtr);
	break;
    case BINARY_SCAN: {
	int i;
	Tcl_Obj *valuePtr, *elementPtr;
	Tcl_HashTable numberCacheHash;
	Tcl_HashTable *numberCachePtr;

	if (objc < 4) {
	    Tcl_WrongNumArgs(interp, 2, objv,
		    "value formatString ?varName varName ...?");
	    return TCL_ERROR;
	}
	numberCachePtr = &numberCacheHash;
	Tcl_InitHashTable(numberCachePtr, TCL_ONE_WORD_KEYS);
	buffer = Tcl_GetByteArrayFromObj(objv[2], &length);
	format = TclGetString(objv[3]);
	cursor = buffer;
	arg = 4;
	offset = 0;
	while (*format != '\0') {
	    str = format;
	    flags = 0;
	    if (!GetFormatSpec(&format, &cmd, &count, &flags)) {
		goto done;
	    }
	    switch (cmd) {
	    case 'a':
	    case 'A': {
		unsigned char *src;

		if (arg >= objc) {
		    DeleteScanNumberCache(numberCachePtr);
		    goto badIndex;
		}
		if (count == BINARY_ALL) {
		    count = length - offset;
		} else {
		    if (count == BINARY_NOCOUNT) {
			count = 1;
		    }
		    if (count > (length - offset)) {
			goto done;
		    }
		}

		src = buffer + offset;
		size = count;

		/*
		 * Trim trailing nulls and spaces, if necessary.
		 */

		if (cmd == 'A') {
		    while (size > 0) {
			if (src[size-1] != '\0' && src[size-1] != ' ') {
			    break;
			}
			size--;
		    }
		}

		/*
		 * Have to do this #ifdef-fery because (as part of defining
		 * Tcl_NewByteArrayObj) we removed the #def that hides this
		 * stuff normally. If this code ever gets copied to another
		 * file, it should be changed back to the simpler version.
		 */

#ifdef TCL_MEM_DEBUG
		valuePtr = Tcl_DbNewByteArrayObj(src, size, __FILE__,__LINE__);
#else
		valuePtr = Tcl_NewByteArrayObj(src, size);
#endif /* TCL_MEM_DEBUG */

		resultPtr = Tcl_ObjSetVar2(interp, objv[arg], NULL, valuePtr,
			TCL_LEAVE_ERR_MSG);
		arg++;
		if (resultPtr == NULL) {
		    DeleteScanNumberCache(numberCachePtr);
		    return TCL_ERROR;
		}
		offset += count;
		break;
	    }
	    case 'b':
	    case 'B': {
		unsigned char *src;
		char *dest;

		if (arg >= objc) {
		    DeleteScanNumberCache(numberCachePtr);
		    goto badIndex;
		}
		if (count == BINARY_ALL) {
		    count = (length - offset) * 8;
		} else {
		    if (count == BINARY_NOCOUNT) {
			count = 1;
		    }
		    if (count > (length - offset) * 8) {
			goto done;
		    }
		}
		src = buffer + offset;
		valuePtr = Tcl_NewObj();
		Tcl_SetObjLength(valuePtr, count);
		dest = TclGetString(valuePtr);

		if (cmd == 'b') {
		    for (i = 0; i < count; i++) {
			if (i % 8) {
			    value >>= 1;
			} else {
			    value = *src++;
			}
			*dest++ = (char) ((value & 1) ? '1' : '0');
		    }
		} else {
		    for (i = 0; i < count; i++) {
			if (i % 8) {
			    value <<= 1;
			} else {
			    value = *src++;
			}
			*dest++ = (char) ((value & 0x80) ? '1' : '0');
		    }
		}

		resultPtr = Tcl_ObjSetVar2(interp, objv[arg], NULL, valuePtr,
			TCL_LEAVE_ERR_MSG);
		arg++;
		if (resultPtr == NULL) {
		    DeleteScanNumberCache(numberCachePtr);
		    return TCL_ERROR;
		}
		offset += (count + 7) / 8;
		break;
	    }
	    case 'h':
	    case 'H': {
		char *dest;
		unsigned char *src;
		int i;
		static const char hexdigit[] = "0123456789abcdef";

		if (arg >= objc) {
		    DeleteScanNumberCache(numberCachePtr);
		    goto badIndex;
		}
		if (count == BINARY_ALL) {
		    count = (length - offset)*2;
		} else {
		    if (count == BINARY_NOCOUNT) {
			count = 1;
		    }
		    if (count > (length - offset)*2) {
			goto done;
		    }
		}
		src = buffer + offset;
		valuePtr = Tcl_NewObj();
		Tcl_SetObjLength(valuePtr, count);
		dest = TclGetString(valuePtr);

		if (cmd == 'h') {
		    for (i = 0; i < count; i++) {
			if (i % 2) {
			    value >>= 4;
			} else {
			    value = *src++;
			}
			*dest++ = hexdigit[value & 0xf];
		    }
		} else {
		    for (i = 0; i < count; i++) {
			if (i % 2) {
			    value <<= 4;
			} else {
			    value = *src++;
			}
			*dest++ = hexdigit[(value >> 4) & 0xf];
		    }
		}

		resultPtr = Tcl_ObjSetVar2(interp, objv[arg], NULL, valuePtr,
			TCL_LEAVE_ERR_MSG);
		arg++;
		if (resultPtr == NULL) {
		    DeleteScanNumberCache(numberCachePtr);
		    return TCL_ERROR;
		}
		offset += (count + 1) / 2;
		break;
	    }
	    case 'c':
		size = 1;
		goto scanNumber;
	    case 't':
	    case 's':
	    case 'S':
		size = 2;
		goto scanNumber;
	    case 'n':
	    case 'i':
	    case 'I':
		size = 4;
		goto scanNumber;
	    case 'm':
	    case 'w':
	    case 'W':
		size = 8;
		goto scanNumber;
	    case 'r':
	    case 'R':
	    case 'f':
		size = sizeof(float);
		goto scanNumber;
	    case 'q':
	    case 'Q':
	    case 'd': {
		unsigned char *src;

		size = sizeof(double);
		/* fall through */

	    scanNumber:
		if (arg >= objc) {
		    DeleteScanNumberCache(numberCachePtr);
		    goto badIndex;
		}
		if (count == BINARY_NOCOUNT) {
		    if ((length - offset) < size) {
			goto done;
		    }
		    valuePtr = ScanNumber(buffer+offset, cmd, flags,
			    &numberCachePtr);
		    offset += size;
		} else {
		    if (count == BINARY_ALL) {
			count = (length - offset) / size;
		    }
		    if ((length - offset) < (count * size)) {
			goto done;
		    }
		    valuePtr = Tcl_NewObj();
		    src = buffer+offset;
		    for (i = 0; i < count; i++) {
			elementPtr = ScanNumber(src, cmd, flags,
				&numberCachePtr);
			src += size;
			Tcl_ListObjAppendElement(NULL, valuePtr, elementPtr);
		    }
		    offset += count*size;
		}

		resultPtr = Tcl_ObjSetVar2(interp, objv[arg], NULL, valuePtr,
			TCL_LEAVE_ERR_MSG);
		arg++;
		if (resultPtr == NULL) {
		    DeleteScanNumberCache(numberCachePtr);
		    return TCL_ERROR;
		}
		break;
	    }
	    case 'x':
		if (count == BINARY_NOCOUNT) {
		    count = 1;
		}
		if ((count == BINARY_ALL) || (count > (length - offset))) {
		    offset = length;
		} else {
		    offset += count;
		}
		break;
	    case 'X':
		if (count == BINARY_NOCOUNT) {
		    count = 1;
		}
		if ((count == BINARY_ALL) || (count > offset)) {
		    offset = 0;
		} else {
		    offset -= count;
		}
		break;
	    case '@':
		if (count == BINARY_NOCOUNT) {
		    DeleteScanNumberCache(numberCachePtr);
		    goto badCount;
		}
		if ((count == BINARY_ALL) || (count > length)) {
		    offset = length;
		} else {
		    offset = count;
		}
		break;
	    default:
		DeleteScanNumberCache(numberCachePtr);
		errorString = str;
		goto badField;
	    }
	}

	/*
	 * Set the result to the last position of the cursor.
	 */

    done:
	Tcl_SetObjResult(interp, Tcl_NewLongObj(arg - 4));
	DeleteScanNumberCache(numberCachePtr);
	break;
    }
    }
    return TCL_OK;

  badValue:
    Tcl_ResetResult(interp);
    Tcl_AppendResult(interp, "expected ", errorString,
	    " string but got \"", errorValue, "\" instead", NULL);
    return TCL_ERROR;

  badCount:
    errorString = "missing count for \"@\" field specifier";
    goto error;

  badIndex:
    errorString = "not enough arguments for all format specifiers";
    goto error;

  badField:
    {
	Tcl_UniChar ch;
	char buf[TCL_UTF_MAX + 1];

	Tcl_UtfToUniChar(errorString, &ch);
	buf[Tcl_UniCharToUtf(ch, buf)] = '\0';
	Tcl_AppendResult(interp, "bad field specifier \"", buf, "\"", NULL);
	return TCL_ERROR;
    }

  error:
    Tcl_AppendResult(interp, errorString, NULL);
    return TCL_ERROR;
}

/*
 *----------------------------------------------------------------------
 *
 * GetFormatSpec --
 *
 *	This function parses the format strings used in the binary format and
 *	scan commands.
 *
 * Results:
 *	Moves the formatPtr to the start of the next command. Returns the
 *	current command character and count in cmdPtr and countPtr. The count
 *	is set to BINARY_ALL if the count character was '*' or BINARY_NOCOUNT
 *	if no count was specified. Returns 1 on success, or 0 if the string
 *	did not have a format specifier.
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */

static int
GetFormatSpec(
    char **formatPtr,		/* Pointer to format string. */
    char *cmdPtr,		/* Pointer to location of command char. */
    int *countPtr,		/* Pointer to repeat count value. */
    int *flagsPtr)		/* Pointer to field flags */
{
    /*
     * Skip any leading blanks.
     */

    while (**formatPtr == ' ') {
	(*formatPtr)++;
    }

    /*
     * The string was empty, except for whitespace, so fail.
     */

    if (!(**formatPtr)) {
	return 0;
    }

    /*
     * Extract the command character and any trailing digits or '*'.
     */

    *cmdPtr = **formatPtr;
    (*formatPtr)++;
    if (**formatPtr == 'u') {
	(*formatPtr)++;
	(*flagsPtr) |= BINARY_UNSIGNED;
    }
    if (**formatPtr == '*') {
	(*formatPtr)++;
	(*countPtr) = BINARY_ALL;
    } else if (isdigit(UCHAR(**formatPtr))) { /* INTL: digit */
	(*countPtr) = strtoul(*formatPtr, formatPtr, 10);
    } else {
	(*countPtr) = BINARY_NOCOUNT;
    }
    return 1;
}

/*
 *----------------------------------------------------------------------
 *
 * NeedReversing --
 *
 *	This routine determines, if bytes of a number need to be re-ordered,
 *	and returns a numeric code indicating the re-ordering to be done.
 *	This depends on the endiannes of the machine and the desired format.
 *	It is in effect a table (whose contents depend on the endianness of
 *	the system) describing whether a value needs reversing or not. Anyone
 *	porting the code to a big-endian platform should take care to make
 *	sure that they define WORDS_BIGENDIAN though this is already done by
 *	configure for the Unix build; little-endian platforms (including
 *	Windows) don't need to do anything.
 *
 * Results:
 *	0	No re-ordering needed.
 *	1	Reverse the bytes:	01234567 <-> 76543210 (little to big)
 *	2	Apply this re-ordering: 01234567 <-> 45670123 (Nokia to little)
 *	3	Apply this re-ordering: 01234567 <-> 32107654 (Nokia to big)
 *
 * Side effects:
 *	None
 *
 *----------------------------------------------------------------------
 */

static int
NeedReversing(
    int format)
{
    switch (format) {
	/* native floats and doubles: never reverse */
    case 'd':
    case 'f':
	/* big endian ints: never reverse */
    case 'I':
    case 'S':
    case 'W':
#ifdef WORDS_BIGENDIAN
	/* native ints: reverse if we're little-endian */
    case 'n':
    case 't':
    case 'm':
	/* f: reverse if we're little-endian */
    case 'Q':
    case 'R':
#else /* !WORDS_BIGENDIAN */
	/* small endian floats: reverse if we're big-endian */
    case 'r':
#endif /* WORDS_BIGENDIAN */
	return 0;

#ifdef WORDS_BIGENDIAN
	/* small endian floats: reverse if we're big-endian */
    case 'q':
    case 'r':
#else /* !WORDS_BIGENDIAN */
	/* native ints: reverse if we're little-endian */
    case 'n':
    case 't':
    case 'm':
	/* f: reverse if we're little-endian */
    case 'R':
#endif /* WORDS_BIGENDIAN */
	/* small endian ints: always reverse */
    case 'i':
    case 's':
    case 'w':
	return 1;

#ifndef WORDS_BIGENDIAN
    /*
     * The Q and q formats need special handling to account for the unusual
     * byte ordering of 8-byte floats on Nokia 770 systems, which claim to be
     * little-endian, but also reverse word order.
     */

    case 'Q':
	if (TclNokia770Doubles()) {
	    return 3;
	}
	return 1;
    case 'q':
	if (TclNokia770Doubles()) {
	    return 2;
	}
	return 0;
#endif
    }

    Tcl_Panic("unexpected fallthrough");
    return 0;
}

/*
 *----------------------------------------------------------------------
 *
 * CopyNumber --
 *
 *	This routine is called by FormatNumber and ScanNumber to copy a
 *	floating-point number. If required, bytes are reversed while copying.
 *	The behaviour is only fully defined when used with IEEE float and
 *	double values (guaranteed to be 4 and 8 bytes long, respectively.)
 *
 * Results:
 *	None
 *
 * Side effects:
 *	Copies length bytes
 *
 *----------------------------------------------------------------------
 */

static void
CopyNumber(
    const void *from,		/* source */
    void *to,			/* destination */
    unsigned int length,	/* Number of bytes to copy */
    int type)			/* What type of thing are we copying? */
{
    switch (NeedReversing(type)) {
    case 0: 
	memcpy(to, from, length);
	break;
    case 1: {
	const unsigned char *fromPtr = from;
	unsigned char *toPtr = to;

	switch (length) {
	case 4:
	    toPtr[0] = fromPtr[3];
	    toPtr[1] = fromPtr[2];
	    toPtr[2] = fromPtr[1];
	    toPtr[3] = fromPtr[0];
	    break;
	case 8:
	    toPtr[0] = fromPtr[7];
	    toPtr[1] = fromPtr[6];
	    toPtr[2] = fromPtr[5];
	    toPtr[3] = fromPtr[4];
	    toPtr[4] = fromPtr[3];
	    toPtr[5] = fromPtr[2];
	    toPtr[6] = fromPtr[1];
	    toPtr[7] = fromPtr[0];
	    break;
	}
	break;
    }
    case 2: {
	const unsigned char *fromPtr = from;
	unsigned char *toPtr = to;

	toPtr[0] = fromPtr[4];
	toPtr[1] = fromPtr[5];
	toPtr[2] = fromPtr[6];
	toPtr[3] = fromPtr[7];
	toPtr[4] = fromPtr[0];
	toPtr[5] = fromPtr[1];
	toPtr[6] = fromPtr[2];
	toPtr[7] = fromPtr[3];
	break;
    }
    case 3: {
	const unsigned char *fromPtr = from;
	unsigned char *toPtr = to;

	toPtr[0] = fromPtr[3];
	toPtr[1] = fromPtr[2];
	toPtr[2] = fromPtr[1];
	toPtr[3] = fromPtr[0];
	toPtr[4] = fromPtr[7];
	toPtr[5] = fromPtr[6];
	toPtr[6] = fromPtr[5];
	toPtr[7] = fromPtr[4];
	break;
    }
    }
}

/*
 *----------------------------------------------------------------------
 *
 * FormatNumber --
 *
 *	This routine is called by Tcl_BinaryObjCmd to format a number into a
 *	location pointed at by cursor.
 *
 * Results:
 *	A standard Tcl result.
 *
 * Side effects:
 *	Moves the cursor to the next location to be written into.
 *
 *----------------------------------------------------------------------
 */

static int
FormatNumber(
    Tcl_Interp *interp,		/* Current interpreter, used to report
				 * errors. */
    int type,			/* Type of number to format. */
    Tcl_Obj *src,		/* Number to format. */
    unsigned char **cursorPtr)	/* Pointer to index into destination buffer. */
{
    long value;
    double dvalue;
    Tcl_WideInt wvalue;
    float fvalue;

    switch (type) {
    case 'd':
    case 'q':
    case 'Q':
	/*
	 * Double-precision floating point values. Tcl_GetDoubleFromObj
	 * returns TCL_ERROR for NaN, but we can check by comparing the
	 * object's type pointer.
	 */

	if (Tcl_GetDoubleFromObj(interp, src, &dvalue) != TCL_OK) {
	    if (src->typePtr != &tclDoubleType) {
		return TCL_ERROR;
	    }
	    dvalue = src->internalRep.doubleValue;
	}
	CopyNumber(&dvalue, *cursorPtr, sizeof(double), type);
	*cursorPtr += sizeof(double);
	return TCL_OK;

    case 'f':
    case 'r':
    case 'R':
	/*
	 * Single-precision floating point values. Tcl_GetDoubleFromObj
	 * returns TCL_ERROR for NaN, but we can check by comparing the
	 * object's type pointer.
	 */

	if (Tcl_GetDoubleFromObj(interp, src, &dvalue) != TCL_OK) {
	    if (src->typePtr != &tclDoubleType) {
		return TCL_ERROR;
	    }
	    dvalue = src->internalRep.doubleValue;
	}

	/*
	 * Because some compilers will generate floating point exceptions on
	 * an overflow cast (e.g. Borland), we restrict the values to the
	 * valid range for float.
	 */

	if (fabs(dvalue) > (double)FLT_MAX) {
	    fvalue = (dvalue >= 0.0) ? FLT_MAX : -FLT_MAX;
	} else {
	    fvalue = (float) dvalue;
	}
	CopyNumber(&fvalue, *cursorPtr, sizeof(float), type);
	*cursorPtr += sizeof(float);
	return TCL_OK;

	/*
	 * 64-bit integer values.
	 */
    case 'w':
    case 'W':
    case 'm':
	if (Tcl_GetWideIntFromObj(interp, src, &wvalue) != TCL_OK) {
	    return TCL_ERROR;
	}
	if (NeedReversing(type)) {
	    *(*cursorPtr)++ = (unsigned char) wvalue;
	    *(*cursorPtr)++ = (unsigned char) (wvalue >> 8);
	    *(*cursorPtr)++ = (unsigned char) (wvalue >> 16);
	    *(*cursorPtr)++ = (unsigned char) (wvalue >> 24);
	    *(*cursorPtr)++ = (unsigned char) (wvalue >> 32);
	    *(*cursorPtr)++ = (unsigned char) (wvalue >> 40);
	    *(*cursorPtr)++ = (unsigned char) (wvalue >> 48);
	    *(*cursorPtr)++ = (unsigned char) (wvalue >> 56);
	} else {
	    *(*cursorPtr)++ = (unsigned char) (wvalue >> 56);
	    *(*cursorPtr)++ = (unsigned char) (wvalue >> 48);
	    *(*cursorPtr)++ = (unsigned char) (wvalue >> 40);
	    *(*cursorPtr)++ = (unsigned char) (wvalue >> 32);
	    *(*cursorPtr)++ = (unsigned char) (wvalue >> 24);
	    *(*cursorPtr)++ = (unsigned char) (wvalue >> 16);
	    *(*cursorPtr)++ = (unsigned char) (wvalue >> 8);
	    *(*cursorPtr)++ = (unsigned char) wvalue;
	}
	return TCL_OK;

	/*
	 * 32-bit integer values.
	 */
    case 'i':
    case 'I':
    case 'n':
	if (TclGetLongFromObj(interp, src, &value) != TCL_OK) {
	    return TCL_ERROR;
	}
	if (NeedReversing(type)) {
	    *(*cursorPtr)++ = (unsigned char) value;
	    *(*cursorPtr)++ = (unsigned char) (value >> 8);
	    *(*cursorPtr)++ = (unsigned char) (value >> 16);
	    *(*cursorPtr)++ = (unsigned char) (value >> 24);
	} else {
	    *(*cursorPtr)++ = (unsigned char) (value >> 24);
	    *(*cursorPtr)++ = (unsigned char) (value >> 16);
	    *(*cursorPtr)++ = (unsigned char) (value >> 8);
	    *(*cursorPtr)++ = (unsigned char) value;
	}
	return TCL_OK;

	/*
	 * 16-bit integer values.
	 */
    case 's':
    case 'S':
    case 't':
	if (TclGetLongFromObj(interp, src, &value) != TCL_OK) {
	    return TCL_ERROR;
	}
	if (NeedReversing(type)) {
	    *(*cursorPtr)++ = (unsigned char) value;
	    *(*cursorPtr)++ = (unsigned char) (value >> 8);
	} else {
	    *(*cursorPtr)++ = (unsigned char) (value >> 8);
	    *(*cursorPtr)++ = (unsigned char) value;
	}
	return TCL_OK;

	/*
	 * 8-bit integer values.
	 */
    case 'c':
	if (TclGetLongFromObj(interp, src, &value) != TCL_OK) {
	    return TCL_ERROR;
	}
	*(*cursorPtr)++ = (unsigned char) value;
	return TCL_OK;

    default:
	Tcl_Panic("unexpected fallthrough");
	return TCL_ERROR;
    }
}

/*
 *----------------------------------------------------------------------
 *
 * ScanNumber --
 *
 *	This routine is called by Tcl_BinaryObjCmd to scan a number out of a
 *	buffer.
 *
 * Results:
 *	Returns a newly created object containing the scanned number. This
 *	object has a ref count of zero.
 *
 * Side effects:
 *	Might reuse an object in the number cache, place a new object in the
 *	cache, or delete the cache and set the reference to it (itself passed
 *	in by reference) to NULL.
 *
 *----------------------------------------------------------------------
 */

static Tcl_Obj *
ScanNumber(
    unsigned char *buffer,	/* Buffer to scan number from. */
    int type,			/* Format character from "binary scan" */
    int flags,			/* Format field flags */
    Tcl_HashTable **numberCachePtrPtr)
				/* Place to look for cache of scanned
				 * value objects, or NULL if too many
				 * different numbers have been scanned. */
{
    long value;
    float fvalue;
    double dvalue;
    Tcl_WideUInt uwvalue;

    /*
     * We cannot rely on the compiler to properly sign extend integer values
     * when we cast from smaller values to larger values because we don't know
     * the exact size of the integer types. So, we have to handle sign
     * extension explicitly by checking the high bit and padding with 1's as
     * needed. This practice is disabled if the BINARY_UNSIGNED flag is set.
     */

    switch (type) {
    case 'c':
	/*
	 * Characters need special handling. We want to produce a signed
	 * result, but on some platforms (such as AIX) chars are unsigned. To
	 * deal with this, check for a value that should be negative but
	 * isn't.
	 */

	value = buffer[0];
	if (!(flags & BINARY_UNSIGNED)) {
	    if (value & 0x80) {
		value |= -0x100;
	    }
	}
	goto returnNumericObject;

	/*
	 * 16-bit numeric values. We need the sign extension trick (see above)
	 * here as well.
	 */

    case 's':
    case 'S':
    case 't':
	if (NeedReversing(type)) {
	    value = (long) (buffer[0] + (buffer[1] << 8));
	} else {
	    value = (long) (buffer[1] + (buffer[0] << 8));
	}
	if (!(flags & BINARY_UNSIGNED)) {
	    if (value & 0x8000) {
		value |= -0x10000;
	    }
	}
	goto returnNumericObject;

	/*
	 * 32-bit numeric values.
	 */

    case 'i':
    case 'I':
    case 'n':
	if (NeedReversing(type)) {
	    value = (long) (buffer[0]
		    + (buffer[1] << 8)
		    + (buffer[2] << 16)
		    + (((long)buffer[3]) << 24));
	} else {
	    value = (long) (buffer[3]
		    + (buffer[2] << 8)
		    + (buffer[1] << 16)
		    + (((long)buffer[0]) << 24));
	}

	/*
	 * Check to see if the value was sign extended properly on systems
	 * where an int is more than 32-bits.
	 * We avoid caching unsigned integers as we cannot distinguish between
	 * 32bit signed and unsigned in the hash (short and char are ok).
	 */

	if (flags & BINARY_UNSIGNED) {
	    return Tcl_NewWideIntObj((Tcl_WideInt)(unsigned long)value);
	}
	if ((value & (((unsigned int)1)<<31)) && (value > 0)) {
	    value -= (((unsigned int)1)<<31);
	    value -= (((unsigned int)1)<<31);
	}

    returnNumericObject:
	if (*numberCachePtrPtr == NULL) {
	    return Tcl_NewLongObj(value);
	} else {
	    register Tcl_HashTable *tablePtr = *numberCachePtrPtr;
	    register Tcl_HashEntry *hPtr;
	    int isNew;

	    hPtr = Tcl_CreateHashEntry(tablePtr, (char *)value, &isNew);
	    if (!isNew) {
		return (Tcl_Obj *) Tcl_GetHashValue(hPtr);
	    }
	    if (tablePtr->numEntries <= BINARY_SCAN_MAX_CACHE) {
		register Tcl_Obj *objPtr = Tcl_NewLongObj(value);

		Tcl_IncrRefCount(objPtr);
		Tcl_SetHashValue(hPtr, (ClientData) objPtr);
		return objPtr;
	    }

	    /*
	     * We've overflowed the cache! Someone's parsing a LOT of varied
	     * binary data in a single call! Bail out by switching back to the
	     * old behaviour for the rest of the scan.
	     *
	     * Note that anyone just using the 'c' conversion (for bytes)
	     * cannot trigger this.
	     */

	    DeleteScanNumberCache(tablePtr);
	    *numberCachePtrPtr = NULL;
	    return Tcl_NewLongObj(value);
	}

	/*
	 * Do not cache wide (64-bit) values; they are already too large to
	 * use as keys.
	 */

    case 'w':
    case 'W':
    case 'm':
	if (NeedReversing(type)) {
	    uwvalue = ((Tcl_WideUInt) buffer[0])
		    | (((Tcl_WideUInt) buffer[1]) << 8)
		    | (((Tcl_WideUInt) buffer[2]) << 16)
		    | (((Tcl_WideUInt) buffer[3]) << 24)
		    | (((Tcl_WideUInt) buffer[4]) << 32)
		    | (((Tcl_WideUInt) buffer[5]) << 40)
		    | (((Tcl_WideUInt) buffer[6]) << 48)
		    | (((Tcl_WideUInt) buffer[7]) << 56);
	} else {
	    uwvalue = ((Tcl_WideUInt) buffer[7])
		    | (((Tcl_WideUInt) buffer[6]) << 8)
		    | (((Tcl_WideUInt) buffer[5]) << 16)
		    | (((Tcl_WideUInt) buffer[4]) << 24)
		    | (((Tcl_WideUInt) buffer[3]) << 32)
		    | (((Tcl_WideUInt) buffer[2]) << 40)
		    | (((Tcl_WideUInt) buffer[1]) << 48)
		    | (((Tcl_WideUInt) buffer[0]) << 56);
	}
	if (flags & BINARY_UNSIGNED) {
	    Tcl_Obj *bigObj = NULL;
	    mp_int big;

	    TclBNInitBignumFromWideUInt(&big, uwvalue);
	    bigObj = Tcl_NewBignumObj(&big);
	    return bigObj;
	}
	return Tcl_NewWideIntObj((Tcl_WideInt) uwvalue);

	/*
	 * Do not cache double values; they are already too large to use as
	 * keys and the values stored are utterly incompatible with the
	 * integer part of the cache.
	 */

	/*
	 * 32-bit IEEE single-precision floating point.
	 */

    case 'f':
    case 'R':
    case 'r':
	CopyNumber(buffer, &fvalue, sizeof(float), type);
	return Tcl_NewDoubleObj(fvalue);

	/*
	 * 64-bit IEEE double-precision floating point.
	 */

    case 'd':
    case 'Q':
    case 'q':
	CopyNumber(buffer, &dvalue, sizeof(double), type);
	return Tcl_NewDoubleObj(dvalue);
    }
    return NULL;
}

/*
 *----------------------------------------------------------------------
 *
 * DeleteScanNumberCache --
 *
 *	Deletes the hash table acting as a scan number cache.
 *
 * Results:
 *	None
 *
 * Side effects:
 *	Decrements the reference counts of the objects in the cache.
 *
 *----------------------------------------------------------------------
 */

static void
DeleteScanNumberCache(
    Tcl_HashTable *numberCachePtr)
				/* Pointer to the hash table, or NULL (when
				 * the cache has already been deleted due to
				 * overflow.) */
{
    Tcl_HashEntry *hEntry;
    Tcl_HashSearch search;

    if (numberCachePtr == NULL) {
	return;
    }

    hEntry = Tcl_FirstHashEntry(numberCachePtr, &search);
    while (hEntry != NULL) {
	register Tcl_Obj *value = Tcl_GetHashValue(hEntry);

	if (value != NULL) {
	    Tcl_DecrRefCount(value);
	}
	hEntry = Tcl_NextHashEntry(&search);
    }
    Tcl_DeleteHashTable(numberCachePtr);
}

/*
 * Local Variables:
 * mode: c
 * c-basic-offset: 4
 * fill-column: 78
 * End:
 */
