/*
 * tclObj.c --
 *
 *	This file contains Tcl object-related functions that are used by many
 *	Tcl commands.
 *
 * Copyright (c) 1995-1997 Sun Microsystems, Inc.
 * Copyright (c) 1999 by Scriptics Corporation.
 * Copyright (c) 2001 by ActiveState Corporation.
 * Copyright (c) 2005 by Kevin B. Kenny.  All rights reserved.
 * Copyright (c) 2007 Daniel A. Steffen <das@users.sourceforge.net>
 *
 * See the file "license.terms" for information on usage and redistribution of
 * this file, and for a DISCLAIMER OF ALL WARRANTIES.
 *
 * RCS: @(#) $Id: tclObj.c,v 1.139.2.1 2008/03/31 17:21:15 dgp Exp $
 */

#include "tclInt.h"
#include "tommath.h"
#include <float.h>
#include <math.h>

/*
 * Table of all object types.
 */

static Tcl_HashTable typeTable;
static int typeTableInitialized = 0;	/* 0 means not yet initialized. */
TCL_DECLARE_MUTEX(tableMutex)

/*
 * Head of the list of free Tcl_Obj structs we maintain.
 */

Tcl_Obj *tclFreeObjList = NULL;

/*
 * The object allocator is single threaded. This mutex is referenced by the
 * TclNewObj macro, however, so must be visible.
 */

#ifdef TCL_THREADS
MODULE_SCOPE Tcl_Mutex tclObjMutex;
Tcl_Mutex tclObjMutex;
#endif

/*
 * Pointer to a heap-allocated string of length zero that the Tcl core uses as
 * the value of an empty string representation for an object. This value is
 * shared by all new objects allocated by Tcl_NewObj.
 */

char tclEmptyString = '\0';
char *tclEmptyStringRep = &tclEmptyString;

#if defined(TCL_MEM_DEBUG) && defined(TCL_THREADS)
/*
 * Thread local table that is used to check that a Tcl_Obj was not allocated
 * by some other thread.
 */
typedef struct ThreadSpecificData {
    Tcl_HashTable *objThreadMap;
} ThreadSpecificData;

static Tcl_ThreadDataKey dataKey;
#endif /* TCL_MEM_DEBUG && TCL_THREADS */

/*
 * Nested Tcl_Obj deletion management support
 *
 * All context references used in the object freeing code are pointers to this
 * structure; every thread will have its own structure instance. The purpose
 * of this structure is to allow deeply nested collections of Tcl_Objs to be
 * freed without taking a vast depth of C stack (which could cause all sorts
 * of breakage.)
 */

typedef struct PendingObjData {
    int deletionCount;		/* Count of the number of invokations of
				 * TclFreeObj() are on the stack (at least
				 * conceptually; many are actually expanded
				 * macros). */
    Tcl_Obj *deletionStack;	/* Stack of objects that have had TclFreeObj()
				 * invoked upon them but which can't be
				 * deleted yet because they are in a nested
				 * invokation of TclFreeObj(). By postponing
				 * this way, we limit the maximum overall C
				 * stack depth when deleting a complex object.
				 * The down-side is that we alter the overall
				 * behaviour by altering the order in which
				 * objects are deleted, and we change the
				 * order in which the string rep and the
				 * internal rep of an object are deleted. Note
				 * that code which assumes the previous
				 * behaviour in either of these respects is
				 * unsafe anyway; it was never documented as
				 * to exactly what would happen in these
				 * cases, and the overall contract of a
				 * user-level Tcl_DecrRefCount() is still
				 * preserved (assuming that a particular T_DRC
				 * would delete an object is not very
				 * safe). */
} PendingObjData;

/*
 * These are separated out so that some semantic content is attached
 * to them.
 */
#define ObjDeletionLock(contextPtr)	((contextPtr)->deletionCount++)
#define ObjDeletionUnlock(contextPtr)	((contextPtr)->deletionCount--)
#define ObjDeletePending(contextPtr)	((contextPtr)->deletionCount > 0)
#define ObjOnStack(contextPtr)		((contextPtr)->deletionStack != NULL)
#define PushObjToDelete(contextPtr,objPtr) \
    /* The string rep is already invalidated so we can use the bytes value \
     * for our pointer chain: push onto the head of the stack. */ \
    (objPtr)->bytes = (char *) ((contextPtr)->deletionStack); \
    (contextPtr)->deletionStack = (objPtr)
#define PopObjToDelete(contextPtr,objPtrVar) \
    (objPtrVar) = (contextPtr)->deletionStack; \
    (contextPtr)->deletionStack = (Tcl_Obj *) (objPtrVar)->bytes

/*
 * Macro to set up the local reference to the deletion context.
 */
#ifndef TCL_THREADS
static PendingObjData pendingObjData;
#define ObjInitDeletionContext(contextPtr) \
    PendingObjData *CONST contextPtr = &pendingObjData
#else
static Tcl_ThreadDataKey pendingObjDataKey;
#define ObjInitDeletionContext(contextPtr) \
    PendingObjData *CONST contextPtr = (PendingObjData *) \
	    Tcl_GetThreadData(&pendingObjDataKey, sizeof(PendingObjData))
#endif

/*
 * Macros to pack/unpack a bignum's fields in a Tcl_Obj internal rep
 */

#define PACK_BIGNUM(bignum, objPtr) \
    if ((bignum).used > 0x7fff) { \
	mp_int *temp = (void *) ckalloc((unsigned) sizeof(mp_int)); \
	*temp = bignum; \
	(objPtr)->internalRep.ptrAndLongRep.ptr = (void*) temp; \
	(objPtr)->internalRep.ptrAndLongRep.value = (unsigned long)(-1); \
    } else { \
	if ((bignum).alloc > 0x7fff) { \
	    mp_shrink(&(bignum)); \
	} \
	(objPtr)->internalRep.ptrAndLongRep.ptr = (void*) (bignum).dp; \
	(objPtr)->internalRep.ptrAndLongRep.value = ( ((bignum).sign << 30) \
		| ((bignum).alloc << 15) | ((bignum).used)); \
    }

#define UNPACK_BIGNUM(objPtr, bignum) \
    if ((objPtr)->internalRep.ptrAndLongRep.value == (unsigned long)(-1)) { \
	(bignum) = *((mp_int *) ((objPtr)->internalRep.ptrAndLongRep.ptr)); \
    } else { \
	(bignum).dp = (mp_digit*) (objPtr)->internalRep.ptrAndLongRep.ptr; \
	(bignum).sign = (objPtr)->internalRep.ptrAndLongRep.value >> 30; \
	(bignum).alloc = \
		((objPtr)->internalRep.ptrAndLongRep.value >> 15) & 0x7fff; \
	(bignum).used = (objPtr)->internalRep.ptrAndLongRep.value & 0x7fff; \
    }

/*
 * Prototypes for functions defined later in this file:
 */

static int		ParseBoolean(Tcl_Obj *objPtr);
static int		SetBooleanFromAny(Tcl_Interp *interp, Tcl_Obj *objPtr);
static int		SetDoubleFromAny(Tcl_Interp *interp, Tcl_Obj *objPtr);
static int		SetIntFromAny(Tcl_Interp *interp, Tcl_Obj *objPtr);
static void		UpdateStringOfDouble(Tcl_Obj *objPtr);
static void		UpdateStringOfInt(Tcl_Obj *objPtr);
#ifndef NO_WIDE_TYPE
static void		UpdateStringOfWideInt(Tcl_Obj *objPtr);
static int		SetWideIntFromAny(Tcl_Interp *interp, Tcl_Obj *objPtr);
#endif
static void		FreeBignum(Tcl_Obj *objPtr);
static void		DupBignum(Tcl_Obj *objPtr, Tcl_Obj *copyPtr);
static void		UpdateStringOfBignum(Tcl_Obj *objPtr);
static int		GetBignumFromObj(Tcl_Interp *interp, Tcl_Obj *objPtr,
			    int copy, mp_int *bignumValue);

/*
 * Prototypes for the array hash key methods.
 */

static Tcl_HashEntry *	AllocObjEntry(Tcl_HashTable *tablePtr, void *keyPtr);

/*
 * Prototypes for the CommandName object type.
 */

static void		DupCmdNameInternalRep(Tcl_Obj *objPtr,
			    Tcl_Obj *copyPtr);
static void		FreeCmdNameInternalRep(Tcl_Obj *objPtr);
static int		SetCmdNameFromAny(Tcl_Interp *interp, Tcl_Obj *objPtr);

/*
 * The structures below defines the Tcl object types defined in this file by
 * means of functions that can be invoked by generic object code. See also
 * tclStringObj.c, tclListObj.c, tclByteCode.c for other type manager
 * implementations.
 */

static Tcl_ObjType oldBooleanType = {
    "boolean",				/* name */
    NULL,				/* freeIntRepProc */
    NULL,				/* dupIntRepProc */
    NULL,				/* updateStringProc */
    SetBooleanFromAny			/* setFromAnyProc */
};
Tcl_ObjType tclBooleanType = {
    "booleanString",			/* name */
    NULL,				/* freeIntRepProc */
    NULL,				/* dupIntRepProc */
    NULL,				/* updateStringProc */
    SetBooleanFromAny			/* setFromAnyProc */
};
Tcl_ObjType tclDoubleType = {
    "double",				/* name */
    NULL,				/* freeIntRepProc */
    NULL,				/* dupIntRepProc */
    UpdateStringOfDouble,		/* updateStringProc */
    SetDoubleFromAny			/* setFromAnyProc */
};
Tcl_ObjType tclIntType = {
    "int",				/* name */
    NULL,				/* freeIntRepProc */
    NULL,				/* dupIntRepProc */
    UpdateStringOfInt,			/* updateStringProc */
    SetIntFromAny			/* setFromAnyProc */
};
#ifndef NO_WIDE_TYPE
Tcl_ObjType tclWideIntType = {
    "wideInt",				/* name */
    NULL,				/* freeIntRepProc */
    NULL,				/* dupIntRepProc */
    UpdateStringOfWideInt,		/* updateStringProc */
    SetWideIntFromAny			/* setFromAnyProc */
};
#endif
Tcl_ObjType tclBignumType = {
    "bignum",				/* name */
    FreeBignum,				/* freeIntRepProc */
    DupBignum,				/* dupIntRepProc */
    UpdateStringOfBignum,		/* updateStringProc */
    NULL				/* setFromAnyProc */
};

/*
 * The structure below defines the Tcl obj hash key type.
 */

Tcl_HashKeyType tclObjHashKeyType = {
    TCL_HASH_KEY_TYPE_VERSION,	/* version */
    0,				/* flags */
    TclHashObjKey,		/* hashKeyProc */
    TclCompareObjKeys,		/* compareKeysProc */
    AllocObjEntry,		/* allocEntryProc */
    TclFreeObjEntry		/* freeEntryProc */
};

/*
 * The structure below defines the command name Tcl object type by means of
 * functions that can be invoked by generic object code. Objects of this type
 * cache the Command pointer that results from looking up command names in the
 * command hashtable. Such objects appear as the zeroth ("command name")
 * argument in a Tcl command.
 *
 * NOTE: the ResolvedCmdName that gets cached is stored in the
 * twoPtrValue.ptr1 field, and the twoPtrValue.ptr2 field is unused. You might
 * think you could use the simpler otherValuePtr field to store the single
 * ResolvedCmdName pointer, but DO NOT DO THIS. It seems that some extensions
 * use the second internal pointer field of the twoPtrValue field for their
 * own purposes.
 */

static Tcl_ObjType tclCmdNameType = {
    "cmdName",				/* name */
    FreeCmdNameInternalRep,		/* freeIntRepProc */
    DupCmdNameInternalRep,		/* dupIntRepProc */
    NULL,				/* updateStringProc */
    SetCmdNameFromAny			/* setFromAnyProc */
};

/*
 * Structure containing a cached pointer to a command that is the result of
 * resolving the command's name in some namespace. It is the internal
 * representation for a cmdName object. It contains the pointer along with
 * some information that is used to check the pointer's validity.
 */

typedef struct ResolvedCmdName {
    Command *cmdPtr;		/* A cached Command pointer. */
    Namespace *refNsPtr;	/* Points to the namespace containing the
				 * reference (not the namespace that contains
				 * the referenced command). NULL if the name
				 * is fully qualified.*/
    long refNsId;		/* refNsPtr's unique namespace id. Used to
				 * verify that refNsPtr is still valid (e.g.,
				 * it's possible that the cmd's containing
				 * namespace was deleted and a new one created
				 * at the same address). */
    int refNsCmdEpoch;		/* Value of the referencing namespace's
				 * cmdRefEpoch when the pointer was cached.
				 * Before using the cached pointer, we check
				 * if the namespace's epoch was incremented;
				 * if so, this cached pointer is invalid. */
    int cmdEpoch;		/* Value of the command's cmdEpoch when this
				 * pointer was cached. Before using the cached
				 * pointer, we check if the cmd's epoch was
				 * incremented; if so, the cmd was renamed,
				 * deleted, hidden, or exposed, and so the
				 * pointer is invalid. */
    int refCount;		/* Reference count: 1 for each cmdName object
				 * that has a pointer to this ResolvedCmdName
				 * structure as its internal rep. This
				 * structure can be freed when refCount
				 * becomes zero. */
} ResolvedCmdName;

/*
 *-------------------------------------------------------------------------
 *
 * TclInitObjectSubsystem --
 *
 *	This function is invoked to perform once-only initialization of the
 *	type table. It also registers the object types defined in this file.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	Initializes the table of defined object types "typeTable" with builtin
 *	object types defined in this file.
 *
 *-------------------------------------------------------------------------
 */

void
TclInitObjSubsystem(void)
{
    Tcl_MutexLock(&tableMutex);
    typeTableInitialized = 1;
    Tcl_InitHashTable(&typeTable, TCL_STRING_KEYS);
    Tcl_MutexUnlock(&tableMutex);

    Tcl_RegisterObjType(&tclByteArrayType);
    Tcl_RegisterObjType(&tclDoubleType);
    Tcl_RegisterObjType(&tclEndOffsetType);
    Tcl_RegisterObjType(&tclIntType);
    Tcl_RegisterObjType(&tclStringType);
    Tcl_RegisterObjType(&tclListType);
    Tcl_RegisterObjType(&tclDictType);
    Tcl_RegisterObjType(&tclByteCodeType);
    Tcl_RegisterObjType(&tclArraySearchType);
    Tcl_RegisterObjType(&tclCmdNameType);
    Tcl_RegisterObjType(&tclRegexpType);
    Tcl_RegisterObjType(&tclProcBodyType);

    /* For backward compatibility only ... */
    Tcl_RegisterObjType(&oldBooleanType);
#ifndef NO_WIDE_TYPE
    Tcl_RegisterObjType(&tclWideIntType);
#endif

#ifdef TCL_COMPILE_STATS
    Tcl_MutexLock(&tclObjMutex);
    tclObjsAlloced = 0;
    tclObjsFreed = 0;
    {
	int i;
	for (i=0 ; i<TCL_MAX_SHARED_OBJ_STATS ; i++) {
	    tclObjsShared[i] = 0;
	}
    }
    Tcl_MutexUnlock(&tclObjMutex);
#endif
}

/*
 *----------------------------------------------------------------------
 *
 * TclFinalizeObjects --
 *
 *	This function is called by Tcl_Finalize to clean up all registered
 *	Tcl_ObjType's and to reset the tclFreeObjList.
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
TclFinalizeObjects(void)
{
    Tcl_MutexLock(&tableMutex);
    if (typeTableInitialized) {
	Tcl_DeleteHashTable(&typeTable);
	typeTableInitialized = 0;
    }
    Tcl_MutexUnlock(&tableMutex);

    /*
     * All we do here is reset the head pointer of the linked list of free
     * Tcl_Obj's to NULL; the memory finalization will take care of releasing
     * memory for us.
     */
    Tcl_MutexLock(&tclObjMutex);
    tclFreeObjList = NULL;
    Tcl_MutexUnlock(&tclObjMutex);
}

/*
 *--------------------------------------------------------------
 *
 * Tcl_RegisterObjType --
 *
 *	This function is called to register a new Tcl object type in the table
 *	of all object types supported by Tcl.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	The type is registered in the Tcl type table. If there was already a
 *	type with the same name as in typePtr, it is replaced with the new
 *	type.
 *
 *--------------------------------------------------------------
 */

void
Tcl_RegisterObjType(
    Tcl_ObjType *typePtr)	/* Information about object type; storage must
				 * be statically allocated (must live
				 * forever). */
{
    int isNew;

    Tcl_MutexLock(&tableMutex);
    Tcl_SetHashValue(
	    Tcl_CreateHashEntry(&typeTable, typePtr->name, &isNew), typePtr);
    Tcl_MutexUnlock(&tableMutex);
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_AppendAllObjTypes --
 *
 *	This function appends onto the argument object the name of each object
 *	type as a list element. This includes the builtin object types (e.g.
 *	int, list) as well as those added using Tcl_NewObj. These names can be
 *	used, for example, with Tcl_GetObjType to get pointers to the
 *	corresponding Tcl_ObjType structures.
 *
 * Results:
 *	The return value is normally TCL_OK; in this case the object
 *	referenced by objPtr has each type name appended to it. If an error
 *	occurs, TCL_ERROR is returned and the interpreter's result holds an
 *	error message.
 *
 * Side effects:
 *	If necessary, the object referenced by objPtr is converted into a list
 *	object.
 *
 *----------------------------------------------------------------------
 */

int
Tcl_AppendAllObjTypes(
    Tcl_Interp *interp,		/* Interpreter used for error reporting. */
    Tcl_Obj *objPtr)		/* Points to the Tcl object onto which the
				 * name of each registered type is appended as
				 * a list element. */
{
    register Tcl_HashEntry *hPtr;
    Tcl_HashSearch search;
    int numElems;

    /*
     * Get the test for a valid list out of the way first.
     */

    if (TclListObjLength(interp, objPtr, &numElems) != TCL_OK) {
	return TCL_ERROR;
    }

    /*
     * Type names are NUL-terminated, not counted strings. This code relies on
     * that.
     */

    Tcl_MutexLock(&tableMutex);
    for (hPtr = Tcl_FirstHashEntry(&typeTable, &search);
	    hPtr != NULL; hPtr = Tcl_NextHashEntry(&search)) {
	Tcl_ListObjAppendElement(NULL, objPtr,
		Tcl_NewStringObj(Tcl_GetHashKey(&typeTable, hPtr), -1));
    }
    Tcl_MutexUnlock(&tableMutex);
    return TCL_OK;
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_GetObjType --
 *
 *	This function looks up an object type by name.
 *
 * Results:
 *	If an object type with name matching "typeName" is found, a pointer to
 *	its Tcl_ObjType structure is returned; otherwise, NULL is returned.
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */

Tcl_ObjType *
Tcl_GetObjType(
    CONST char *typeName)	/* Name of Tcl object type to look up. */
{
    register Tcl_HashEntry *hPtr;
    Tcl_ObjType *typePtr = NULL;

    Tcl_MutexLock(&tableMutex);
    hPtr = Tcl_FindHashEntry(&typeTable, typeName);
    if (hPtr != NULL) {
	typePtr = (Tcl_ObjType *) Tcl_GetHashValue(hPtr);
    }
    Tcl_MutexUnlock(&tableMutex);
    return typePtr;
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_ConvertToType --
 *
 *	Convert the Tcl object "objPtr" to have type "typePtr" if possible.
 *
 * Results:
 *	The return value is TCL_OK on success and TCL_ERROR on failure. If
 *	TCL_ERROR is returned, then the interpreter's result contains an error
 *	message unless "interp" is NULL. Passing a NULL "interp" allows this
 *	function to be used as a test whether the conversion could be done
 *	(and in fact was done).
 *
 * Side effects:
 *	Any internal representation for the old type is freed.
 *
 *----------------------------------------------------------------------
 */

int
Tcl_ConvertToType(
    Tcl_Interp *interp,		/* Used for error reporting if not NULL. */
    Tcl_Obj *objPtr,		/* The object to convert. */
    Tcl_ObjType *typePtr)	/* The target type. */
{
    if (objPtr->typePtr == typePtr) {
	return TCL_OK;
    }

    /*
     * Use the target type's Tcl_SetFromAnyProc to set "objPtr"s internal form
     * as appropriate for the target type. This frees the old internal
     * representation.
     */

    if (typePtr->setFromAnyProc == NULL) {
	Tcl_Panic("may not convert object to type %s", typePtr->name);
    }

    return typePtr->setFromAnyProc(interp, objPtr);
}

/*
 *----------------------------------------------------------------------
 *
 * TclDbInitNewObj --
 *
 *	Called via the TclNewObj or TclDbNewObj macros when TCL_MEM_DEBUG is
 *	enabled. This function will initialize the members of a Tcl_Obj
 *	struct. Initilization would be done inline via the TclNewObj macro
 *	when compiling without TCL_MEM_DEBUG.
 *
 * Results:
 *	The Tcl_Obj struct members are initialized.
 *
 * Side effects:
 *	None.
 *----------------------------------------------------------------------
 */

#ifdef TCL_MEM_DEBUG
void
TclDbInitNewObj(
    register Tcl_Obj *objPtr)
{
    objPtr->refCount = 0;
    objPtr->bytes = tclEmptyStringRep;
    objPtr->length = 0;
    objPtr->typePtr = NULL;

#ifdef TCL_THREADS
    /*
     * Add entry to a thread local map used to check if a Tcl_Obj was
     * allocated by the currently executing thread.
     */

    if (!TclInExit()) {
	Tcl_HashEntry *hPtr;
	Tcl_HashTable *tablePtr;
	int isNew;
	ThreadSpecificData *tsdPtr = TCL_TSD_INIT(&dataKey);

	if (tsdPtr->objThreadMap == NULL) {
	    tsdPtr->objThreadMap = (Tcl_HashTable *)
		    ckalloc(sizeof(Tcl_HashTable));
	    Tcl_InitHashTable(tsdPtr->objThreadMap, TCL_ONE_WORD_KEYS);
	}
	tablePtr = tsdPtr->objThreadMap;
	hPtr = Tcl_CreateHashEntry(tablePtr, (char *) objPtr, &isNew);
	if (!isNew) {
	    Tcl_Panic("expected to create new entry for object map");
	}
	Tcl_SetHashValue(hPtr, NULL);
    }
#endif /* TCL_THREADS */
}
#endif /* TCL_MEM_DEBUG */

/*
 *----------------------------------------------------------------------
 *
 * Tcl_NewObj --
 *
 *	This function is normally called when not debugging: i.e., when
 *	TCL_MEM_DEBUG is not defined. It creates new Tcl objects that denote
 *	the empty string. These objects have a NULL object type and NULL
 *	string representation byte pointer. Type managers call this routine to
 *	allocate new objects that they further initialize.
 *
 *	When TCL_MEM_DEBUG is defined, this function just returns the result
 *	of calling the debugging version Tcl_DbNewObj.
 *
 * Results:
 *	The result is a newly allocated object that represents the empty
 *	string. The new object's typePtr is set NULL and its ref count is set
 *	to 0.
 *
 * Side effects:
 *	If compiling with TCL_COMPILE_STATS, this function increments the
 *	global count of allocated objects (tclObjsAlloced).
 *
 *----------------------------------------------------------------------
 */

#ifdef TCL_MEM_DEBUG
#undef Tcl_NewObj

Tcl_Obj *
Tcl_NewObj(void)
{
    return Tcl_DbNewObj("unknown", 0);
}

#else /* if not TCL_MEM_DEBUG */

Tcl_Obj *
Tcl_NewObj(void)
{
    register Tcl_Obj *objPtr;

    /*
     * Use the macro defined in tclInt.h - it will use the correct allocator.
     */

    TclNewObj(objPtr);
    return objPtr;
}
#endif /* TCL_MEM_DEBUG */

/*
 *----------------------------------------------------------------------
 *
 * Tcl_DbNewObj --
 *
 *	This function is normally called when debugging: i.e., when
 *	TCL_MEM_DEBUG is defined. It creates new Tcl objects that denote the
 *	empty string. It is the same as the Tcl_NewObj function above except
 *	that it calls Tcl_DbCkalloc directly with the file name and line
 *	number from its caller. This simplifies debugging since then the
 *	[memory active] command will report the correct file name and line
 *	number when reporting objects that haven't been freed.
 *
 *	When TCL_MEM_DEBUG is not defined, this function just returns the
 *	result of calling Tcl_NewObj.
 *
 * Results:
 *	The result is a newly allocated that represents the empty string. The
 *	new object's typePtr is set NULL and its ref count is set to 0.
 *
 * Side effects:
 *	If compiling with TCL_COMPILE_STATS, this function increments the
 *	global count of allocated objects (tclObjsAlloced).
 *
 *----------------------------------------------------------------------
 */

#ifdef TCL_MEM_DEBUG

Tcl_Obj *
Tcl_DbNewObj(
    register CONST char *file,	/* The name of the source file calling this
				 * function; used for debugging. */
    register int line)		/* Line number in the source file; used for
				 * debugging. */
{
    register Tcl_Obj *objPtr;

    /*
     * Use the macro defined in tclInt.h - it will use the correct allocator.
     */

    TclDbNewObj(objPtr, file, line);
    return objPtr;
}
#else /* if not TCL_MEM_DEBUG */

Tcl_Obj *
Tcl_DbNewObj(
    CONST char *file,		/* The name of the source file calling this
				 * function; used for debugging. */
    int line)			/* Line number in the source file; used for
				 * debugging. */
{
    return Tcl_NewObj();
}
#endif /* TCL_MEM_DEBUG */

/*
 *----------------------------------------------------------------------
 *
 * TclAllocateFreeObjects --
 *
 *	Function to allocate a number of free Tcl_Objs. This is done using a
 *	single ckalloc to reduce the overhead for Tcl_Obj allocation.
 *
 *	Assumes mutex is held.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	tclFreeObjList, the head of the list of free Tcl_Objs, is set to the
 *	first of a number of free Tcl_Obj's linked together by their
 *	internalRep.otherValuePtrs.
 *
 *----------------------------------------------------------------------
 */

#define OBJS_TO_ALLOC_EACH_TIME 100

void
TclAllocateFreeObjects(void)
{
    size_t bytesToAlloc = (OBJS_TO_ALLOC_EACH_TIME * sizeof(Tcl_Obj));
    char *basePtr;
    register Tcl_Obj *prevPtr, *objPtr;
    register int i;

    /*
     * This has been noted by Purify to be a potential leak. The problem is
     * that Tcl, when not TCL_MEM_DEBUG compiled, keeps around all allocated
     * Tcl_Obj's, pointed to by tclFreeObjList, when freed instead of actually
     * freeing the memory. TclFinalizeObjects() does not ckfree() this memory,
     * but leaves it to Tcl's memory subsystem finalization to release it.
     * Purify apparently can't figure that out, and fires a false alarm.
     */

    basePtr = (char *) ckalloc(bytesToAlloc);

    prevPtr = NULL;
    objPtr = (Tcl_Obj *) basePtr;
    for (i = 0; i < OBJS_TO_ALLOC_EACH_TIME; i++) {
	objPtr->internalRep.otherValuePtr = (void *) prevPtr;
	prevPtr = objPtr;
	objPtr++;
    }
    tclFreeObjList = prevPtr;
}
#undef OBJS_TO_ALLOC_EACH_TIME

/*
 *----------------------------------------------------------------------
 *
 * TclFreeObj --
 *
 *	This function frees the memory associated with the argument object.
 *	It is called by the tcl.h macro Tcl_DecrRefCount when an object's ref
 *	count is zero. It is only "public" since it must be callable by that
 *	macro wherever the macro is used. It should not be directly called by
 *	clients.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	Deallocates the storage for the object's Tcl_Obj structure after
 *	deallocating the string representation and calling the type-specific
 *	Tcl_FreeInternalRepProc to deallocate the object's internal
 *	representation. If compiling with TCL_COMPILE_STATS, this function
 *	increments the global count of freed objects (tclObjsFreed).
 *
 *----------------------------------------------------------------------
 */

#ifdef TCL_MEM_DEBUG
void
TclFreeObj(
    register Tcl_Obj *objPtr)	/* The object to be freed. */
{
    register Tcl_ObjType *typePtr = objPtr->typePtr;

    /*
     * This macro declares a variable, so must come here...
     */

    ObjInitDeletionContext(context);

    if (objPtr->refCount < -1) {
	Tcl_Panic("Reference count for %lx was negative", objPtr);
    }

    /* Invalidate the string rep first so we can use the bytes value 
     * for our pointer chain, and signal an obj deletion (as opposed
     * to shimmering) with 'length == -1' */ 
    
    TclInvalidateStringRep(objPtr);
    objPtr->length = -1;

    if (ObjDeletePending(context)) {
	PushObjToDelete(context, objPtr);
    } else {
	TCL_DTRACE_OBJ_FREE(objPtr);
	if ((typePtr != NULL) && (typePtr->freeIntRepProc != NULL)) {
	    ObjDeletionLock(context);
	    typePtr->freeIntRepProc(objPtr);
	    ObjDeletionUnlock(context);
	}

	Tcl_MutexLock(&tclObjMutex);
	ckfree((char *) objPtr);
	Tcl_MutexUnlock(&tclObjMutex);
	TclIncrObjsFreed();
	ObjDeletionLock(context);
	while (ObjOnStack(context)) {
	    Tcl_Obj *objToFree;

	    PopObjToDelete(context,objToFree);
	    TCL_DTRACE_OBJ_FREE(objToFree);
	    TclFreeIntRep(objToFree);

	    Tcl_MutexLock(&tclObjMutex);
	    ckfree((char *) objToFree);
	    Tcl_MutexUnlock(&tclObjMutex);
	    TclIncrObjsFreed();
	}
	ObjDeletionUnlock(context);
    }
}
#else /* TCL_MEM_DEBUG */

void
TclFreeObj(
    register Tcl_Obj *objPtr)	/* The object to be freed. */
{
    /* Invalidate the string rep first so we can use the bytes value 
     * for our pointer chain, and signal an obj deletion (as opposed
     * to shimmering) with 'length == -1' */ 

    TclInvalidateStringRep(objPtr);
    objPtr->length = -1;
    
    if (!objPtr->typePtr || !objPtr->typePtr->freeIntRepProc) {
	/*
	 * objPtr can be freed safely, as it will not attempt to free any
	 * other objects: it will not cause recursive calls to this function.
	 */

	TCL_DTRACE_OBJ_FREE(objPtr);
	TclFreeObjStorage(objPtr);
	TclIncrObjsFreed();
    } else {
	/*
	 * This macro declares a variable, so must come here...
	 */

	ObjInitDeletionContext(context);

	if (ObjDeletePending(context)) {
	    PushObjToDelete(context, objPtr);
	} else {
	    /*
	     * Note that the contents of the while loop assume that the string
	     * rep has already been freed and we don't want to do anything
	     * fancy with adding to the queue inside ourselves. Must take care
	     * to unstack the object first since freeing the internal rep can
	     * add further objects to the stack. The code assumes that it is
	     * the first thing in a block; all current usages in the core
	     * satisfy this.
	     */

	    TCL_DTRACE_OBJ_FREE(objPtr);
	    ObjDeletionLock(context);
	    objPtr->typePtr->freeIntRepProc(objPtr);
	    ObjDeletionUnlock(context);

	    TclFreeObjStorage(objPtr);
	    TclIncrObjsFreed();
	    ObjDeletionLock(context);
	    while (ObjOnStack(context)) {
		Tcl_Obj *objToFree;
		PopObjToDelete(context,objToFree);
		TCL_DTRACE_OBJ_FREE(objToFree);
		if ((objToFree->typePtr != NULL)
			&& (objToFree->typePtr->freeIntRepProc != NULL)) {
		    objToFree->typePtr->freeIntRepProc(objToFree);
		}
		TclFreeObjStorage(objToFree);
		TclIncrObjsFreed();
	    }
	    ObjDeletionUnlock(context);
	}
    }
}
#endif

/*
 *----------------------------------------------------------------------
 *
 * TclObjBeingDeleted --
 *
 *	This function returns 1 when the Tcl_Obj is being deleted. It is
 *	provided for the rare cases where the reason for the loss of an
 *	internal rep might be relevant. [FR 1512138]
 *
 * Results:
 *	1 if being deleted, 0 otherwise.
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */

int
TclObjBeingDeleted(
    Tcl_Obj *objPtr)
{
    return (objPtr->length == -1);
}


/*
 *----------------------------------------------------------------------
 *
 * Tcl_DuplicateObj --
 *
 *	Create and return a new object that is a duplicate of the argument
 *	object.
 *
 * Results:
 *	The return value is a pointer to a newly created Tcl_Obj. This object
 *	has reference count 0 and the same type, if any, as the source object
 *	objPtr. Also:
 *	  1) If the source object has a valid string rep, we copy it;
 *	     otherwise, the duplicate's string rep is set NULL to mark it
 *	     invalid.
 *	  2) If the source object has an internal representation (i.e. its
 *	     typePtr is non-NULL), the new object's internal rep is set to a
 *	     copy; otherwise the new internal rep is marked invalid.
 *
 * Side effects:
 *	What constitutes "copying" the internal representation depends on the
 *	type. For example, if the argument object is a list, the element
 *	objects it points to will not actually be copied but will be shared
 *	with the duplicate list. That is, the ref counts of the element
 *	objects will be incremented.
 *
 *----------------------------------------------------------------------
 */

Tcl_Obj *
Tcl_DuplicateObj(
    register Tcl_Obj *objPtr)		/* The object to duplicate. */
{
    register Tcl_ObjType *typePtr = objPtr->typePtr;
    register Tcl_Obj *dupPtr;

    TclNewObj(dupPtr);

    if (objPtr->bytes == NULL) {
	dupPtr->bytes = NULL;
    } else if (objPtr->bytes != tclEmptyStringRep) {
	TclInitStringRep(dupPtr, objPtr->bytes, objPtr->length);
    }

    if (typePtr != NULL) {
	if (typePtr->dupIntRepProc == NULL) {
	    dupPtr->internalRep = objPtr->internalRep;
	    dupPtr->typePtr = typePtr;
	} else {
	    (*typePtr->dupIntRepProc)(objPtr, dupPtr);
	}
    }
    return dupPtr;
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_GetString --
 *
 *	Returns the string representation byte array pointer for an object.
 *
 * Results:
 *	Returns a pointer to the string representation of objPtr. The byte
 *	array referenced by the returned pointer must not be modified by the
 *	caller. Furthermore, the caller must copy the bytes if they need to
 *	retain them since the object's string rep can change as a result of
 *	other operations.
 *
 * Side effects:
 *	May call the object's updateStringProc to update the string
 *	representation from the internal representation.
 *
 *----------------------------------------------------------------------
 */

char *
Tcl_GetString(
    register Tcl_Obj *objPtr)	/* Object whose string rep byte pointer should
				 * be returned. */
{
    if (objPtr->bytes != NULL) {
	return objPtr->bytes;
    }

    if (objPtr->typePtr->updateStringProc == NULL) {
	Tcl_Panic("UpdateStringProc should not be invoked for type %s",
		objPtr->typePtr->name);
    }
    (*objPtr->typePtr->updateStringProc)(objPtr);
    return objPtr->bytes;
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_GetStringFromObj --
 *
 *	Returns the string representation's byte array pointer and length for
 *	an object.
 *
 * Results:
 *	Returns a pointer to the string representation of objPtr. If lengthPtr
 *	isn't NULL, the length of the string representation is stored at
 *	*lengthPtr. The byte array referenced by the returned pointer must not
 *	be modified by the caller. Furthermore, the caller must copy the bytes
 *	if they need to retain them since the object's string rep can change
 *	as a result of other operations.
 *
 * Side effects:
 *	May call the object's updateStringProc to update the string
 *	representation from the internal representation.
 *
 *----------------------------------------------------------------------
 */

char *
Tcl_GetStringFromObj(
    register Tcl_Obj *objPtr,	/* Object whose string rep byte pointer should
				 * be returned. */
    register int *lengthPtr)	/* If non-NULL, the location where the string
				 * rep's byte array length should * be stored.
				 * If NULL, no length is stored. */
{
    if (objPtr->bytes == NULL) {
	if (objPtr->typePtr->updateStringProc == NULL) {
	    Tcl_Panic("UpdateStringProc should not be invoked for type %s",
		    objPtr->typePtr->name);
	}
	(*objPtr->typePtr->updateStringProc)(objPtr);
    }

    if (lengthPtr != NULL) {
	*lengthPtr = objPtr->length;
    }
    return objPtr->bytes;
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_InvalidateStringRep --
 *
 *	This function is called to invalidate an object's string
 *	representation.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	Deallocates the storage for any old string representation, then sets
 *	the string representation NULL to mark it invalid.
 *
 *----------------------------------------------------------------------
 */

void
Tcl_InvalidateStringRep(
    register Tcl_Obj *objPtr)	/* Object whose string rep byte pointer should
				 * be freed. */
{
    TclInvalidateStringRep(objPtr);
}


/*
 *----------------------------------------------------------------------
 *
 * Tcl_NewBooleanObj --
 *
 *	This function is normally called when not debugging: i.e., when
 *	TCL_MEM_DEBUG is not defined. It creates a new Tcl_Obj and
 *	initializes it from the argument boolean value. A nonzero "boolValue"
 *	is coerced to 1.
 *
 *	When TCL_MEM_DEBUG is defined, this function just returns the result
 *	of calling the debugging version Tcl_DbNewBooleanObj.
 *
 * Results:
 *	The newly created object is returned. This object will have an invalid
 *	string representation. The returned object has ref count 0.
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */

#ifdef TCL_MEM_DEBUG
#undef Tcl_NewBooleanObj

Tcl_Obj *
Tcl_NewBooleanObj(
    register int boolValue)	/* Boolean used to initialize new object. */
{
    return Tcl_DbNewBooleanObj(boolValue, "unknown", 0);
}

#else /* if not TCL_MEM_DEBUG */

Tcl_Obj *
Tcl_NewBooleanObj(
    register int boolValue)	/* Boolean used to initialize new object. */
{
    register Tcl_Obj *objPtr;

    TclNewBooleanObj(objPtr, boolValue);
    return objPtr;
}
#endif /* TCL_MEM_DEBUG */

/*
 *----------------------------------------------------------------------
 *
 * Tcl_DbNewBooleanObj --
 *
 *	This function is normally called when debugging: i.e., when
 *	TCL_MEM_DEBUG is defined. It creates new boolean objects. It is the
 *	same as the Tcl_NewBooleanObj function above except that it calls
 *	Tcl_DbCkalloc directly with the file name and line number from its
 *	caller. This simplifies debugging since then the [memory active]
 *	command will report the correct file name and line number when
 *	reporting objects that haven't been freed.
 *
 *	When TCL_MEM_DEBUG is not defined, this function just returns the
 *	result of calling Tcl_NewBooleanObj.
 *
 * Results:
 *	The newly created object is returned. This object will have an invalid
 *	string representation. The returned object has ref count 0.
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */

#ifdef TCL_MEM_DEBUG

Tcl_Obj *
Tcl_DbNewBooleanObj(
    register int boolValue,	/* Boolean used to initialize new object. */
    CONST char *file,		/* The name of the source file calling this
				 * function; used for debugging. */
    int line)			/* Line number in the source file; used for
				 * debugging. */
{
    register Tcl_Obj *objPtr;

    TclDbNewObj(objPtr, file, line);
    objPtr->bytes = NULL;

    objPtr->internalRep.longValue = (boolValue? 1 : 0);
    objPtr->typePtr = &tclIntType;
    return objPtr;
}

#else /* if not TCL_MEM_DEBUG */

Tcl_Obj *
Tcl_DbNewBooleanObj(
    register int boolValue,	/* Boolean used to initialize new object. */
    CONST char *file,		/* The name of the source file calling this
				 * function; used for debugging. */
    int line)			/* Line number in the source file; used for
				 * debugging. */
{
    return Tcl_NewBooleanObj(boolValue);
}
#endif /* TCL_MEM_DEBUG */

/*
 *----------------------------------------------------------------------
 *
 * Tcl_SetBooleanObj --
 *
 *	Modify an object to be a boolean object and to have the specified
 *	boolean value. A nonzero "boolValue" is coerced to 1.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	The object's old string rep, if any, is freed. Also, any old internal
 *	rep is freed.
 *
 *----------------------------------------------------------------------
 */

void
Tcl_SetBooleanObj(
    register Tcl_Obj *objPtr,	/* Object whose internal rep to init. */
    register int boolValue)	/* Boolean used to set object's value. */
{
    if (Tcl_IsShared(objPtr)) {
	Tcl_Panic("%s called with shared object", "Tcl_SetBooleanObj");
    }

    TclSetBooleanObj(objPtr, boolValue);
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_GetBooleanFromObj --
 *
 *	Attempt to return a boolean from the Tcl object "objPtr". This
 *	includes conversion from any of Tcl's numeric types.
 *
 * Results:
 *	The return value is a standard Tcl object result. If an error occurs
 *	during conversion, an error message is left in the interpreter's
 *	result unless "interp" is NULL.
 *
 * Side effects:
 *	The intrep of *objPtr may be changed.
 *
 *----------------------------------------------------------------------
 */

int
Tcl_GetBooleanFromObj(
    Tcl_Interp *interp, 	/* Used for error reporting if not NULL. */
    register Tcl_Obj *objPtr,	/* The object from which to get boolean. */
    register int *boolPtr)	/* Place to store resulting boolean. */
{
    do {
	if (objPtr->typePtr == &tclIntType) {
	    *boolPtr = (objPtr->internalRep.longValue != 0);
	    return TCL_OK;
	}
	if (objPtr->typePtr == &tclBooleanType) {
	    *boolPtr = (int) objPtr->internalRep.longValue;
	    return TCL_OK;
	}
	if (objPtr->typePtr == &tclDoubleType) {
	    /*
	     * Caution: Don't be tempted to check directly for the "double"
	     * Tcl_ObjType and then compare the intrep to 0.0. This isn't
	     * reliable because a "double" Tcl_ObjType can hold the NaN value.
	     * Use the API Tcl_GetDoubleFromObj, which does the checking and
	     * sets the proper error message for us.
	     */

            double d;

	    if (Tcl_GetDoubleFromObj(interp, objPtr, &d) != TCL_OK) {
		return TCL_ERROR;
	    }
	    *boolPtr = (d != 0.0);
	    return TCL_OK;
	}
	if (objPtr->typePtr == &tclBignumType) {
	    *boolPtr = 1;
	    return TCL_OK;
	}
#ifndef NO_WIDE_TYPE
	if (objPtr->typePtr == &tclWideIntType) {
	    *boolPtr = (objPtr->internalRep.wideValue != 0);
	    return TCL_OK;
	}
#endif
    } while ((ParseBoolean(objPtr) == TCL_OK) || (TCL_OK ==
	    TclParseNumber(interp, objPtr, "boolean value", NULL,-1,NULL,0)));
    return TCL_ERROR;
}

/*
 *----------------------------------------------------------------------
 *
 * SetBooleanFromAny --
 *
 *	Attempt to generate a boolean internal form for the Tcl object
 *	"objPtr".
 *
 * Results:
 *	The return value is a standard Tcl result. If an error occurs during
 *	conversion, an error message is left in the interpreter's result
 *	unless "interp" is NULL.
 *
 * Side effects:
 *	If no error occurs, an integer 1 or 0 is stored as "objPtr"s internal
 *	representation and the type of "objPtr" is set to boolean.
 *
 *----------------------------------------------------------------------
 */

static int
SetBooleanFromAny(
    Tcl_Interp *interp,		/* Used for error reporting if not NULL. */
    register Tcl_Obj *objPtr)	/* The object to convert. */
{
    /*
     * For some "pure" numeric Tcl_ObjTypes (no string rep), we can determine
     * whether a boolean conversion is possible without generating the string
     * rep.
     */

    if (objPtr->bytes == NULL) {
	if (objPtr->typePtr == &tclIntType) {
	    switch (objPtr->internalRep.longValue) {
	    case 0L: case 1L:
		return TCL_OK;
	    }
	    goto badBoolean;
	}

	if (objPtr->typePtr == &tclBignumType) {
	    goto badBoolean;
	}

#ifndef NO_WIDE_TYPE
	if (objPtr->typePtr == &tclWideIntType) {
	    goto badBoolean;
	}
#endif

	if (objPtr->typePtr == &tclDoubleType) {
	    goto badBoolean;
	}
    }

    if (ParseBoolean(objPtr) == TCL_OK) {
	return TCL_OK;
    }

  badBoolean:
    if (interp != NULL) {
	int length;
	char *str = Tcl_GetStringFromObj(objPtr, &length);
	Tcl_Obj *msg;

	TclNewLiteralStringObj(msg, "expected boolean value but got \"");
	Tcl_AppendLimitedToObj(msg, str, length, 50, "");
	Tcl_AppendToObj(msg, "\"", -1);
	Tcl_SetObjResult(interp, msg);
    }
    return TCL_ERROR;
}

static int
ParseBoolean(
    register Tcl_Obj *objPtr)	/* The object to parse/convert. */
{
    int i, length, newBool;
    char lowerCase[6], *str = TclGetStringFromObj(objPtr, &length);

    if ((length == 0) || (length > 5)) {
	/* longest valid boolean string rep. is "false" */
	return TCL_ERROR;
    }

    switch (str[0]) {
    case '0':
	if (length == 1) {
	    newBool = 0;
	    goto numericBoolean;
	}
	return TCL_ERROR;
    case '1':
	if (length == 1) {
	    newBool = 1;
	    goto numericBoolean;
	}
	return TCL_ERROR;
    }

    /*
     * Force to lower case for case-insensitive detection. Filter out known
     * invalid characters at the same time.
     */

    for (i=0; i < length; i++) {
	char c = str[i];
	switch (c) {
	case 'A': case 'E': case 'F': case 'L': case 'N':
	case 'O': case 'R': case 'S': case 'T': case 'U': case 'Y':
	    lowerCase[i] = c + (char) ('a' - 'A');
	    break;
	case 'a': case 'e': case 'f': case 'l': case 'n':
	case 'o': case 'r': case 's': case 't': case 'u': case 'y':
	    lowerCase[i] = c;
	    break;
	default:
	    return TCL_ERROR;
	}
    }
    lowerCase[length] = 0;
    switch (lowerCase[0]) {
    case 'y':
	/*
	 * Checking the 'y' is redundant, but makes the code clearer.
	 */
	if (strncmp(lowerCase, "yes", (size_t) length) == 0) {
	    newBool = 1;
	    goto goodBoolean;
	}
	return TCL_ERROR;
    case 'n':
	if (strncmp(lowerCase, "no", (size_t) length) == 0) {
	    newBool = 0;
	    goto goodBoolean;
	}
	return TCL_ERROR;
    case 't':
	if (strncmp(lowerCase, "true", (size_t) length) == 0) {
	    newBool = 1;
	    goto goodBoolean;
	}
	return TCL_ERROR;
    case 'f':
	if (strncmp(lowerCase, "false", (size_t) length) == 0) {
	    newBool = 0;
	    goto goodBoolean;
	}
	return TCL_ERROR;
    case 'o':
	if (length < 2) {
	    return TCL_ERROR;
	}
	if (strncmp(lowerCase, "on", (size_t) length) == 0) {
	    newBool = 1;
	    goto goodBoolean;
	} else if (strncmp(lowerCase, "off", (size_t) length) == 0) {
	    newBool = 0;
	    goto goodBoolean;
	}
	return TCL_ERROR;
    default:
	return TCL_ERROR;
    }

    /*
     * Free the old internalRep before setting the new one. We do this as late
     * as possible to allow the conversion code, in particular
     * Tcl_GetStringFromObj, to use that old internalRep.
     */

  goodBoolean:
    TclFreeIntRep(objPtr);
    objPtr->internalRep.longValue = newBool;
    objPtr->typePtr = &tclBooleanType;
    return TCL_OK;

  numericBoolean:
    TclFreeIntRep(objPtr);
    objPtr->internalRep.longValue = newBool;
    objPtr->typePtr = &tclIntType;
    return TCL_OK;
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_NewDoubleObj --
 *
 *	This function is normally called when not debugging: i.e., when
 *	TCL_MEM_DEBUG is not defined. It creates a new double object and
 *	initializes it from the argument double value.
 *
 *	When TCL_MEM_DEBUG is defined, this function just returns the result
 *	of calling the debugging version Tcl_DbNewDoubleObj.
 *
 * Results:
 *	The newly created object is returned. This object will have an
 *	invalid string representation. The returned object has ref count 0.
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */

#ifdef TCL_MEM_DEBUG
#undef Tcl_NewDoubleObj

Tcl_Obj *
Tcl_NewDoubleObj(
    register double dblValue)	/* Double used to initialize the object. */
{
    return Tcl_DbNewDoubleObj(dblValue, "unknown", 0);
}

#else /* if not TCL_MEM_DEBUG */

Tcl_Obj *
Tcl_NewDoubleObj(
    register double dblValue)	/* Double used to initialize the object. */
{
    register Tcl_Obj *objPtr;

    TclNewDoubleObj(objPtr, dblValue);
    return objPtr;
}
#endif /* if TCL_MEM_DEBUG */

/*
 *----------------------------------------------------------------------
 *
 * Tcl_DbNewDoubleObj --
 *
 *	This function is normally called when debugging: i.e., when
 *	TCL_MEM_DEBUG is defined. It creates new double objects. It is the
 *	same as the Tcl_NewDoubleObj function above except that it calls
 *	Tcl_DbCkalloc directly with the file name and line number from its
 *	caller. This simplifies debugging since then the [memory active]
 *	command will report the correct file name and line number when
 *	reporting objects that haven't been freed.
 *
 *	When TCL_MEM_DEBUG is not defined, this function just returns the
 *	result of calling Tcl_NewDoubleObj.
 *
 * Results:
 *	The newly created object is returned. This object will have an invalid
 *	string representation. The returned object has ref count 0.
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */

#ifdef TCL_MEM_DEBUG

Tcl_Obj *
Tcl_DbNewDoubleObj(
    register double dblValue,	/* Double used to initialize the object. */
    CONST char *file,		/* The name of the source file calling this
				 * function; used for debugging. */
    int line)			/* Line number in the source file; used for
				 * debugging. */
{
    register Tcl_Obj *objPtr;

    TclDbNewObj(objPtr, file, line);
    objPtr->bytes = NULL;

    objPtr->internalRep.doubleValue = dblValue;
    objPtr->typePtr = &tclDoubleType;
    return objPtr;
}

#else /* if not TCL_MEM_DEBUG */

Tcl_Obj *
Tcl_DbNewDoubleObj(
    register double dblValue,	/* Double used to initialize the object. */
    CONST char *file,		/* The name of the source file calling this
				 * function; used for debugging. */
    int line)			/* Line number in the source file; used for
				 * debugging. */
{
    return Tcl_NewDoubleObj(dblValue);
}
#endif /* TCL_MEM_DEBUG */

/*
 *----------------------------------------------------------------------
 *
 * Tcl_SetDoubleObj --
 *
 *	Modify an object to be a double object and to have the specified
 *	double value.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	The object's old string rep, if any, is freed. Also, any old internal
 *	rep is freed.
 *
 *----------------------------------------------------------------------
 */

void
Tcl_SetDoubleObj(
    register Tcl_Obj *objPtr,	/* Object whose internal rep to init. */
    register double dblValue)	/* Double used to set the object's value. */
{
    if (Tcl_IsShared(objPtr)) {
	Tcl_Panic("%s called with shared object", "Tcl_SetDoubleObj");
    }

    TclSetDoubleObj(objPtr, dblValue);
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_GetDoubleFromObj --
 *
 *	Attempt to return a double from the Tcl object "objPtr". If the object
 *	is not already a double, an attempt will be made to convert it to one.
 *
 * Results:
 *	The return value is a standard Tcl object result. If an error occurs
 *	during conversion, an error message is left in the interpreter's
 *	result unless "interp" is NULL.
 *
 * Side effects:
 *	If the object is not already a double, the conversion will free any
 *	old internal representation.
 *
 *----------------------------------------------------------------------
 */

int
Tcl_GetDoubleFromObj(
    Tcl_Interp *interp, 	/* Used for error reporting if not NULL. */
    register Tcl_Obj *objPtr,	/* The object from which to get a double. */
    register double *dblPtr)	/* Place to store resulting double. */
{
    do {
	if (objPtr->typePtr == &tclDoubleType) {
	    if (TclIsNaN(objPtr->internalRep.doubleValue)) {
		if (interp != NULL) {
		    Tcl_SetObjResult(interp, Tcl_NewStringObj(
			    "floating point value is Not a Number", -1));
		}
		return TCL_ERROR;
	    }
	    *dblPtr = (double) objPtr->internalRep.doubleValue;
	    return TCL_OK;
	}
	if (objPtr->typePtr == &tclIntType) {
	    *dblPtr = objPtr->internalRep.longValue;
	    return TCL_OK;
	}
	if (objPtr->typePtr == &tclBignumType) {
	    mp_int big;
	    UNPACK_BIGNUM( objPtr, big );
	    *dblPtr = TclBignumToDouble( &big );
	    return TCL_OK;
	}
#ifndef NO_WIDE_TYPE
	if (objPtr->typePtr == &tclWideIntType) {
	    *dblPtr = (double) objPtr->internalRep.wideValue;
	    return TCL_OK;
	}
#endif
    } while (SetDoubleFromAny(interp, objPtr) == TCL_OK);
    return TCL_ERROR;
}

/*
 *----------------------------------------------------------------------
 *
 * SetDoubleFromAny --
 *
 *	Attempt to generate an double-precision floating point internal form
 *	for the Tcl object "objPtr".
 *
 * Results:
 *	The return value is a standard Tcl object result. If an error occurs
 *	during conversion, an error message is left in the interpreter's
 *	result unless "interp" is NULL.
 *
 * Side effects:
 *	If no error occurs, a double is stored as "objPtr"s internal
 *	representation.
 *
 *----------------------------------------------------------------------
 */

static int
SetDoubleFromAny(
    Tcl_Interp *interp,		/* Used for error reporting if not NULL. */
    register Tcl_Obj *objPtr)	/* The object to convert. */
{
    return TclParseNumber(interp, objPtr, "floating-point number", NULL, -1,
	    NULL, 0);
}

/*
 *----------------------------------------------------------------------
 *
 * UpdateStringOfDouble --
 *
 *	Update the string representation for a double-precision floating point
 *	object. This must obey the current tcl_precision value for
 *	double-to-string conversions. Note: This function does not free an
 *	existing old string rep so storage will be lost if this has not
 *	already been done.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	The object's string is set to a valid string that results from the
 *	double-to-string conversion.
 *
 *----------------------------------------------------------------------
 */

static void
UpdateStringOfDouble(
    register Tcl_Obj *objPtr)	/* Double obj with string rep to update. */
{
    char buffer[TCL_DOUBLE_SPACE];
    register int len;

    Tcl_PrintDouble(NULL, objPtr->internalRep.doubleValue, buffer);
    len = strlen(buffer);

    objPtr->bytes = (char *) ckalloc((unsigned) len + 1);
    strcpy(objPtr->bytes, buffer);
    objPtr->length = len;
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_NewIntObj --
 *
 *	If a client is compiled with TCL_MEM_DEBUG defined, calls to
 *	Tcl_NewIntObj to create a new integer object end up calling the
 *	debugging function Tcl_DbNewLongObj instead.
 *
 *	Otherwise, if the client is compiled without TCL_MEM_DEBUG defined,
 *	calls to Tcl_NewIntObj result in a call to one of the two
 *	Tcl_NewIntObj implementations below. We provide two implementations so
 *	that the Tcl core can be compiled to do memory debugging of the core
 *	even if a client does not request it for itself.
 *
 *	Integer and long integer objects share the same "integer" type
 *	implementation. We store all integers as longs and Tcl_GetIntFromObj
 *	checks whether the current value of the long can be represented by an
 *	int.
 *
 * Results:
 *	The newly created object is returned. This object will have an invalid
 *	string representation. The returned object has ref count 0.
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */

#ifdef TCL_MEM_DEBUG
#undef Tcl_NewIntObj

Tcl_Obj *
Tcl_NewIntObj(
    register int intValue)	/* Int used to initialize the new object. */
{
    return Tcl_DbNewLongObj((long)intValue, "unknown", 0);
}

#else /* if not TCL_MEM_DEBUG */

Tcl_Obj *
Tcl_NewIntObj(
    register int intValue)	/* Int used to initialize the new object. */
{
    register Tcl_Obj *objPtr;

    TclNewIntObj(objPtr, intValue);
    return objPtr;
}
#endif /* if TCL_MEM_DEBUG */

/*
 *----------------------------------------------------------------------
 *
 * Tcl_SetIntObj --
 *
 *	Modify an object to be an integer and to have the specified integer
 *	value.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	The object's old string rep, if any, is freed. Also, any old internal
 *	rep is freed.
 *
 *----------------------------------------------------------------------
 */

void
Tcl_SetIntObj(
    register Tcl_Obj *objPtr,	/* Object whose internal rep to init. */
    register int intValue)	/* Integer used to set object's value. */
{
    if (Tcl_IsShared(objPtr)) {
	Tcl_Panic("%s called with shared object", "Tcl_SetIntObj");
    }

    TclSetIntObj(objPtr, intValue);
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_GetIntFromObj --
 *
 *	Attempt to return an int from the Tcl object "objPtr". If the object
 *	is not already an int, an attempt will be made to convert it to one.
 *
 *	Integer and long integer objects share the same "integer" type
 *	implementation. We store all integers as longs and Tcl_GetIntFromObj
 *	checks whether the current value of the long can be represented by an
 *	int.
 *
 * Results:
 *	The return value is a standard Tcl object result. If an error occurs
 *	during conversion or if the long integer held by the object can not be
 *	represented by an int, an error message is left in the interpreter's
 *	result unless "interp" is NULL.
 *
 * Side effects:
 *	If the object is not already an int, the conversion will free any old
 *	internal representation.
 *
 *----------------------------------------------------------------------
 */

int
Tcl_GetIntFromObj(
    Tcl_Interp *interp, 	/* Used for error reporting if not NULL. */
    register Tcl_Obj *objPtr,	/* The object from which to get a int. */
    register int *intPtr)	/* Place to store resulting int. */
{
#if (LONG_MAX == INT_MAX)
    return TclGetLongFromObj(interp, objPtr, (long *) intPtr);
#else
    long l;

    if (TclGetLongFromObj(interp, objPtr, &l) != TCL_OK) {
	return TCL_ERROR;
    }
    if ((ULONG_MAX > UINT_MAX) && ((l > UINT_MAX) || (l < -(long)UINT_MAX))) {
	if (interp != NULL) {
	    CONST char *s =
		    "integer value too large to represent as non-long integer";
	    Tcl_SetObjResult(interp, Tcl_NewStringObj(s, -1));
	    Tcl_SetErrorCode(interp, "ARITH", "IOVERFLOW", s, NULL);
	}
	return TCL_ERROR;
    }
    *intPtr = (int) l;
    return TCL_OK;
#endif
}

/*
 *----------------------------------------------------------------------
 *
 * SetIntFromAny --
 *
 *	Attempts to force the internal representation for a Tcl object to
 *	tclIntType, specifically.
 *
 * Results:
 *	The return value is a standard object Tcl result. If an error occurs
 *	during conversion, an error message is left in the interpreter's
 *	result unless "interp" is NULL.
 *
 *----------------------------------------------------------------------
 */

static int
SetIntFromAny(
    Tcl_Interp *interp,		/* Tcl interpreter */
    Tcl_Obj *objPtr)		/* Pointer to the object to convert */
{
    long l;
    return TclGetLongFromObj(interp, objPtr, &l);
}

/*
 *----------------------------------------------------------------------
 *
 * UpdateStringOfInt --
 *
 *	Update the string representation for an integer object. Note: This
 *	function does not free an existing old string rep so storage will be
 *	lost if this has not already been done.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	The object's string is set to a valid string that results from the
 *	int-to-string conversion.
 *
 *----------------------------------------------------------------------
 */

static void
UpdateStringOfInt(
    register Tcl_Obj *objPtr)	/* Int object whose string rep to update. */
{
    char buffer[TCL_INTEGER_SPACE];
    register int len;

    len = TclFormatInt(buffer, objPtr->internalRep.longValue);

    objPtr->bytes = ckalloc((unsigned) len + 1);
    strcpy(objPtr->bytes, buffer);
    objPtr->length = len;
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_NewLongObj --
 *
 *	If a client is compiled with TCL_MEM_DEBUG defined, calls to
 *	Tcl_NewLongObj to create a new long integer object end up calling the
 *	debugging function Tcl_DbNewLongObj instead.
 *
 *	Otherwise, if the client is compiled without TCL_MEM_DEBUG defined,
 *	calls to Tcl_NewLongObj result in a call to one of the two
 *	Tcl_NewLongObj implementations below. We provide two implementations
 *	so that the Tcl core can be compiled to do memory debugging of the
 *	core even if a client does not request it for itself.
 *
 *	Integer and long integer objects share the same "integer" type
 *	implementation. We store all integers as longs and Tcl_GetIntFromObj
 *	checks whether the current value of the long can be represented by an
 *	int.
 *
 * Results:
 *	The newly created object is returned. This object will have an invalid
 *	string representation. The returned object has ref count 0.
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */

#ifdef TCL_MEM_DEBUG
#undef Tcl_NewLongObj

Tcl_Obj *
Tcl_NewLongObj(
    register long longValue)	/* Long integer used to initialize the
				 * new object. */
{
    return Tcl_DbNewLongObj(longValue, "unknown", 0);
}

#else /* if not TCL_MEM_DEBUG */

Tcl_Obj *
Tcl_NewLongObj(
    register long longValue)	/* Long integer used to initialize the
				 * new object. */
{
    register Tcl_Obj *objPtr;

    TclNewLongObj(objPtr, longValue);
    return objPtr;
}
#endif /* if TCL_MEM_DEBUG */

/*
 *----------------------------------------------------------------------
 *
 * Tcl_DbNewLongObj --
 *
 *	If a client is compiled with TCL_MEM_DEBUG defined, calls to
 *	Tcl_NewIntObj and Tcl_NewLongObj to create new integer or long integer
 *	objects end up calling the debugging function Tcl_DbNewLongObj
 *	instead. We provide two implementations of Tcl_DbNewLongObj so that
 *	whether the Tcl core is compiled to do memory debugging of the core is
 *	independent of whether a client requests debugging for itself.
 *
 *	When the core is compiled with TCL_MEM_DEBUG defined, Tcl_DbNewLongObj
 *	calls Tcl_DbCkalloc directly with the file name and line number from
 *	its caller. This simplifies debugging since then the [memory active]
 *	command will report the caller's file name and line number when
 *	reporting objects that haven't been freed.
 *
 *	Otherwise, when the core is compiled without TCL_MEM_DEBUG defined,
 *	this function just returns the result of calling Tcl_NewLongObj.
 *
 * Results:
 *	The newly created long integer object is returned. This object will
 *	have an invalid string representation. The returned object has ref
 *	count 0.
 *
 * Side effects:
 *	Allocates memory.
 *
 *----------------------------------------------------------------------
 */

#ifdef TCL_MEM_DEBUG

Tcl_Obj *
Tcl_DbNewLongObj(
    register long longValue,	/* Long integer used to initialize the new
				 * object. */
    CONST char *file,		/* The name of the source file calling this
				 * function; used for debugging. */
    int line)			/* Line number in the source file; used for
				 * debugging. */
{
    register Tcl_Obj *objPtr;

    TclDbNewObj(objPtr, file, line);
    objPtr->bytes = NULL;

    objPtr->internalRep.longValue = longValue;
    objPtr->typePtr = &tclIntType;
    return objPtr;
}

#else /* if not TCL_MEM_DEBUG */

Tcl_Obj *
Tcl_DbNewLongObj(
    register long longValue,	/* Long integer used to initialize the new
				 * object. */
    CONST char *file,		/* The name of the source file calling this
				 * function; used for debugging. */
    int line)			/* Line number in the source file; used for
				 * debugging. */
{
    return Tcl_NewLongObj(longValue);
}
#endif /* TCL_MEM_DEBUG */

/*
 *----------------------------------------------------------------------
 *
 * Tcl_SetLongObj --
 *
 *	Modify an object to be an integer object and to have the specified
 *	long integer value.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	The object's old string rep, if any, is freed. Also, any old internal
 *	rep is freed.
 *
 *----------------------------------------------------------------------
 */

void
Tcl_SetLongObj(
    register Tcl_Obj *objPtr,	/* Object whose internal rep to init. */
    register long longValue)	/* Long integer used to initialize the
				 * object's value. */
{
    if (Tcl_IsShared(objPtr)) {
	Tcl_Panic("%s called with shared object", "Tcl_SetLongObj");
    }

    TclSetLongObj(objPtr, longValue);
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_GetLongFromObj --
 *
 *	Attempt to return an long integer from the Tcl object "objPtr". If the
 *	object is not already an int object, an attempt will be made to
 *	convert it to one.
 *
 * Results:
 *	The return value is a standard Tcl object result. If an error occurs
 *	during conversion, an error message is left in the interpreter's
 *	result unless "interp" is NULL.
 *
 * Side effects:
 *	If the object is not already an int object, the conversion will free
 *	any old internal representation.
 *
 *----------------------------------------------------------------------
 */

int
Tcl_GetLongFromObj(
    Tcl_Interp *interp, 	/* Used for error reporting if not NULL. */
    register Tcl_Obj *objPtr,	/* The object from which to get a long. */
    register long *longPtr)	/* Place to store resulting long. */
{
    do {
	if (objPtr->typePtr == &tclIntType) {
	    *longPtr = objPtr->internalRep.longValue;
	    return TCL_OK;
	}
#ifndef NO_WIDE_TYPE
	if (objPtr->typePtr == &tclWideIntType) {
	    /*
	     * We return any integer in the range -ULONG_MAX to ULONG_MAX
	     * converted to a long, ignoring overflow. The rule preserves
	     * existing semantics for conversion of integers on input, but
	     * avoids inadvertent demotion of wide integers to 32-bit ones in
	     * the internal rep.
	     */

	    Tcl_WideInt w = objPtr->internalRep.wideValue;
	    if (w >= -(Tcl_WideInt)(ULONG_MAX)
		    && w <= (Tcl_WideInt)(ULONG_MAX)) {
		*longPtr = Tcl_WideAsLong(w);
		return TCL_OK;
	    }
	    goto tooLarge;
	}
#endif
        if (objPtr->typePtr == &tclDoubleType) {
            if (interp != NULL) {
		Tcl_Obj *msg;

		TclNewLiteralStringObj(msg, "expected integer but got \"");
		Tcl_AppendObjToObj(msg, objPtr);
		Tcl_AppendToObj(msg, "\"", -1);
		Tcl_SetObjResult(interp, msg);
	    }
	    return TCL_ERROR;
	}
        if (objPtr->typePtr == &tclBignumType) {
	    /*
	     * Must check for those bignum values that can fit in a long, even
	     * when auto-narrowing is enabled. Only those values in the signed
	     * long range get auto-narrowed to tclIntType, while all the
	     * values in the unsigned long range will fit in a long.
	     */

	    mp_int big;

	    UNPACK_BIGNUM(objPtr, big);
	    if ((size_t)(big.used) <= (CHAR_BIT * sizeof(long) + DIGIT_BIT - 1)
		    / DIGIT_BIT) {
		unsigned long value = 0, numBytes = sizeof(long);
		long scratch;
		unsigned char *bytes = (unsigned char *)&scratch;
		if (mp_to_unsigned_bin_n(&big, bytes, &numBytes) == MP_OKAY) {
		    while (numBytes-- > 0) {
			value = (value << CHAR_BIT) | *bytes++;
		    }
		    if (big.sign) {
			*longPtr = - (long) value;
		    } else {
			*longPtr = (long) value;
		    }
		    return TCL_OK;
		}
	    }
#ifndef NO_WIDE_TYPE
	tooLarge:
#endif
	    if (interp != NULL) {
		char *s = "integer value too large to represent";
		Tcl_Obj *msg = Tcl_NewStringObj(s, -1);

		Tcl_SetObjResult(interp, msg);
		Tcl_SetErrorCode(interp, "ARITH", "IOVERFLOW", s, NULL);
	    }
	    return TCL_ERROR;
	}
    } while (TclParseNumber(interp, objPtr, "integer", NULL, -1, NULL,
	    TCL_PARSE_INTEGER_ONLY)==TCL_OK);
    return TCL_ERROR;
}
#ifndef NO_WIDE_TYPE

/*
 *----------------------------------------------------------------------
 *
 * UpdateStringOfWideInt --
 *
 *	Update the string representation for a wide integer object. Note: this
 *	function does not free an existing old string rep so storage will be
 *	lost if this has not already been done.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	The object's string is set to a valid string that results from the
 *	wideInt-to-string conversion.
 *
 *----------------------------------------------------------------------
 */

static void
UpdateStringOfWideInt(
    register Tcl_Obj *objPtr)	/* Int object whose string rep to update. */
{
    char buffer[TCL_INTEGER_SPACE+2];
    register unsigned len;
    register Tcl_WideInt wideVal = objPtr->internalRep.wideValue;

    /*
     * Note that sprintf will generate a compiler warning under Mingw claiming
     * %I64 is an unknown format specifier. Just ignore this warning. We can't
     * use %L as the format specifier since that gets printed as a 32 bit
     * value.
     */

    sprintf(buffer, "%" TCL_LL_MODIFIER "d", wideVal);
    len = strlen(buffer);
    objPtr->bytes = ckalloc((unsigned) len + 1);
    memcpy(objPtr->bytes, buffer, len + 1);
    objPtr->length = len;
}
#endif /* !NO_WIDE_TYPE */

/*
 *----------------------------------------------------------------------
 *
 * Tcl_NewWideIntObj --
 *
 *	If a client is compiled with TCL_MEM_DEBUG defined, calls to
 *	Tcl_NewWideIntObj to create a new 64-bit integer object end up calling
 *	the debugging function Tcl_DbNewWideIntObj instead.
 *
 *	Otherwise, if the client is compiled without TCL_MEM_DEBUG defined,
 *	calls to Tcl_NewWideIntObj result in a call to one of the two
 *	Tcl_NewWideIntObj implementations below. We provide two
 *	implementations so that the Tcl core can be compiled to do memory
 *	debugging of the core even if a client does not request it for itself.
 *
 * Results:
 *	The newly created object is returned. This object will have an invalid
 *	string representation. The returned object has ref count 0.
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */

#ifdef TCL_MEM_DEBUG
#undef Tcl_NewWideIntObj

Tcl_Obj *
Tcl_NewWideIntObj(
    register Tcl_WideInt wideValue)
				/* Wide integer used to initialize the new
				 * object. */
{
    return Tcl_DbNewWideIntObj(wideValue, "unknown", 0);
}

#else /* if not TCL_MEM_DEBUG */

Tcl_Obj *
Tcl_NewWideIntObj(
    register Tcl_WideInt wideValue)
				/* Wide integer used to initialize the new
				 * object. */
{
    register Tcl_Obj *objPtr;

    TclNewObj(objPtr);
    Tcl_SetWideIntObj(objPtr, wideValue);
    return objPtr;
}
#endif /* if TCL_MEM_DEBUG */

/*
 *----------------------------------------------------------------------
 *
 * Tcl_DbNewWideIntObj --
 *
 *	If a client is compiled with TCL_MEM_DEBUG defined, calls to
 *	Tcl_NewWideIntObj to create new wide integer end up calling the
 *	debugging function Tcl_DbNewWideIntObj instead. We provide two
 *	implementations of Tcl_DbNewWideIntObj so that whether the Tcl core is
 *	compiled to do memory debugging of the core is independent of whether
 *	a client requests debugging for itself.
 *
 *	When the core is compiled with TCL_MEM_DEBUG defined,
 *	Tcl_DbNewWideIntObj calls Tcl_DbCkalloc directly with the file name
 *	and line number from its caller. This simplifies debugging since then
 *	the checkmem command will report the caller's file name and line
 *	number when reporting objects that haven't been freed.
 *
 *	Otherwise, when the core is compiled without TCL_MEM_DEBUG defined,
 *	this function just returns the result of calling Tcl_NewWideIntObj.
 *
 * Results:
 *	The newly created wide integer object is returned. This object will
 *	have an invalid string representation. The returned object has ref
 *	count 0.
 *
 * Side effects:
 *	Allocates memory.
 *
 *----------------------------------------------------------------------
 */

#ifdef TCL_MEM_DEBUG

Tcl_Obj *
Tcl_DbNewWideIntObj(
    register Tcl_WideInt wideValue,
				/* Wide integer used to initialize the new
				 * object. */
    CONST char *file,		/* The name of the source file calling this
				 * function; used for debugging. */
    int line)			/* Line number in the source file; used for
				 * debugging. */
{
    register Tcl_Obj *objPtr;

    TclDbNewObj(objPtr, file, line);
    Tcl_SetWideIntObj(objPtr, wideValue);
    return objPtr;
}

#else /* if not TCL_MEM_DEBUG */

Tcl_Obj *
Tcl_DbNewWideIntObj(
    register Tcl_WideInt wideValue,
				/* Long integer used to initialize the new
				 * object. */
    CONST char *file,		/* The name of the source file calling this
				 * function; used for debugging. */
    int line)			/* Line number in the source file; used for
				 * debugging. */
{
    return Tcl_NewWideIntObj(wideValue);
}
#endif /* TCL_MEM_DEBUG */

/*
 *----------------------------------------------------------------------
 *
 * Tcl_SetWideIntObj --
 *
 *	Modify an object to be a wide integer object and to have the specified
 *	wide integer value.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	The object's old string rep, if any, is freed. Also, any old internal
 *	rep is freed.
 *
 *----------------------------------------------------------------------
 */

void
Tcl_SetWideIntObj(
    register Tcl_Obj *objPtr,	/* Object w. internal rep to init. */
    register Tcl_WideInt wideValue)
				/* Wide integer used to initialize the
				 * object's value. */
{
    if (Tcl_IsShared(objPtr)) {
	Tcl_Panic("%s called with shared object", "Tcl_SetWideIntObj");
    }

    if ((wideValue >= (Tcl_WideInt) LONG_MIN)
	    && (wideValue <= (Tcl_WideInt) LONG_MAX)) {
	TclSetLongObj(objPtr, (long) wideValue);
    } else {
#ifndef NO_WIDE_TYPE
	TclSetWideIntObj(objPtr, wideValue);
#else
	mp_int big;

	TclBNInitBignumFromWideInt(&big, wideValue);
	Tcl_SetBignumObj(objPtr, &big);
#endif
    }
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_GetWideIntFromObj --
 *
 *	Attempt to return a wide integer from the Tcl object "objPtr". If the
 *	object is not already a wide int object, an attempt will be made to
 *	convert it to one.
 *
 * Results:
 *	The return value is a standard Tcl object result. If an error occurs
 *	during conversion, an error message is left in the interpreter's
 *	result unless "interp" is NULL.
 *
 * Side effects:
 *	If the object is not already an int object, the conversion will free
 *	any old internal representation.
 *
 *----------------------------------------------------------------------
 */

int
Tcl_GetWideIntFromObj(
    Tcl_Interp *interp, 	/* Used for error reporting if not NULL. */
    register Tcl_Obj *objPtr,	/* Object from which to get a wide int. */
    register Tcl_WideInt *wideIntPtr)
				/* Place to store resulting long. */
{
    do {
#ifndef NO_WIDE_TYPE
	if (objPtr->typePtr == &tclWideIntType) {
	    *wideIntPtr = objPtr->internalRep.wideValue;
	    return TCL_OK;
	}
#endif
	if (objPtr->typePtr == &tclIntType) {
	    *wideIntPtr = (Tcl_WideInt) objPtr->internalRep.longValue;
	    return TCL_OK;
	}
        if (objPtr->typePtr == &tclDoubleType) {
            if (interp != NULL) {
		Tcl_Obj *msg;

		TclNewLiteralStringObj(msg, "expected integer but got \"");
		Tcl_AppendObjToObj(msg, objPtr);
		Tcl_AppendToObj(msg, "\"", -1);
		Tcl_SetObjResult(interp, msg);
	    }
	    return TCL_ERROR;
	}
        if (objPtr->typePtr == &tclBignumType) {
	    /*
	     * Must check for those bignum values that can fit in a
	     * Tcl_WideInt, even when auto-narrowing is enabled.
	     */

	    mp_int big;

	    UNPACK_BIGNUM(objPtr, big);
	    if ((size_t)(big.used) <= (CHAR_BIT * sizeof(Tcl_WideInt)
		     + DIGIT_BIT - 1) / DIGIT_BIT) {
		Tcl_WideUInt value = 0;
		unsigned long numBytes = sizeof(Tcl_WideInt);
		Tcl_WideInt scratch;
		unsigned char *bytes = (unsigned char *) &scratch;

		if (mp_to_unsigned_bin_n(&big, bytes, &numBytes) == MP_OKAY) {
		    while (numBytes-- > 0) {
			value = (value << CHAR_BIT) | *bytes++;
		    }
		    if (big.sign) {
			*wideIntPtr = - (Tcl_WideInt) value;
		    } else {
			*wideIntPtr = (Tcl_WideInt) value;
		    }
		    return TCL_OK;
		}
	    }
	    if (interp != NULL) {
		char *s = "integer value too large to represent";
		Tcl_Obj* msg = Tcl_NewStringObj(s, -1);

		Tcl_SetObjResult(interp, msg);
		Tcl_SetErrorCode(interp, "ARITH", "IOVERFLOW", s, NULL);
	    }
	    return TCL_ERROR;
	}
    } while (TclParseNumber(interp, objPtr, "integer", NULL, -1, NULL,
	    TCL_PARSE_INTEGER_ONLY)==TCL_OK);
    return TCL_ERROR;
}
#ifndef NO_WIDE_TYPE

/*
 *----------------------------------------------------------------------
 *
 * SetWideIntFromAny --
 *
 *	Attempts to force the internal representation for a Tcl object to
 *	tclWideIntType, specifically.
 *
 * Results:
 *	The return value is a standard object Tcl result. If an error occurs
 *	during conversion, an error message is left in the interpreter's
 *	result unless "interp" is NULL.
 *
 *----------------------------------------------------------------------
 */

static int
SetWideIntFromAny(
    Tcl_Interp *interp,		/* Tcl interpreter */
    Tcl_Obj *objPtr)		/* Pointer to the object to convert */
{
    Tcl_WideInt w;
    return Tcl_GetWideIntFromObj(interp, objPtr, &w);
}
#endif /* !NO_WIDE_TYPE */

/*
 *----------------------------------------------------------------------
 *
 * FreeBignum --
 *
 *	This function frees the internal rep of a bignum.
 *
 * Results:
 *	None.
 *
 *----------------------------------------------------------------------
 */

static void
FreeBignum(
    Tcl_Obj *objPtr)
{
    mp_int toFree;		/* Bignum to free */

    UNPACK_BIGNUM(objPtr, toFree);
    mp_clear(&toFree);
    if ((long)(objPtr->internalRep.ptrAndLongRep.value) < 0) {
	ckfree((char *)objPtr->internalRep.ptrAndLongRep.ptr);
    }
}

/*
 *----------------------------------------------------------------------
 *
 * DupBignum --
 *
 *	This function duplicates the internal rep of a bignum.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	The destination object receies a copy of the source object
 *
 *----------------------------------------------------------------------
 */

static void
DupBignum(
    Tcl_Obj *srcPtr,
    Tcl_Obj *copyPtr)
{
    mp_int bignumVal;
    mp_int bignumCopy;

    copyPtr->typePtr = &tclBignumType;
    UNPACK_BIGNUM(srcPtr, bignumVal);
    if (mp_init_copy(&bignumCopy, &bignumVal) != MP_OKAY) {
	Tcl_Panic("initialization failure in DupBignum");
    }
    PACK_BIGNUM(bignumCopy, copyPtr);
}

/*
 *----------------------------------------------------------------------
 *
 * UpdateStringOfBignum --
 *
 *	This function updates the string representation of a bignum object.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	The object's string is set to whatever results from the bignum-
 *	to-string conversion.
 *
 * The object's existing string representation is NOT freed; memory will leak
 * if the string rep is still valid at the time this function is called.
 *
 *----------------------------------------------------------------------
 */

static void
UpdateStringOfBignum(
    Tcl_Obj *objPtr)
{
    mp_int bignumVal;
    int size;
    int status;
    char* stringVal;

    UNPACK_BIGNUM(objPtr, bignumVal);
    status = mp_radix_size(&bignumVal, 10, &size);
    if (status != MP_OKAY) {
	Tcl_Panic("radix size failure in UpdateStringOfBignum");
    }
    if (size == 3) {
	/*
	 * mp_radix_size() returns 3 when more than INT_MAX bytes would be
	 * needed to hold the string rep (because mp_radix_size ignores
	 * integer overflow issues). When we know the string rep will be more
	 * than 3, we can conclude the string rep would overflow our string
	 * length limits.
	 *
	 * Note that so long as we enforce our bignums to the size that fits
	 * in a packed bignum, this branch will never be taken.
	 */

	Tcl_Panic("UpdateStringOfBignum: string length limit exceeded");
    }
    stringVal = ckalloc((size_t) size);
    status = mp_toradix_n(&bignumVal, stringVal, 10, size);
    if (status != MP_OKAY) {
	Tcl_Panic("conversion failure in UpdateStringOfBignum");
    }
    objPtr->bytes = stringVal;
    objPtr->length = size - 1;	/* size includes a trailing null byte */
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_NewBignumObj --
 *
 *	Creates an initializes a bignum object.
 *
 * Results:
 *	Returns the newly created object.
 *
 * Side effects:
 *	The bignum value is cleared, since ownership has transferred to Tcl.
 *
 *----------------------------------------------------------------------
 */

#ifdef TCL_MEM_DEBUG
#undef Tcl_NewBignumObj

Tcl_Obj *
Tcl_NewBignumObj(
    mp_int *bignumValue)
{
    return Tcl_DbNewBignumObj(bignumValue, "unknown", 0);
}
#else
Tcl_Obj *
Tcl_NewBignumObj(
    mp_int *bignumValue)
{
    Tcl_Obj* objPtr;

    TclNewObj(objPtr);
    Tcl_SetBignumObj(objPtr, bignumValue);
    return objPtr;
}
#endif

/*
 *----------------------------------------------------------------------
 *
 * Tcl_DbNewBignumObj --
 *
 *	This function is normally called when debugging: that is, when
 *	TCL_MEM_DEBUG is defined. It constructs a bignum object, recording the
 *	creation point so that [memory active] can report it.
 *
 * Results:
 *	Returns the newly created object.
 *
 * Side effects:
 *	The bignum value is cleared, since ownership has transferred to Tcl.
 *
 *----------------------------------------------------------------------
 */

#ifdef TCL_MEM_DEBUG
Tcl_Obj *
Tcl_DbNewBignumObj(
    mp_int *bignumValue,
    CONST char *file,
    int line)
{
    Tcl_Obj *objPtr;

    TclDbNewObj(objPtr, file, line);
    Tcl_SetBignumObj(objPtr, bignumValue);
    return objPtr;
}
#else
Tcl_Obj *
Tcl_DbNewBignumObj(
    mp_int *bignumValue,
    CONST char *file,
    int line)
{
    return Tcl_NewBignumObj(bignumValue);
}
#endif

/*
 *----------------------------------------------------------------------
 *
 * GetBignumFromObj --
 *
 *	This function retrieves a 'bignum' value from a Tcl object, converting
 *	the object if necessary. Either copies or transfers the mp_int value
 *	depending on the copy flag value passed in.
 *
 * Results:
 *	Returns TCL_OK if the conversion is successful, TCL_ERROR otherwise.
 *
 * Side effects:
 *	A copy of bignum is stored in *bignumValue, which is expected to be
 *	uninitialized or cleared. If conversion fails, and the 'interp'
 *	argument is not NULL, an error message is stored in the interpreter
 *	result.
 *
 *----------------------------------------------------------------------
 */

static int
GetBignumFromObj(
    Tcl_Interp *interp,		/* Tcl interpreter for error reporting */
    Tcl_Obj *objPtr,		/* Object to read */
    int copy,			/* Whether to copy the returned bignum value */
    mp_int *bignumValue)	/* Returned bignum value. */
{
    do {
	if (objPtr->typePtr == &tclBignumType) {
	    if (copy || Tcl_IsShared(objPtr)) {
		mp_int temp;
		UNPACK_BIGNUM(objPtr, temp);
		mp_init_copy(bignumValue, &temp);
	    } else {
		UNPACK_BIGNUM(objPtr, *bignumValue);
		objPtr->internalRep.ptrAndLongRep.ptr = NULL;
		objPtr->internalRep.ptrAndLongRep.value = 0;
		objPtr->typePtr = NULL;
		if (objPtr->bytes == NULL) {
		    TclInitStringRep(objPtr, tclEmptyStringRep, 0);
		}
	    }
	    return TCL_OK;
	}
	if (objPtr->typePtr == &tclIntType) {
	    TclBNInitBignumFromLong(bignumValue, objPtr->internalRep.longValue);
	    return TCL_OK;
	}
#ifndef NO_WIDE_TYPE
	if (objPtr->typePtr == &tclWideIntType) {
	    TclBNInitBignumFromWideInt(bignumValue,
		    objPtr->internalRep.wideValue);
	    return TCL_OK;
	}
#endif
	if (objPtr->typePtr == &tclDoubleType) {
	    if (interp != NULL) {
		Tcl_Obj *msg;

		TclNewLiteralStringObj(msg, "expected integer but got \"");
		Tcl_AppendObjToObj(msg, objPtr);
		Tcl_AppendToObj(msg, "\"", -1);
		Tcl_SetObjResult(interp, msg);
	    }
	    return TCL_ERROR;
	}
    } while (TclParseNumber(interp, objPtr, "integer", NULL, -1, NULL,
	    TCL_PARSE_INTEGER_ONLY)==TCL_OK);
    return TCL_ERROR;
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_GetBignumFromObj --
 *
 *	This function retrieves a 'bignum' value from a Tcl object, converting
 *	the object if necessary.
 *
 * Results:
 *	Returns TCL_OK if the conversion is successful, TCL_ERROR otherwise.
 *
 * Side effects:
 *	A copy of bignum is stored in *bignumValue, which is expected to be
 *	uninitialized or cleared. If conversion fails, an the 'interp'
 *	argument is not NULL, an error message is stored in the interpreter
 *	result.
 *
 *	It is expected that the caller will NOT have invoked mp_init on the
 *	bignum value before passing it in. Tcl will initialize the mp_int as
 *	it sets the value. The value is a copy of the value in objPtr, so it
 *	becomes the responsibility of the caller to call mp_clear on it.
 *
 *----------------------------------------------------------------------
 */

int
Tcl_GetBignumFromObj(
    Tcl_Interp *interp,		/* Tcl interpreter for error reporting */
    Tcl_Obj *objPtr,		/* Object to read */
    mp_int *bignumValue)	/* Returned bignum value. */
{
    return GetBignumFromObj(interp, objPtr, 1, bignumValue);
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_TakeBignumFromObj --
 *
 *	This function retrieves a 'bignum' value from a Tcl object, converting
 *	the object if necessary.
 *
 * Results:
 *	Returns TCL_OK if the conversion is successful, TCL_ERROR otherwise.
 *
 * Side effects:
 *	A copy of bignum is stored in *bignumValue, which is expected to be
 *	uninitialized or cleared. If conversion fails, an the 'interp'
 *	argument is not NULL, an error message is stored in the interpreter
 *	result.
 *
 *	It is expected that the caller will NOT have invoked mp_init on the
 *	bignum value before passing it in. Tcl will initialize the mp_int as
 *	it sets the value. The value is transferred from the internals of
 *	objPtr to the caller, passing responsibility of the caller to call
 *	mp_clear on it. The objPtr is cleared to hold an empty value.
 *
 *----------------------------------------------------------------------
 */

int
Tcl_TakeBignumFromObj(
    Tcl_Interp *interp,		/* Tcl interpreter for error reporting */
    Tcl_Obj *objPtr,		/* Object to read */
    mp_int *bignumValue)	/* Returned bignum value. */
{
    return GetBignumFromObj(interp, objPtr, 0, bignumValue);
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_SetBignumObj --
 *
 *	This function sets the value of a Tcl_Obj to a large integer.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	Object value is stored. The bignum value is cleared, since ownership
 *	has transferred to Tcl.
 *
 *----------------------------------------------------------------------
 */

void
Tcl_SetBignumObj(
    Tcl_Obj *objPtr,		/* Object to set */
    mp_int *bignumValue)	/* Value to store */
{
    if (Tcl_IsShared(objPtr)) {
	Tcl_Panic("%s called with shared object", "Tcl_SetBignumObj");
    }
    if ((size_t)(bignumValue->used)
	    <= (CHAR_BIT * sizeof(long) + DIGIT_BIT - 1) / DIGIT_BIT) {
	unsigned long value = 0, numBytes = sizeof(long);
	long scratch;
	unsigned char *bytes = (unsigned char *)&scratch;
	if (mp_to_unsigned_bin_n(bignumValue, bytes, &numBytes) != MP_OKAY) {
	    goto tooLargeForLong;
	}
	while (numBytes-- > 0) {
	    value = (value << CHAR_BIT) | *bytes++;
	}
	if (value > (((~(unsigned long)0) >> 1) + bignumValue->sign)) {
	    goto tooLargeForLong;
	}
	if (bignumValue->sign) {
	    TclSetLongObj(objPtr, -(long)value);
	} else {
	    TclSetLongObj(objPtr, (long)value);
	}
	mp_clear(bignumValue);
	return;
    }
  tooLargeForLong:
#ifndef NO_WIDE_TYPE
    if ((size_t)(bignumValue->used)
	    <= (CHAR_BIT * sizeof(Tcl_WideInt) + DIGIT_BIT - 1) / DIGIT_BIT) {
	Tcl_WideUInt value = 0;
	unsigned long numBytes = sizeof(Tcl_WideInt);
	Tcl_WideInt scratch;
	unsigned char *bytes = (unsigned char *)&scratch;
	if (mp_to_unsigned_bin_n(bignumValue, bytes, &numBytes) != MP_OKAY) {
	    goto tooLargeForWide;
	}
	while (numBytes-- > 0) {
	    value = (value << CHAR_BIT) | *bytes++;
	}
	if (value > (((~(Tcl_WideUInt)0) >> 1) + bignumValue->sign)) {
	    goto tooLargeForWide;
	}
	if (bignumValue->sign) {
	    TclSetWideIntObj(objPtr, -(Tcl_WideInt)value);
	} else {
	    TclSetWideIntObj(objPtr, (Tcl_WideInt)value);
	}
	mp_clear(bignumValue);
	return;
    }
  tooLargeForWide:
#endif
    TclInvalidateStringRep(objPtr);
    TclFreeIntRep(objPtr);
    TclSetBignumIntRep(objPtr, bignumValue);
}

void
TclSetBignumIntRep(
    Tcl_Obj *objPtr,
    mp_int *bignumValue)
{
    objPtr->typePtr = &tclBignumType;
    PACK_BIGNUM(*bignumValue, objPtr);

    /*
     * Clear the mp_int value.
     * Don't call mp_clear() because it would free the digit array
     * we just packed into the Tcl_Obj.
     */

    bignumValue->dp = NULL;
    bignumValue->alloc = bignumValue->used = 0;
    bignumValue->sign = MP_NEG;
}

/*
 *----------------------------------------------------------------------
 *
 * TclGetNumberFromObj --
 *
 * Results:
 *
 * Side effects:
 *
 *----------------------------------------------------------------------
 */

int TclGetNumberFromObj(
    Tcl_Interp *interp,
    Tcl_Obj *objPtr,
    ClientData *clientDataPtr,
    int *typePtr)
{
    do {
	if (objPtr->typePtr == &tclDoubleType) {
	    if (TclIsNaN(objPtr->internalRep.doubleValue)) {
		*typePtr = TCL_NUMBER_NAN;
	    } else {
		*typePtr = TCL_NUMBER_DOUBLE;
	    }
	    *clientDataPtr = &(objPtr->internalRep.doubleValue);
	    return TCL_OK;
	}
	if (objPtr->typePtr == &tclIntType) {
	    *typePtr = TCL_NUMBER_LONG;
	    *clientDataPtr = &(objPtr->internalRep.longValue);
	    return TCL_OK;
	}
#ifndef NO_WIDE_TYPE
	if (objPtr->typePtr == &tclWideIntType) {
	    *typePtr = TCL_NUMBER_WIDE;
	    *clientDataPtr = &(objPtr->internalRep.wideValue);
	    return TCL_OK;
	}
#endif
	if (objPtr->typePtr == &tclBignumType) {
	    static Tcl_ThreadDataKey bignumKey;
	    mp_int *bigPtr = Tcl_GetThreadData(&bignumKey,
		    (int) sizeof(mp_int));
	    UNPACK_BIGNUM( objPtr, *bigPtr );
	    *typePtr = TCL_NUMBER_BIG;
	    *clientDataPtr = bigPtr;
	    return TCL_OK;
	}
    } while (TCL_OK ==
	    TclParseNumber(interp, objPtr, "number", NULL, -1, NULL, 0));
    return TCL_ERROR;
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_DbIncrRefCount --
 *
 *	This function is normally called when debugging: i.e., when
 *	TCL_MEM_DEBUG is defined. This checks to see whether or not the memory
 *	has been freed before incrementing the ref count.
 *
 *	When TCL_MEM_DEBUG is not defined, this function just increments the
 *	reference count of the object.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	The object's ref count is incremented.
 *
 *----------------------------------------------------------------------
 */

void
Tcl_DbIncrRefCount(
    register Tcl_Obj *objPtr,	/* The object we are registering a reference
				 * to. */
    CONST char *file,		/* The name of the source file calling this
				 * function; used for debugging. */
    int line)			/* Line number in the source file; used for
				 * debugging. */
{
#ifdef TCL_MEM_DEBUG
    if (objPtr->refCount == 0x61616161) {
	fprintf(stderr, "file = %s, line = %d\n", file, line);
	fflush(stderr);
	Tcl_Panic("incrementing refCount of previously disposed object");
    }

# ifdef TCL_THREADS
    /*
     * Check to make sure that the Tcl_Obj was allocated by the current
     * thread. Don't do this check when shutting down since thread local
     * storage can be finalized before the last Tcl_Obj is freed.
     */

    if (!TclInExit()) {
	Tcl_HashTable *tablePtr;
	Tcl_HashEntry *hPtr;
	ThreadSpecificData *tsdPtr = TCL_TSD_INIT(&dataKey);

	tablePtr = tsdPtr->objThreadMap;
	if (!tablePtr) {
	    Tcl_Panic("object table not initialized");
	}
	hPtr = Tcl_FindHashEntry(tablePtr, (char *) objPtr);
	if (!hPtr) {
	    Tcl_Panic("%s%s",
		    "Trying to incr ref count of "
		    "Tcl_Obj allocated in another thread");
	}
    }
# endif
#endif
    ++(objPtr)->refCount;
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_DbDecrRefCount --
 *
 *	This function is normally called when debugging: i.e., when
 *	TCL_MEM_DEBUG is defined. This checks to see whether or not the memory
 *	has been freed before decrementing the ref count.
 *
 *	When TCL_MEM_DEBUG is not defined, this function just decrements the
 *	reference count of the object.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	The object's ref count is incremented.
 *
 *----------------------------------------------------------------------
 */

void
Tcl_DbDecrRefCount(
    register Tcl_Obj *objPtr,	/* The object we are releasing a reference
				 * to. */
    CONST char *file,		/* The name of the source file calling this
				 * function; used for debugging. */
    int line)			/* Line number in the source file; used for
				 * debugging. */
{
#ifdef TCL_MEM_DEBUG
    if (objPtr->refCount == 0x61616161) {
	fprintf(stderr, "file = %s, line = %d\n", file, line);
	fflush(stderr);
	Tcl_Panic("decrementing refCount of previously disposed object");
    }

# ifdef TCL_THREADS
    /*
     * Check to make sure that the Tcl_Obj was allocated by the current
     * thread. Don't do this check when shutting down since thread local
     * storage can be finalized before the last Tcl_Obj is freed.
     */

    if (!TclInExit()) {
	Tcl_HashTable *tablePtr;
	Tcl_HashEntry *hPtr;
	ThreadSpecificData *tsdPtr = TCL_TSD_INIT(&dataKey);

	tablePtr = tsdPtr->objThreadMap;
	if (!tablePtr) {
	    Tcl_Panic("object table not initialized");
	}
	hPtr = Tcl_FindHashEntry(tablePtr, (char *) objPtr);
	if (!hPtr) {
	    Tcl_Panic("%s%s",
		    "Trying to decr ref count of "
		    "Tcl_Obj allocated in another thread");
	}

	/* If the Tcl_Obj is going to be deleted, remove the entry */
	if ((((objPtr)->refCount) - 1) <= 0) {
	    Tcl_DeleteHashEntry(hPtr);
	}
    }
# endif
#endif
    if (--(objPtr)->refCount <= 0) {
	TclFreeObj(objPtr);
    }
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_DbIsShared --
 *
 *	This function is normally called when debugging: i.e., when
 *	TCL_MEM_DEBUG is defined. It tests whether the object has a ref count
 *	greater than one.
 *
 *	When TCL_MEM_DEBUG is not defined, this function just tests if the
 *	object has a ref count greater than one.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */

int
Tcl_DbIsShared(
    register Tcl_Obj *objPtr,	/* The object to test for being shared. */
    CONST char *file,		/* The name of the source file calling this
				 * function; used for debugging. */
    int line)			/* Line number in the source file; used for
				 * debugging. */
{
#ifdef TCL_MEM_DEBUG
    if (objPtr->refCount == 0x61616161) {
	fprintf(stderr, "file = %s, line = %d\n", file, line);
	fflush(stderr);
	Tcl_Panic("checking whether previously disposed object is shared");
    }

# ifdef TCL_THREADS
    /*
     * Check to make sure that the Tcl_Obj was allocated by the current
     * thread. Don't do this check when shutting down since thread local
     * storage can be finalized before the last Tcl_Obj is freed.
     */

    if (!TclInExit()) {
	Tcl_HashTable *tablePtr;
	Tcl_HashEntry *hPtr;
	ThreadSpecificData *tsdPtr = TCL_TSD_INIT(&dataKey);
	tablePtr = tsdPtr->objThreadMap;
	if (!tablePtr) {
	    Tcl_Panic("object table not initialized");
	}
	hPtr = Tcl_FindHashEntry(tablePtr, (char *) objPtr);
	if (!hPtr) {
	    Tcl_Panic("%s%s",
		    "Trying to check shared status of"
		    "Tcl_Obj allocated in another thread");
	}
    }
# endif
#endif

#ifdef TCL_COMPILE_STATS
    Tcl_MutexLock(&tclObjMutex);
    if ((objPtr)->refCount <= 1) {
	tclObjsShared[1]++;
    } else if ((objPtr)->refCount < TCL_MAX_SHARED_OBJ_STATS) {
	tclObjsShared[(objPtr)->refCount]++;
    } else {
	tclObjsShared[0]++;
    }
    Tcl_MutexUnlock(&tclObjMutex);
#endif

    return ((objPtr)->refCount > 1);
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_InitObjHashTable --
 *
 *	Given storage for a hash table, set up the fields to prepare the hash
 *	table for use, the keys are Tcl_Obj *.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	TablePtr is now ready to be passed to Tcl_FindHashEntry and
 *	Tcl_CreateHashEntry.
 *
 *----------------------------------------------------------------------
 */

void
Tcl_InitObjHashTable(
    register Tcl_HashTable *tablePtr)
				/* Pointer to table record, which is supplied
				 * by the caller. */
{
    Tcl_InitCustomHashTable(tablePtr, TCL_CUSTOM_PTR_KEYS,
	    &tclObjHashKeyType);
}

/*
 *----------------------------------------------------------------------
 *
 * AllocObjEntry --
 *
 *	Allocate space for a Tcl_HashEntry containing the Tcl_Obj * key.
 *
 * Results:
 *	The return value is a pointer to the created entry.
 *
 * Side effects:
 *	Increments the reference count on the object.
 *
 *----------------------------------------------------------------------
 */

static Tcl_HashEntry *
AllocObjEntry(
    Tcl_HashTable *tablePtr,	/* Hash table. */
    void *keyPtr)		/* Key to store in the hash table entry. */
{
    Tcl_Obj *objPtr = (Tcl_Obj *) keyPtr;
    Tcl_HashEntry *hPtr;

    hPtr = (Tcl_HashEntry *) ckalloc((unsigned) (sizeof(Tcl_HashEntry)));
    hPtr->key.oneWordValue = (char *) objPtr;
    Tcl_IncrRefCount(objPtr);
    hPtr->clientData = NULL;

    return hPtr;
}

/*
 *----------------------------------------------------------------------
 *
 * TclCompareObjKeys --
 *
 *	Compares two Tcl_Obj * keys.
 *
 * Results:
 *	The return value is 0 if they are different and 1 if they are the
 *	same.
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */

int
TclCompareObjKeys(
    void *keyPtr,		/* New key to compare. */
    Tcl_HashEntry *hPtr)	/* Existing key to compare. */
{
    Tcl_Obj *objPtr1 = (Tcl_Obj *) keyPtr;
    Tcl_Obj *objPtr2 = (Tcl_Obj *) hPtr->key.oneWordValue;
    register CONST char *p1, *p2;
    register int l1, l2;

    /*
     * If the object pointers are the same then they match.
     */

    if (objPtr1 == objPtr2) {
	return 1;
    }

    /*
     * Don't use Tcl_GetStringFromObj as it would prevent l1 and l2 being
     * in a register.
     */

    p1 = TclGetString(objPtr1);
    l1 = objPtr1->length;
    p2 = TclGetString(objPtr2);
    l2 = objPtr2->length;

    /*
     * Only compare if the string representations are of the same length.
     */

    if (l1 == l2) {
	for (;; p1++, p2++, l1--) {
	    if (*p1 != *p2) {
		break;
	    }
	    if (l1 == 0) {
		return 1;
	    }
	}
    }

    return 0;
}

/*
 *----------------------------------------------------------------------
 *
 * TclFreeObjEntry --
 *
 *	Frees space for a Tcl_HashEntry containing the Tcl_Obj * key.
 *
 * Results:
 *	The return value is a pointer to the created entry.
 *
 * Side effects:
 *	Decrements the reference count of the object.
 *
 *----------------------------------------------------------------------
 */

void
TclFreeObjEntry(
    Tcl_HashEntry *hPtr)	/* Hash entry to free. */
{
    Tcl_Obj *objPtr = (Tcl_Obj *) hPtr->key.oneWordValue;

    Tcl_DecrRefCount(objPtr);
    ckfree((char *) hPtr);
}

/*
 *----------------------------------------------------------------------
 *
 * TclHashObjKey --
 *
 *	Compute a one-word summary of the string representation of the
 *	Tcl_Obj, which can be used to generate a hash index.
 *
 * Results:
 *	The return value is a one-word summary of the information in the
 *	string representation of the Tcl_Obj.
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */

unsigned int
TclHashObjKey(
    Tcl_HashTable *tablePtr,	/* Hash table. */
    void *keyPtr)		/* Key from which to compute hash value. */
{
    Tcl_Obj *objPtr = (Tcl_Obj *) keyPtr;
    CONST char *string = TclGetString(objPtr);
    int length = objPtr->length;
    unsigned int result = 0;
    int i;

    /*
     * I tried a zillion different hash functions and asked many other people
     * for advice. Many people had their own favorite functions, all
     * different, but no-one had much idea why they were good ones. I chose
     * the one below (multiply by 9 and add new character) because of the
     * following reasons:
     *
     * 1. Multiplying by 10 is perfect for keys that are decimal strings, and
     *	  multiplying by 9 is just about as good.
     * 2. Times-9 is (shift-left-3) plus (old). This means that each
     *	  character's bits hang around in the low-order bits of the hash value
     *	  for ever, plus they spread fairly rapidly up to the high-order bits
     *	  to fill out the hash value. This seems works well both for decimal
     *	  and *non-decimal strings.
     */

    for (i=0 ; i<length ; i++) {
	result += (result << 3) + string[i];
    }
    return result;
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_GetCommandFromObj --
 *
 *	Returns the command specified by the name in a Tcl_Obj.
 *
 * Results:
 *	Returns a token for the command if it is found. Otherwise, if it can't
 *	be found or there is an error, returns NULL.
 *
 * Side effects:
 *	May update the internal representation for the object, caching the
 *	command reference so that the next time this function is called with
 *	the same object, the command can be found quickly.
 *
 *----------------------------------------------------------------------
 */

Tcl_Command
Tcl_GetCommandFromObj(
    Tcl_Interp *interp,		/* The interpreter in which to resolve the
				 * command and to report errors. */
    register Tcl_Obj *objPtr)	/* The object containing the command's name.
				 * If the name starts with "::", will be
				 * looked up in global namespace. Else, looked
				 * up first in the current namespace, then in
				 * global namespace. */
{
    register ResolvedCmdName *resPtr;
    register Command *cmdPtr;
    Namespace *refNsPtr;
    int result;

    /*
     * Get the internal representation, converting to a command type if
     * needed. The internal representation is a ResolvedCmdName that points to
     * the actual command.
     *
     * Check the context namespace and the namespace epoch of the resolved
     * symbol to make sure that it is fresh. Note that we verify that the
     * namespace id of the context namespace is the same as the one we cached;
     * this insures that the namespace wasn't deleted and a new one created at
     * the same address with the same command epoch. Note that fully qualified
     * names have a NULL refNsPtr, these checks needn't be made.
     *
     * Check also that the command's epoch is up to date, and that the command
     * is not deleted.
     *
     * If any check fails, then force another conversion to the command type,
     * to discard the old rep and create a new one.      
     */

    resPtr = (ResolvedCmdName *) objPtr->internalRep.twoPtrValue.ptr1;
    if ((objPtr->typePtr != &tclCmdNameType)
	    || (resPtr == NULL)
	    || (cmdPtr = resPtr->cmdPtr, cmdPtr->cmdEpoch != resPtr->cmdEpoch)
	    || (interp != cmdPtr->nsPtr->interp)
	    || (cmdPtr->flags & CMD_IS_DELETED)
	    || ((resPtr->refNsPtr != NULL) && 
		     (((refNsPtr = (Namespace *) TclGetCurrentNamespace(interp))
			     != resPtr->refNsPtr)
		     || (resPtr->refNsId != refNsPtr->nsId)
		     || (resPtr->refNsCmdEpoch != refNsPtr->cmdRefEpoch)))
	) {
	
	result = tclCmdNameType.setFromAnyProc(interp, objPtr);
	
	resPtr = (ResolvedCmdName *) objPtr->internalRep.twoPtrValue.ptr1;
	if ((result == TCL_OK) && resPtr) {
	    cmdPtr = resPtr->cmdPtr;
	} else {
	    cmdPtr = NULL;
	}
    }
    
    return (Tcl_Command) cmdPtr;
}

/*
 *----------------------------------------------------------------------
 *
 * TclSetCmdNameObj --
 *
 *	Modify an object to be an CmdName object that refers to the argument
 *	Command structure.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	The object's old internal rep is freed. It's string rep is not
 *	changed. The refcount in the Command structure is incremented to keep
 *	it from being freed if the command is later deleted until
 *	TclExecuteByteCode has a chance to recognize that it was deleted.
 *
 *----------------------------------------------------------------------
 */

void
TclSetCmdNameObj(
    Tcl_Interp *interp,		/* Points to interpreter containing command
				 * that should be cached in objPtr. */
    register Tcl_Obj *objPtr,	/* Points to Tcl object to be changed to a
				 * CmdName object. */
    Command *cmdPtr)		/* Points to Command structure that the
				 * CmdName object should refer to. */
{
    Interp *iPtr = (Interp *) interp;
    register ResolvedCmdName *resPtr;
    register Namespace *currNsPtr;
    char *name;

    if (objPtr->typePtr == &tclCmdNameType) {
	return;
    }

    cmdPtr->refCount++;
    resPtr = (ResolvedCmdName *) ckalloc(sizeof(ResolvedCmdName));
    resPtr->cmdPtr = cmdPtr;
    resPtr->cmdEpoch = cmdPtr->cmdEpoch;
    resPtr->refCount = 1;

    name = TclGetString(objPtr);
    if ((*name++ == ':') && (*name == ':')) {
	/*
	 * The name is fully qualified: set the referring namespace to
	 * NULL. 
	 */

	resPtr->refNsPtr = NULL;
    } else {
	/*
	 * Get the current namespace.
	 */

	currNsPtr = iPtr->varFramePtr->nsPtr;
	
	resPtr->refNsPtr = currNsPtr;
	resPtr->refNsId = currNsPtr->nsId;
	resPtr->refNsCmdEpoch = currNsPtr->cmdRefEpoch;
    }

    TclFreeIntRep(objPtr);
    objPtr->internalRep.twoPtrValue.ptr1 = (void *) resPtr;
    objPtr->internalRep.twoPtrValue.ptr2 = NULL;
    objPtr->typePtr = &tclCmdNameType;
}

/*
 *----------------------------------------------------------------------
 *
 * FreeCmdNameInternalRep --
 *
 *	Frees the resources associated with a cmdName object's internal
 *	representation.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	Decrements the ref count of any cached ResolvedCmdName structure
 *	pointed to by the cmdName's internal representation. If this is the
 *	last use of the ResolvedCmdName, it is freed. This in turn decrements
 *	the ref count of the Command structure pointed to by the
 *	ResolvedSymbol, which may free the Command structure.
 *
 *----------------------------------------------------------------------
 */

static void
FreeCmdNameInternalRep(
    register Tcl_Obj *objPtr)	/* CmdName object with internal
				 * representation to free. */
{
    register ResolvedCmdName *resPtr =
	(ResolvedCmdName *) objPtr->internalRep.twoPtrValue.ptr1;

    if (resPtr != NULL) {
	/*
	 * Decrement the reference count of the ResolvedCmdName structure. If
	 * there are no more uses, free the ResolvedCmdName structure.
	 */

	resPtr->refCount--;
	if (resPtr->refCount == 0) {
	    /*
	     * Now free the cached command, unless it is still in its hash
	     * table or if there are other references to it from other cmdName
	     * objects.
	     */

	    Command *cmdPtr = resPtr->cmdPtr;
	    TclCleanupCommandMacro(cmdPtr);
	    ckfree((char *) resPtr);
	}
    }
}

/*
 *----------------------------------------------------------------------
 *
 * DupCmdNameInternalRep --
 *
 *	Initialize the internal representation of an cmdName Tcl_Obj to a copy
 *	of the internal representation of an existing cmdName object.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	"copyPtr"s internal rep is set to point to the ResolvedCmdName
 *	structure corresponding to "srcPtr"s internal rep. Increments the ref
 *	count of the ResolvedCmdName structure pointed to by the cmdName's
 *	internal representation.
 *
 *----------------------------------------------------------------------
 */

static void
DupCmdNameInternalRep(
    Tcl_Obj *srcPtr,		/* Object with internal rep to copy. */
    register Tcl_Obj *copyPtr)	/* Object with internal rep to set. */
{
    register ResolvedCmdName *resPtr = (ResolvedCmdName *)
	    srcPtr->internalRep.twoPtrValue.ptr1;

    copyPtr->internalRep.twoPtrValue.ptr1 = (void *) resPtr;
    copyPtr->internalRep.twoPtrValue.ptr2 = NULL;
    if (resPtr != NULL) {
	resPtr->refCount++;
    }
    copyPtr->typePtr = &tclCmdNameType;
}

/*
 *----------------------------------------------------------------------
 *
 * SetCmdNameFromAny --
 *
 *	Generate an cmdName internal form for the Tcl object "objPtr".
 *
 * Results:
 *	The return value is a standard Tcl result. The conversion always
 *	succeeds and TCL_OK is returned.
 *
 * Side effects:
 *	A pointer to a ResolvedCmdName structure that holds a cached pointer
 *	to the command with a name that matches objPtr's string rep is stored
 *	as objPtr's internal representation. This ResolvedCmdName pointer will
 *	be NULL if no matching command was found. The ref count of the cached
 *	Command's structure (if any) is also incremented.
 *
 *----------------------------------------------------------------------
 */

static int
SetCmdNameFromAny(
    Tcl_Interp *interp,		/* Used for error reporting if not NULL. */
    register Tcl_Obj *objPtr)	/* The object to convert. */
{
    Interp *iPtr = (Interp *) interp;
    char *name;
    register Command *cmdPtr;
    Namespace *currNsPtr;
    register ResolvedCmdName *resPtr;

    /*
     * Find the Command structure, if any, that describes the command called
     * "name". Build a ResolvedCmdName that holds a cached pointer to this
     * Command, and bump the reference count in the referenced Command
     * structure. A Command structure will not be deleted as long as it is
     * referenced from a CmdName object.
     */

    name = TclGetString(objPtr);
    cmdPtr = (Command *) Tcl_FindCommand(interp, name, /*ns*/ NULL, /*flags*/ 0);

    /*
     * Free the old internalRep before setting the new one. Do this after
     * getting the string rep to allow the conversion code (in particular,
     * Tcl_GetStringFromObj) to use that old internalRep.
     */

    if (cmdPtr) {
	cmdPtr->refCount++;
	resPtr = (ResolvedCmdName *) objPtr->internalRep.otherValuePtr;
	if ((objPtr->typePtr == &tclCmdNameType)
		&& resPtr && (resPtr->refCount == 1)) {
	    /*
	     * Reuse the old ResolvedCmdName struct instead of freeing it
	     */
	    
	    Command *oldCmdPtr = resPtr->cmdPtr;
	    if (--oldCmdPtr->refCount == 0) {
		TclCleanupCommandMacro(oldCmdPtr);
	    }
	} else {
	    TclFreeIntRep(objPtr);
	    resPtr = (ResolvedCmdName *) ckalloc(sizeof(ResolvedCmdName));
	    resPtr->refCount = 1;
	    objPtr->internalRep.twoPtrValue.ptr1 = (void *) resPtr;
	    objPtr->internalRep.twoPtrValue.ptr2 = NULL;
	    objPtr->typePtr = &tclCmdNameType;
	}
	resPtr->cmdPtr = cmdPtr;
	resPtr->cmdEpoch = cmdPtr->cmdEpoch;
	if ((*name++ == ':') && (*name == ':')) {
	    /*
	     * The name is fully qualified: set the referring namespace to 
	     * NULL. 
	     */

	    resPtr->refNsPtr = NULL;
	} else {
	    /*
	     * Get the current namespace.
	     */

	    currNsPtr = iPtr->varFramePtr->nsPtr;
	    
	    resPtr->refNsPtr = currNsPtr;
	    resPtr->refNsId = currNsPtr->nsId;
	    resPtr->refNsCmdEpoch = currNsPtr->cmdRefEpoch;
	}
    } else {
	TclFreeIntRep(objPtr);
	objPtr->internalRep.twoPtrValue.ptr1 = NULL;
	objPtr->internalRep.twoPtrValue.ptr2 = NULL;
	objPtr->typePtr = &tclCmdNameType;
    }
    return TCL_OK;
}

/*
 * Local Variables:
 * mode: c
 * c-basic-offset: 4
 * fill-column: 78
 * End:
 */
