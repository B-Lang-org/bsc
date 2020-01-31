/*
 * tclDictObj.c --
 *
 *	This file contains functions that implement the Tcl dict object type
 *	and its accessor command.
 *
 * Copyright (c) 2002 by Donal K. Fellows.
 *
 * See the file "license.terms" for information on usage and redistribution of
 * this file, and for a DISCLAIMER OF ALL WARRANTIES.
 *
 * RCS: @(#) $Id: tclDictObj.c,v 1.56.2.1 2008/07/20 22:02:37 dkf Exp $
 */

#include "tclInt.h"
#include "tommath.h"

/*
 * Forward declaration.
 */
struct Dict;

/*
 * Prototypes for functions defined later in this file:
 */

static void		DeleteDict(struct Dict *dict);
static int		DictAppendCmd(ClientData dummy, Tcl_Interp *interp,
			    int objc, Tcl_Obj *const *objv);
static int		DictCreateCmd(ClientData dummy, Tcl_Interp *interp,
			    int objc, Tcl_Obj *const *objv);
static int		DictExistsCmd(ClientData dummy, Tcl_Interp *interp,
			    int objc, Tcl_Obj *const *objv);
static int		DictFilterCmd(ClientData dummy, Tcl_Interp *interp,
			    int objc, Tcl_Obj *const *objv);
static int		DictForCmd(ClientData dummy, Tcl_Interp *interp,
			    int objc, Tcl_Obj *const *objv);
static int		DictGetCmd(ClientData dummy, Tcl_Interp *interp,
			    int objc, Tcl_Obj *const *objv);
static int		DictIncrCmd(ClientData dummy, Tcl_Interp *interp,
			    int objc, Tcl_Obj *const *objv);
static int		DictInfoCmd(ClientData dummy, Tcl_Interp *interp,
			    int objc, Tcl_Obj *const *objv);
static int		DictKeysCmd(ClientData dummy, Tcl_Interp *interp,
			    int objc, Tcl_Obj *const *objv);
static int		DictLappendCmd(ClientData dummy, Tcl_Interp *interp,
			    int objc, Tcl_Obj *const *objv);
static int		DictMergeCmd(ClientData dummy, Tcl_Interp *interp,
			    int objc, Tcl_Obj *const *objv);
static int		DictRemoveCmd(ClientData dummy, Tcl_Interp *interp,
			    int objc, Tcl_Obj *const *objv);
static int		DictReplaceCmd(ClientData dummy, Tcl_Interp *interp,
			    int objc, Tcl_Obj *const *objv);
static int		DictSetCmd(ClientData dummy, Tcl_Interp *interp,
			    int objc, Tcl_Obj *const *objv);
static int		DictSizeCmd(ClientData dummy, Tcl_Interp *interp,
			    int objc, Tcl_Obj *const *objv);
static int		DictUnsetCmd(ClientData dummy, Tcl_Interp *interp,
			    int objc, Tcl_Obj *const *objv);
static int		DictUpdateCmd(ClientData dummy, Tcl_Interp *interp,
			    int objc, Tcl_Obj *const *objv);
static int		DictValuesCmd(ClientData dummy, Tcl_Interp *interp,
			    int objc, Tcl_Obj *const *objv);
static int		DictWithCmd(ClientData dummy, Tcl_Interp *interp,
			    int objc, Tcl_Obj *const *objv);
static void		DupDictInternalRep(Tcl_Obj *srcPtr, Tcl_Obj *copyPtr);
static void		FreeDictInternalRep(Tcl_Obj *dictPtr);
static void		InvalidateDictChain(Tcl_Obj *dictObj);
static int		SetDictFromAny(Tcl_Interp *interp, Tcl_Obj *objPtr);
static void		UpdateStringOfDict(Tcl_Obj *dictPtr);
static Tcl_HashEntry *	AllocChainEntry(Tcl_HashTable *tablePtr,void *keyPtr);
static inline void	InitChainTable(struct Dict *dict);
static inline void	DeleteChainTable(struct Dict *dict);
static inline Tcl_HashEntry *CreateChainEntry(struct Dict *dict,
			    Tcl_Obj *keyPtr, int *newPtr);
static inline int	DeleteChainEntry(struct Dict *dict, Tcl_Obj *keyPtr);

/*
 * Table of dict subcommand names and implementations.
 */

static const EnsembleImplMap implementationMap[] = {
    {"append",	DictAppendCmd,	TclCompileDictAppendCmd },
    {"create",	DictCreateCmd,	NULL },
    {"exists",	DictExistsCmd,	NULL },
    {"filter",	DictFilterCmd,	NULL },
    {"for",	DictForCmd,	TclCompileDictForCmd },
    {"get",	DictGetCmd,	TclCompileDictGetCmd },
    {"incr",	DictIncrCmd,	TclCompileDictIncrCmd },
    {"info",	DictInfoCmd,	NULL },
    {"keys",	DictKeysCmd,	NULL },
    {"lappend",	DictLappendCmd,	TclCompileDictLappendCmd },
    {"merge",	DictMergeCmd,	NULL },
    {"remove",	DictRemoveCmd,	NULL },
    {"replace",	DictReplaceCmd,	NULL },
    {"set",	DictSetCmd,	TclCompileDictSetCmd },
    {"size",	DictSizeCmd,	NULL },
    {"unset",	DictUnsetCmd,	NULL },
    {"update",	DictUpdateCmd,	TclCompileDictUpdateCmd },
    {"values",	DictValuesCmd,	NULL },
    {"with",	DictWithCmd,	NULL },
    {NULL}
};

/*
 * Internal representation of the entries in the hash table that backs a
 * dictionary.
 */

typedef struct ChainEntry {
    Tcl_HashEntry entry;
    struct ChainEntry *prevPtr;
    struct ChainEntry *nextPtr;
} ChainEntry;

/*
 * Internal representation of a dictionary.
 *
 * The internal representation of a dictionary object is a hash table (with
 * Tcl_Objs for both keys and values), a reference count and epoch number for
 * detecting concurrent modifications of the dictionary, and a pointer to the
 * parent object (used when invalidating string reps of pathed dictionary
 * trees) which is NULL in normal use. The fact that hash tables know (with
 * appropriate initialisation) already about objects makes key management /so/
 * much easier!
 *
 * Reference counts are used to enable safe iteration across hashes while
 * allowing the type of the containing object to be modified.
 */

typedef struct Dict {
    Tcl_HashTable table;	/* Object hash table to store mapping in. */
    ChainEntry *entryChainHead;	/* Linked list of all entries in the
				 * dictionary. Used for doing traversal of the
				 * entries in the order that they are
				 * created. */
    ChainEntry *entryChainTail;	/* Other end of linked list of all entries in
				 * the dictionary. Used for doing traversal of
				 * the entries in the order that they are
				 * created. */
    int epoch;			/* Epoch counter */
    int refcount;		/* Reference counter (see above) */
    Tcl_Obj *chain;		/* Linked list used for invalidating the
				 * string representations of updated nested
				 * dictionaries. */
} Dict;

/*
 * The structure below defines the dictionary object type by means of
 * functions that can be invoked by generic object code.
 */

Tcl_ObjType tclDictType = {
    "dict",
    FreeDictInternalRep,		/* freeIntRepProc */
    DupDictInternalRep,		        /* dupIntRepProc */
    UpdateStringOfDict,			/* updateStringProc */
    SetDictFromAny			/* setFromAnyProc */
};

/*
 * The type of the specially adapted version of the Tcl_Obj*-containing hash
 * table defined in the tclObj.c code. This version differs in that it
 * allocates a bit more space in each hash entry in order to hold the pointers
 * used to keep the hash entries in a linked list.
 *
 * Note that this type of hash table is *only* suitable for direct use in
 * *this* file. Everything else should use the dict iterator API.
 */

static Tcl_HashKeyType chainHashType = {
    TCL_HASH_KEY_TYPE_VERSION,
    0,
    TclHashObjKey,
    TclCompareObjKeys,
    AllocChainEntry,
    TclFreeObjEntry
};

/***** START OF FUNCTIONS IMPLEMENTING DICT CORE API *****/

/*
 *----------------------------------------------------------------------
 *
 * AllocChainEntry --
 *
 *	Allocate space for a Tcl_HashEntry containing the Tcl_Obj * key, and
 *	which has a bit of extra space afterwards for storing pointers to the
 *	rest of the chain of entries (the extra pointers are left NULL).
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
AllocChainEntry(
    Tcl_HashTable *tablePtr,
    void *keyPtr)
{
    Tcl_Obj *objPtr = keyPtr;
    ChainEntry *cPtr;

    cPtr = (ChainEntry *) ckalloc(sizeof(ChainEntry));
    cPtr->entry.key.oneWordValue = (char *) objPtr;
    Tcl_IncrRefCount(objPtr);
    cPtr->entry.clientData = NULL;
    cPtr->prevPtr = cPtr->nextPtr = NULL;

    return &cPtr->entry;
}

/*
 * Helper functions that disguise most of the details relating to how the
 * linked list of hash entries is managed. In particular, these manage the
 * creation of the table and initializing of the chain, the deletion of the
 * table and chain, the adding of an entry to the chain, and the removal of an
 * entry from the chain.
 */

static inline void
InitChainTable(
    Dict *dict)
{
    Tcl_InitCustomHashTable(&dict->table, TCL_CUSTOM_PTR_KEYS,
	    &chainHashType);
    dict->entryChainHead = dict->entryChainTail = NULL;
}

static inline void
DeleteChainTable(
    Dict *dict)
{
    ChainEntry *cPtr;

    for (cPtr=dict->entryChainHead ; cPtr!=NULL ; cPtr=cPtr->nextPtr) {
	Tcl_Obj *valuePtr = Tcl_GetHashValue(&cPtr->entry);

	TclDecrRefCount(valuePtr);
    }
    Tcl_DeleteHashTable(&dict->table);
}

static inline Tcl_HashEntry *
CreateChainEntry(
    Dict *dict,
    Tcl_Obj *keyPtr,
    int *newPtr)
{
    ChainEntry *cPtr = (ChainEntry *)
	    Tcl_CreateHashEntry(&dict->table, (char *) keyPtr, newPtr);

    /*
     * If this is a new entry in the hash table, stitch it into the chain.
     */

    if (*newPtr) {
	cPtr->nextPtr = NULL;
	if (dict->entryChainHead == NULL) {
	    cPtr->prevPtr = NULL;
	    dict->entryChainHead = cPtr;
	    dict->entryChainTail = cPtr;
	} else {
	    cPtr->prevPtr = dict->entryChainTail;
	    dict->entryChainTail->nextPtr = cPtr;
	    dict->entryChainTail = cPtr;
	}
    }

    return &cPtr->entry;
}

static inline int
DeleteChainEntry(
    Dict *dict,
    Tcl_Obj *keyPtr)
{
    ChainEntry *cPtr = (ChainEntry *)
	    Tcl_FindHashEntry(&dict->table, (char *) keyPtr);

    if (cPtr == NULL) {
	return 0;
    } else {
	Tcl_Obj *valuePtr = Tcl_GetHashValue(&cPtr->entry);
	TclDecrRefCount(valuePtr);
    }

    /*
     * Unstitch from the chain.
     */

    if (cPtr->nextPtr) {
	cPtr->nextPtr->prevPtr = cPtr->prevPtr;
    } else {
	dict->entryChainTail = cPtr->prevPtr;
    }
    if (cPtr->prevPtr) {
	cPtr->prevPtr->nextPtr = cPtr->nextPtr;
    } else {
	dict->entryChainHead = cPtr->nextPtr;
    }

    Tcl_DeleteHashEntry(&cPtr->entry);
    return 1;
}

/*
 *----------------------------------------------------------------------
 *
 * DupDictInternalRep --
 *
 *	Initialize the internal representation of a dictionary Tcl_Obj to a
 *	copy of the internal representation of an existing dictionary object.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	"srcPtr"s dictionary internal rep pointer should not be NULL and we
 *	assume it is not NULL. We set "copyPtr"s internal rep to a pointer to
 *	a newly allocated dictionary rep that, in turn, points to "srcPtr"s
 *	key and value objects. Those objects are not actually copied but are
 *	shared between "srcPtr" and "copyPtr". The ref count of each key and
 *	value object is incremented.
 *
 *----------------------------------------------------------------------
 */

static void
DupDictInternalRep(
    Tcl_Obj *srcPtr,
    Tcl_Obj *copyPtr)
{
    Dict *oldDict = srcPtr->internalRep.otherValuePtr;
    Dict *newDict = (Dict *) ckalloc(sizeof(Dict));
    ChainEntry *cPtr;

    /*
     * Copy values across from the old hash table.
     */

    InitChainTable(newDict);
    for (cPtr=oldDict->entryChainHead ; cPtr!=NULL ; cPtr=cPtr->nextPtr) {
	void *key = Tcl_GetHashKey(&oldDict->table, &cPtr->entry);
	Tcl_Obj *valuePtr = Tcl_GetHashValue(&cPtr->entry);
	int n;
	Tcl_HashEntry *hPtr = CreateChainEntry(newDict, key, &n);

	/*
	 * Fill in the contents.
	 */

	Tcl_SetHashValue(hPtr, (ClientData) valuePtr);
	Tcl_IncrRefCount(valuePtr);
    }

    /*
     * Initialise other fields.
     */

    newDict->epoch = 0;
    newDict->chain = NULL;
    newDict->refcount = 1;

    /*
     * Store in the object.
     */

    copyPtr->internalRep.otherValuePtr = newDict;
    copyPtr->typePtr = &tclDictType;
}

/*
 *----------------------------------------------------------------------
 *
 * FreeDictInternalRep --
 *
 *	Deallocate the storage associated with a dictionary object's internal
 *	representation.
 *
 * Results:
 *	None
 *
 * Side effects:
 *	Frees the memory holding the dictionary's internal hash table unless
 *	it is locked by an iteration going over it.
 *
 *----------------------------------------------------------------------
 */

static void
FreeDictInternalRep(
    Tcl_Obj *dictPtr)
{
    Dict *dict = dictPtr->internalRep.otherValuePtr;

    --dict->refcount;
    if (dict->refcount <= 0) {
	DeleteDict(dict);
    }

    dictPtr->internalRep.otherValuePtr = NULL;	/* Belt and braces! */
}

/*
 *----------------------------------------------------------------------
 *
 * DeleteDict --
 *
 *	Delete the structure that is used to implement a dictionary's internal
 *	representation. Called when either the dictionary object loses its
 *	internal representation or when the last iteration over the dictionary
 *	completes.
 *
 * Results:
 *	None
 *
 * Side effects:
 *	Decrements the reference count of all key and value objects in the
 *	dictionary, which may free them.
 *
 *----------------------------------------------------------------------
 */

static void
DeleteDict(
    Dict *dict)
{
    DeleteChainTable(dict);
    ckfree((char *) dict);
}

/*
 *----------------------------------------------------------------------
 *
 * UpdateStringOfDict --
 *
 *	Update the string representation for a dictionary object. Note: This
 *	function does not invalidate an existing old string rep so storage
 *	will be lost if this has not already been done. This code is based on
 *	UpdateStringOfList in tclListObj.c
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	The object's string is set to a valid string that results from the
 *	dict-to-string conversion. This string will be empty if the dictionary
 *	has no key/value pairs. The dictionary internal representation should
 *	not be NULL and we assume it is not NULL.
 *
 *----------------------------------------------------------------------
 */

static void
UpdateStringOfDict(
    Tcl_Obj *dictPtr)
{
#define LOCAL_SIZE 20
    int localFlags[LOCAL_SIZE], *flagPtr;
    Dict *dict = dictPtr->internalRep.otherValuePtr;
    ChainEntry *cPtr;
    Tcl_Obj *keyPtr, *valuePtr;
    int numElems, i, length;
    char *elem, *dst;

    /*
     * This field is the most useful one in the whole hash structure, and it
     * is not exposed by any API function...
     */

    numElems = dict->table.numEntries * 2;

    /*
     * Pass 1: estimate space, gather flags.
     */

    if (numElems <= LOCAL_SIZE) {
	flagPtr = localFlags;
    } else {
	flagPtr = (int *) ckalloc((unsigned) numElems*sizeof(int));
    }
    dictPtr->length = 1;
    for (i=0,cPtr=dict->entryChainHead; i<numElems; i+=2,cPtr=cPtr->nextPtr) {
	/*
	 * Assume that cPtr is never NULL since we know the number of array
	 * elements already.
	 */

	keyPtr = (Tcl_Obj *) Tcl_GetHashKey(&dict->table, &cPtr->entry);
	elem = TclGetStringFromObj(keyPtr, &length);
	dictPtr->length += Tcl_ScanCountedElement(elem, length,
		&flagPtr[i]) + 1;

	valuePtr = Tcl_GetHashValue(&cPtr->entry);
	elem = TclGetStringFromObj(valuePtr, &length);
	dictPtr->length += Tcl_ScanCountedElement(elem, length,
		&flagPtr[i+1]) + 1;
    }

    /*
     * Pass 2: copy into string rep buffer.
     */

    dictPtr->bytes = ckalloc((unsigned) dictPtr->length);
    dst = dictPtr->bytes;
    for (i=0,cPtr=dict->entryChainHead; i<numElems; i+=2,cPtr=cPtr->nextPtr) {
	keyPtr = (Tcl_Obj *) Tcl_GetHashKey(&dict->table, &cPtr->entry);
	elem = TclGetStringFromObj(keyPtr, &length);
	dst += Tcl_ConvertCountedElement(elem, length, dst,
		flagPtr[i] | (i==0 ? 0 : TCL_DONT_QUOTE_HASH));
	*(dst++) = ' ';

	valuePtr = Tcl_GetHashValue(&cPtr->entry);
	elem = TclGetStringFromObj(valuePtr, &length);
	dst += Tcl_ConvertCountedElement(elem, length, dst,
		flagPtr[i+1] | TCL_DONT_QUOTE_HASH);
	*(dst++) = ' ';
    }
    if (flagPtr != localFlags) {
	ckfree((char *) flagPtr);
    }
    if (dst == dictPtr->bytes) {
	*dst = 0;
    } else {
	*(--dst) = 0;
    }
    dictPtr->length = dst - dictPtr->bytes;
}

/*
 *----------------------------------------------------------------------
 *
 * SetDictFromAny --
 *
 *	Convert a non-dictionary object into a dictionary object. This code is
 *	very closely related to SetListFromAny in tclListObj.c but does not
 *	actually guarantee that a dictionary object will have a string rep (as
 *	conversions from lists are handled with a special case.)
 *
 * Results:
 *	A standard Tcl result.
 *
 * Side effects:
 *	If the string can be converted, it loses any old internal
 *	representation that it had and gains a dictionary's internalRep.
 *
 *----------------------------------------------------------------------
 */

static int
SetDictFromAny(
    Tcl_Interp *interp,
    Tcl_Obj *objPtr)
{
    char *string, *s;
    const char *elemStart, *nextElem;
    int lenRemain, length, elemSize, hasBrace, result, isNew;
    char *limit;		/* Points just after string's last byte. */
    register const char *p;
    register Tcl_Obj *keyPtr, *valuePtr;
    Dict *dict;
    Tcl_HashEntry *hPtr;

    /*
     * Since lists and dictionaries have very closely-related string
     * representations (i.e. the same parsing code) we can safely special-case
     * the conversion from lists to dictionaries.
     */

    if (objPtr->typePtr == &tclListType) {
	int objc, i;
	Tcl_Obj **objv;

	if (TclListObjGetElements(interp, objPtr, &objc, &objv) != TCL_OK) {
	    return TCL_ERROR;
	}
	if (objc & 1) {
	    if (interp != NULL) {
		Tcl_SetResult(interp, "missing value to go with key",
			TCL_STATIC);
	    }
	    return TCL_ERROR;
	}

	/*
	 * Build the hash of key/value pairs.
	 */

	dict = (Dict *) ckalloc(sizeof(Dict));
	InitChainTable(dict);
	for (i=0 ; i<objc ; i+=2) {
	    /*
	     * Store key and value in the hash table we're building.
	     */

	    hPtr = CreateChainEntry(dict, objv[i], &isNew);
	    if (!isNew) {
		Tcl_Obj *discardedValue = Tcl_GetHashValue(hPtr);

		TclDecrRefCount(discardedValue);
	    }
	    Tcl_SetHashValue(hPtr, objv[i+1]);
	    Tcl_IncrRefCount(objv[i+1]); /* Since hash now holds ref to it */
	}

	/*
	 * Share type-setting code with the string-conversion case.
	 */

	goto installHash;
    }

    /*
     * Get the string representation. Make it up-to-date if necessary.
     */

    string = TclGetStringFromObj(objPtr, &length);
    limit = (string + length);

    /*
     * Allocate a new HashTable that has objects for keys and objects for
     * values.
     */

    dict = (Dict *) ckalloc(sizeof(Dict));
    InitChainTable(dict);
    for (p = string, lenRemain = length;
	    lenRemain > 0;
	    p = nextElem, lenRemain = (limit - nextElem)) {
	result = TclFindElement(interp, p, lenRemain,
		&elemStart, &nextElem, &elemSize, &hasBrace);
	if (result != TCL_OK) {
	    goto errorExit;
	}
	if (elemStart >= limit) {
	    break;
	}

	/*
	 * Allocate a Tcl object for the element and initialize it from the
	 * "elemSize" bytes starting at "elemStart".
	 */

	s = ckalloc((unsigned) elemSize + 1);
	if (hasBrace) {
	    memcpy(s, elemStart, (size_t) elemSize);
	    s[elemSize] = 0;
	} else {
	    elemSize = TclCopyAndCollapse(elemSize, elemStart, s);
	}

	TclNewObj(keyPtr);
        keyPtr->bytes = s;
        keyPtr->length = elemSize;

	p = nextElem;
	lenRemain = (limit - nextElem);
	if (lenRemain <= 0) {
	    goto missingKey;
	}

	result = TclFindElement(interp, p, lenRemain,
		&elemStart, &nextElem, &elemSize, &hasBrace);
	if (result != TCL_OK) {
	    TclDecrRefCount(keyPtr);
	    goto errorExit;
	}
	if (elemStart >= limit) {
	    goto missingKey;
	}

	/*
	 * Allocate a Tcl object for the element and initialize it from the
	 * "elemSize" bytes starting at "elemStart".
	 */

	s = ckalloc((unsigned) elemSize + 1);
	if (hasBrace) {
	    memcpy((void *) s, (void *) elemStart, (size_t) elemSize);
	    s[elemSize] = 0;
	} else {
	    elemSize = TclCopyAndCollapse(elemSize, elemStart, s);
	}

	TclNewObj(valuePtr);
        valuePtr->bytes = s;
        valuePtr->length = elemSize;

	/*
	 * Store key and value in the hash table we're building.
	 */

	hPtr = CreateChainEntry(dict, keyPtr, &isNew);
	if (!isNew) {
	    Tcl_Obj *discardedValue = Tcl_GetHashValue(hPtr);

	    TclDecrRefCount(keyPtr);
	    TclDecrRefCount(discardedValue);
	}
	Tcl_SetHashValue(hPtr, valuePtr);
	Tcl_IncrRefCount(valuePtr); /* since hash now holds ref to it */
    }

  installHash:
    /*
     * Free the old internalRep before setting the new one. We do this as late
     * as possible to allow the conversion code, in particular
     * Tcl_GetStringFromObj, to use that old internalRep.
     */

    TclFreeIntRep(objPtr);
    dict->epoch = 0;
    dict->chain = NULL;
    dict->refcount = 1;
    objPtr->internalRep.otherValuePtr = dict;
    objPtr->typePtr = &tclDictType;
    return TCL_OK;

  missingKey:
    if (interp != NULL) {
	Tcl_SetResult(interp, "missing value to go with key", TCL_STATIC);
    }
    TclDecrRefCount(keyPtr);
    result = TCL_ERROR;

  errorExit:
    DeleteChainTable(dict);
    ckfree((char *) dict);
    return result;
}

/*
 *----------------------------------------------------------------------
 *
 * TclTraceDictPath --
 *
 *	Trace through a tree of dictionaries using the array of keys given. If
 *	the flags argument has the DICT_PATH_UPDATE flag is set, a
 *	backward-pointing chain of dictionaries is also built (in the Dict's
 *	chain field) and the chained dictionaries are made into unshared
 *	dictionaries (if they aren't already.)
 *
 * Results:
 *	The object at the end of the path, or NULL if there was an error. Note
 *	that this it is an error for an intermediate dictionary on the path to
 *	not exist. If the flags argument has the DICT_PATH_EXISTS set, a
 *	non-existent path gives a DICT_PATH_NON_EXISTENT result.
 *
 * Side effects:
 *	If the flags argument is zero or DICT_PATH_EXISTS, there are no side
 *	effects (other than potential conversion of objects to dictionaries.)
 *	If the flags argument is DICT_PATH_UPDATE, the following additional
 *	side effects occur. Shared dictionaries along the path are converted
 *	into unshared objects, and a backward-pointing chain is built using
 *	the chain fields of the dictionaries (for easy invalidation of string
 *	representations using InvalidateDictChain). If the flags argument has
 *	the DICT_PATH_CREATE bits set (and not the DICT_PATH_EXISTS bit),
 *	non-existant keys will be inserted with a value of an empty
 *	dictionary, resulting in the path being built.
 *
 *----------------------------------------------------------------------
 */

Tcl_Obj *
TclTraceDictPath(
    Tcl_Interp *interp,
    Tcl_Obj *dictPtr,
    int keyc,
    Tcl_Obj *const keyv[],
    int flags)
{
    Dict *dict, *newDict;
    int i;

    if (dictPtr->typePtr != &tclDictType) {
	if (SetDictFromAny(interp, dictPtr) != TCL_OK) {
	    return NULL;
	}
    }
    dict = dictPtr->internalRep.otherValuePtr;
    if (flags & DICT_PATH_UPDATE) {
	dict->chain = NULL;
    }

    for (i=0 ; i<keyc ; i++) {
	Tcl_HashEntry *hPtr = Tcl_FindHashEntry(&dict->table, (char *)keyv[i]);
	Tcl_Obj *tmpObj;

	if (hPtr == NULL) {
	    int isNew;			/* Dummy */

	    if (flags & DICT_PATH_EXISTS) {
		return DICT_PATH_NON_EXISTENT;
	    }
	    if ((flags & DICT_PATH_CREATE) != DICT_PATH_CREATE) {
		if (interp != NULL) {
		    Tcl_ResetResult(interp);
		    Tcl_AppendResult(interp, "key \"", TclGetString(keyv[i]),
			    "\" not known in dictionary", NULL);
		    Tcl_SetErrorCode(interp, "TCL", "LOOKUP", "DICT",
			    TclGetString(keyv[i]), NULL);
		}
		return NULL;
	    }

	    /*
	     * The next line should always set isNew to 1.
	     */

	    hPtr = CreateChainEntry(dict, keyv[i], &isNew);
	    tmpObj = Tcl_NewDictObj();
	    Tcl_IncrRefCount(tmpObj);
	    Tcl_SetHashValue(hPtr, tmpObj);
	} else {
	    tmpObj = Tcl_GetHashValue(hPtr);
	    if (tmpObj->typePtr != &tclDictType) {
		if (SetDictFromAny(interp, tmpObj) != TCL_OK) {
		    return NULL;
		}
	    }
	}

	newDict = tmpObj->internalRep.otherValuePtr;
	if (flags & DICT_PATH_UPDATE) {
	    if (Tcl_IsShared(tmpObj)) {
		TclDecrRefCount(tmpObj);
		tmpObj = Tcl_DuplicateObj(tmpObj);
		Tcl_IncrRefCount(tmpObj);
		Tcl_SetHashValue(hPtr, (ClientData) tmpObj);
		dict->epoch++;
		newDict = tmpObj->internalRep.otherValuePtr;
	    }

	    newDict->chain = dictPtr;
	}
	dict = newDict;
	dictPtr = tmpObj;
    }
    return dictPtr;
}

/*
 *----------------------------------------------------------------------
 *
 * InvalidateDictChain --
 *
 *	Go through a dictionary chain (built by an updating invokation of
 *	TclTraceDictPath) and invalidate the string representations of all the
 *	dictionaries on the chain.
 *
 * Results:
 *	None
 *
 * Side effects:
 *	String reps are invalidated and epoch counters (for detecting illegal
 *	concurrent modifications) are updated through the chain of updated
 *	dictionaries.
 *
 *----------------------------------------------------------------------
 */

static void
InvalidateDictChain(
    Tcl_Obj *dictObj)
{
    Dict *dict = dictObj->internalRep.otherValuePtr;

    do {
	Tcl_InvalidateStringRep(dictObj);
	dict->epoch++;
	dictObj = dict->chain;
	if (dictObj == NULL) {
	    break;
	}
	dict->chain = NULL;
	dict = dictObj->internalRep.otherValuePtr;
    } while (dict != NULL);
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_DictObjPut --
 *
 *	Add a key,value pair to a dictionary, or update the value for a key if
 *	that key already has a mapping in the dictionary.
 *
 * Results:
 *	A standard Tcl result.
 *
 * Side effects:
 *	The object pointed to by dictPtr is converted to a dictionary if it is
 *	not already one, and any string representation that it has is
 *	invalidated.
 *
 *----------------------------------------------------------------------
 */

int
Tcl_DictObjPut(
    Tcl_Interp *interp,
    Tcl_Obj *dictPtr,
    Tcl_Obj *keyPtr,
    Tcl_Obj *valuePtr)
{
    Dict *dict;
    Tcl_HashEntry *hPtr;
    int isNew;

    if (Tcl_IsShared(dictPtr)) {
	Tcl_Panic("%s called with shared object", "Tcl_DictObjPut");
    }

    if (dictPtr->typePtr != &tclDictType) {
	int result = SetDictFromAny(interp, dictPtr);

	if (result != TCL_OK) {
	    return result;
	}
    }

    if (dictPtr->bytes != NULL) {
	Tcl_InvalidateStringRep(dictPtr);
    }
    dict = dictPtr->internalRep.otherValuePtr;
    hPtr = CreateChainEntry(dict, keyPtr, &isNew);
    Tcl_IncrRefCount(valuePtr);
    if (!isNew) {
	Tcl_Obj *oldValuePtr = Tcl_GetHashValue(hPtr);

	TclDecrRefCount(oldValuePtr);
    }
    Tcl_SetHashValue(hPtr, valuePtr);
    dict->epoch++;
    return TCL_OK;
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_DictObjGet --
 *
 *	Given a key, get its value from the dictionary (or NULL if key is not
 *	found in dictionary.)
 *
 * Results:
 *	A standard Tcl result. The variable pointed to by valuePtrPtr is
 *	updated with the value for the key. Note that it is not an error for
 *	the key to have no mapping in the dictionary.
 *
 * Side effects:
 *	The object pointed to by dictPtr is converted to a dictionary if it is
 *	not already one.
 *
 *----------------------------------------------------------------------
 */

int
Tcl_DictObjGet(
    Tcl_Interp *interp,
    Tcl_Obj *dictPtr,
    Tcl_Obj *keyPtr,
    Tcl_Obj **valuePtrPtr)
{
    Dict *dict;
    Tcl_HashEntry *hPtr;

    if (dictPtr->typePtr != &tclDictType) {
	int result = SetDictFromAny(interp, dictPtr);
	if (result != TCL_OK) {
	    return result;
	}
    }

    dict = dictPtr->internalRep.otherValuePtr;
    hPtr = Tcl_FindHashEntry(&dict->table, (char *) keyPtr);
    if (hPtr == NULL) {
	*valuePtrPtr = NULL;
    } else {
	*valuePtrPtr = Tcl_GetHashValue(hPtr);
    }
    return TCL_OK;
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_DictObjRemove --
 *
 *	Remove the key,value pair with the given key from the dictionary; the
 *	key does not need to be present in the dictionary.
 *
 * Results:
 *	A standard Tcl result.
 *
 * Side effects:
 *	The object pointed to by dictPtr is converted to a dictionary if it is
 *	not already one, and any string representation that it has is
 *	invalidated.
 *
 *----------------------------------------------------------------------
 */

int
Tcl_DictObjRemove(
    Tcl_Interp *interp,
    Tcl_Obj *dictPtr,
    Tcl_Obj *keyPtr)
{
    Dict *dict;

    if (Tcl_IsShared(dictPtr)) {
	Tcl_Panic("%s called with shared object", "Tcl_DictObjRemove");
    }

    if (dictPtr->typePtr != &tclDictType) {
	int result = SetDictFromAny(interp, dictPtr);
	if (result != TCL_OK) {
	    return result;
	}
    }

    if (dictPtr->bytes != NULL) {
	Tcl_InvalidateStringRep(dictPtr);
    }
    dict = dictPtr->internalRep.otherValuePtr;
    if (DeleteChainEntry(dict, keyPtr)) {
	dict->epoch++;
    }
    return TCL_OK;
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_DictObjSize --
 *
 *	How many key,value pairs are there in the dictionary?
 *
 * Results:
 *	A standard Tcl result. Updates the variable pointed to by sizePtr with
 *	the number of key,value pairs in the dictionary.
 *
 * Side effects:
 *	The dictPtr object is converted to a dictionary type if it is not a
 *	dictionary already.
 *
 *----------------------------------------------------------------------
 */

int
Tcl_DictObjSize(
    Tcl_Interp *interp,
    Tcl_Obj *dictPtr,
    int *sizePtr)
{
    Dict *dict;

    if (dictPtr->typePtr != &tclDictType) {
	int result = SetDictFromAny(interp, dictPtr);
	if (result != TCL_OK) {
	    return result;
	}
    }

    dict = dictPtr->internalRep.otherValuePtr;
    *sizePtr = dict->table.numEntries;
    return TCL_OK;
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_DictObjFirst --
 *
 *	Start a traversal of the dictionary. Caller must supply the search
 *	context, pointers for returning key and value, and a pointer to allow
 *	indication of whether the dictionary has been traversed (i.e. the
 *	dictionary is empty). The order of traversal is undefined.
 *
 * Results:
 *	A standard Tcl result. Updates the variables pointed to by keyPtrPtr,
 *	valuePtrPtr and donePtr. Either of keyPtrPtr and valuePtrPtr may be
 *	NULL, in which case the key/value is not made available to the caller.
 *
 * Side effects:
 *	The dictPtr object is converted to a dictionary type if it is not a
 *	dictionary already. The search context is initialised if the search
 *	has not finished. The dictionary's internal rep is Tcl_Preserve()d if
 *	the dictionary has at least one element.
 *
 *----------------------------------------------------------------------
 */

int
Tcl_DictObjFirst(
    Tcl_Interp *interp,		/* For error messages, or NULL if no error
				 * messages desired. */
    Tcl_Obj *dictPtr,		/* Dictionary to traverse. */
    Tcl_DictSearch *searchPtr,	/* Pointer to a dict search context. */
    Tcl_Obj **keyPtrPtr,	/* Pointer to a variable to have the first key
				 * written into, or NULL. */
    Tcl_Obj **valuePtrPtr,	/* Pointer to a variable to have the first
				 * value written into, or NULL.*/
    int *donePtr)		/* Pointer to a variable which will have a 1
				 * written into when there are no further
				 * values in the dictionary, or a 0
				 * otherwise. */
{
    Dict *dict;
    ChainEntry *cPtr;

    if (dictPtr->typePtr != &tclDictType) {
	int result = SetDictFromAny(interp, dictPtr);

	if (result != TCL_OK) {
	    return result;
	}
    }

    dict = dictPtr->internalRep.otherValuePtr;
    cPtr = dict->entryChainHead;
    if (cPtr == NULL) {
	searchPtr->epoch = -1;
	*donePtr = 1;
    } else {
	*donePtr = 0;
	searchPtr->dictionaryPtr = (Tcl_Dict) dict;
	searchPtr->epoch = dict->epoch;
	searchPtr->next = cPtr->nextPtr;
	dict->refcount++;
	if (keyPtrPtr != NULL) {
	    *keyPtrPtr = (Tcl_Obj *) Tcl_GetHashKey(&dict->table,
		    &cPtr->entry);
	}
	if (valuePtrPtr != NULL) {
	    *valuePtrPtr = Tcl_GetHashValue(&cPtr->entry);
	}
    }
    return TCL_OK;
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_DictObjNext --
 *
 *	Continue a traversal of a dictionary previously started with
 *	Tcl_DictObjFirst. This function is safe against concurrent
 *	modification of the underlying object (including type shimmering),
 *	treating such situations as if the search has terminated, though it is
 *	up to the caller to ensure that the object itself is not disposed
 *	until the search has finished. It is _not_ safe against modifications
 *	from other threads.
 *
 * Results:
 *	Updates the variables pointed to by keyPtrPtr, valuePtrPtr and
 *	donePtr. Either of keyPtrPtr and valuePtrPtr may be NULL, in which
 *	case the key/value is not made available to the caller.
 *
 * Side effects:
 *	Removes a reference to the dictionary's internal rep if the search
 *	terminates.
 *
 *----------------------------------------------------------------------
 */

void
Tcl_DictObjNext(
    Tcl_DictSearch *searchPtr,	/* Pointer to a hash search context. */
    Tcl_Obj **keyPtrPtr,	/* Pointer to a variable to have the first key
				 * written into, or NULL. */
    Tcl_Obj **valuePtrPtr,	/* Pointer to a variable to have the first
				 * value written into, or NULL.*/
    int *donePtr)		/* Pointer to a variable which will have a 1
				 * written into when there are no further
				 * values in the dictionary, or a 0
				 * otherwise. */
{
    ChainEntry *cPtr;

    /*
     * If the searh is done; we do no work.
     */

    if (searchPtr->epoch == -1) {
	*donePtr = 1;
	return;
    }

    /*
     * Bail out if the dictionary has had any elements added, modified or
     * removed. This *shouldn't* happen, but...
     */

    if (((Dict *)searchPtr->dictionaryPtr)->epoch != searchPtr->epoch) {
	Tcl_Panic("concurrent dictionary modification and search");
    }

    cPtr = searchPtr->next;
    if (cPtr == NULL) {
	Tcl_DictObjDone(searchPtr);
	*donePtr = 1;
	return;
    }

    searchPtr->next = cPtr->nextPtr;
    *donePtr = 0;
    if (keyPtrPtr != NULL) {
	*keyPtrPtr = (Tcl_Obj *) Tcl_GetHashKey(
		&((Dict *)searchPtr->dictionaryPtr)->table, &cPtr->entry);
    }
    if (valuePtrPtr != NULL) {
	*valuePtrPtr = Tcl_GetHashValue(&cPtr->entry);
    }
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_DictObjDone --
 *
 *	Call this if you want to stop a search before you reach the end of the
 *	dictionary (e.g. because of abnormal termination of the search). It
 *	need not be used if the search reaches its natural end (i.e. if either
 *	Tcl_DictObjFirst or Tcl_DictObjNext sets its donePtr variable to 1).
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	Removes a reference to the dictionary's internal rep.
 *
 *----------------------------------------------------------------------
 */

void
Tcl_DictObjDone(
    Tcl_DictSearch *searchPtr)		/* Pointer to a hash search context. */
{
    Dict *dict;

    if (searchPtr->epoch != -1) {
	searchPtr->epoch = -1;
	dict = (Dict *) searchPtr->dictionaryPtr;
	dict->refcount--;
	if (dict->refcount <= 0) {
	    DeleteDict(dict);
	}
    }
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_DictObjPutKeyList --
 *
 *	Add a key...key,value pair to a dictionary tree. The main dictionary
 *	value must not be shared, though sub-dictionaries may be. All
 *	intermediate dictionaries on the path must exist.
 *
 * Results:
 *	A standard Tcl result. Note that in the error case, a message is left
 *	in interp unless that is NULL.
 *
 * Side effects:
 *	If the dictionary and any of its sub-dictionaries on the path have
 *	string representations, these are invalidated.
 *
 *----------------------------------------------------------------------
 */

int
Tcl_DictObjPutKeyList(
    Tcl_Interp *interp,
    Tcl_Obj *dictPtr,
    int keyc,
    Tcl_Obj *const keyv[],
    Tcl_Obj *valuePtr)
{
    Dict *dict;
    Tcl_HashEntry *hPtr;
    int isNew;

    if (Tcl_IsShared(dictPtr)) {
	Tcl_Panic("%s called with shared object", "Tcl_DictObjPutKeyList");
    }
    if (keyc < 1) {
	Tcl_Panic("%s called with empty key list", "Tcl_DictObjPutKeyList");
    }

    dictPtr = TclTraceDictPath(interp, dictPtr, keyc-1,keyv, DICT_PATH_CREATE);
    if (dictPtr == NULL) {
	return TCL_ERROR;
    }

    dict = dictPtr->internalRep.otherValuePtr;
    hPtr = CreateChainEntry(dict, keyv[keyc-1], &isNew);
    Tcl_IncrRefCount(valuePtr);
    if (!isNew) {
	Tcl_Obj *oldValuePtr = Tcl_GetHashValue(hPtr);
	TclDecrRefCount(oldValuePtr);
    }
    Tcl_SetHashValue(hPtr, valuePtr);
    InvalidateDictChain(dictPtr);

    return TCL_OK;
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_DictObjRemoveKeyList --
 *
 *	Remove a key...key,value pair from a dictionary tree (the value
 *	removed is implicit in the key path). The main dictionary value must
 *	not be shared, though sub-dictionaries may be. It is not an error if
 *	there is no value associated with the given key list, but all
 *	intermediate dictionaries on the key path must exist.
 *
 * Results:
 *	A standard Tcl result. Note that in the error case, a message is left
 *	in interp unless that is NULL.
 *
 * Side effects:
 *	If the dictionary and any of its sub-dictionaries on the key path have
 *	string representations, these are invalidated.
 *
 *----------------------------------------------------------------------
 */

int
Tcl_DictObjRemoveKeyList(
    Tcl_Interp *interp,
    Tcl_Obj *dictPtr,
    int keyc,
    Tcl_Obj *const keyv[])
{
    Dict *dict;

    if (Tcl_IsShared(dictPtr)) {
	Tcl_Panic("%s called with shared object", "Tcl_DictObjRemoveKeyList");
    }
    if (keyc < 1) {
	Tcl_Panic("%s called with empty key list", "Tcl_DictObjRemoveKeyList");
    }

    dictPtr = TclTraceDictPath(interp, dictPtr, keyc-1,keyv, DICT_PATH_UPDATE);
    if (dictPtr == NULL) {
	return TCL_ERROR;
    }

    dict = dictPtr->internalRep.otherValuePtr;
    DeleteChainEntry(dict, keyv[keyc-1]);
    InvalidateDictChain(dictPtr);
    return TCL_OK;
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_NewDictObj --
 *
 *	This function is normally called when not debugging: i.e., when
 *	TCL_MEM_DEBUG is not defined. It creates a new dict object without any
 *	content.
 *
 *	When TCL_MEM_DEBUG is defined, this function just returns the result
 *	of calling the debugging version Tcl_DbNewDictObj.
 *
 * Results:
 *	A new dict object is returned; it has no keys defined in it. The new
 *	object's string representation is left NULL, and the ref count of the
 *	object is 0.
 *
 * Side Effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */

Tcl_Obj *
Tcl_NewDictObj(void)
{
#ifdef TCL_MEM_DEBUG
    return Tcl_DbNewDictObj("unknown", 0);
#else /* !TCL_MEM_DEBUG */

    Tcl_Obj *dictPtr;
    Dict *dict;

    TclNewObj(dictPtr);
    Tcl_InvalidateStringRep(dictPtr);
    dict = (Dict *) ckalloc(sizeof(Dict));
    InitChainTable(dict);
    dict->epoch = 0;
    dict->chain = NULL;
    dict->refcount = 1;
    dictPtr->internalRep.otherValuePtr = dict;
    dictPtr->typePtr = &tclDictType;
    return dictPtr;
#endif
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_DbNewDictObj --
 *
 *	This function is normally called when debugging: i.e., when
 *	TCL_MEM_DEBUG is defined. It creates new dict objects. It is the same
 *	as the Tcl_NewDictObj function above except that it calls
 *	Tcl_DbCkalloc directly with the file name and line number from its
 *	caller. This simplifies debugging since then the [memory active]
 *	command will report the correct file name and line number when
 *	reporting objects that haven't been freed.
 *
 *	When TCL_MEM_DEBUG is not defined, this function just returns the
 *	result of calling Tcl_NewDictObj.
 *
 * Results:
 *	A new dict object is returned; it has no keys defined in it. The new
 *	object's string representation is left NULL, and the ref count of the
 *	object is 0.
 *
 * Side Effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */

Tcl_Obj *
Tcl_DbNewDictObj(
    const char *file,
    int line)
{
#ifdef TCL_MEM_DEBUG
    Tcl_Obj *dictPtr;
    Dict *dict;

    TclDbNewObj(dictPtr, file, line);
    Tcl_InvalidateStringRep(dictPtr);
    dict = (Dict *) ckalloc(sizeof(Dict));
    InitChainTable(dict);
    dict->epoch = 0;
    dict->chain = NULL;
    dict->refcount = 1;
    dictPtr->internalRep.otherValuePtr = dict;
    dictPtr->typePtr = &tclDictType;
    return dictPtr;
#else /* !TCL_MEM_DEBUG */
    return Tcl_NewDictObj();
#endif
}

/***** START OF FUNCTIONS IMPLEMENTING TCL COMMANDS *****/

/*
 *----------------------------------------------------------------------
 *
 * DictCreateCmd --
 *
 *	This function implements the "dict create" Tcl command. See the user
 *	documentation for details on what it does, and TIP#111 for the formal
 *	specification.
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
DictCreateCmd(
    ClientData dummy,
    Tcl_Interp *interp,
    int objc,
    Tcl_Obj *const *objv)
{
    Tcl_Obj *dictObj;
    int i;

    /*
     * Must have an even number of arguments; note that number of preceding
     * arguments (i.e. "dict create" is also even, which makes this much
     * easier.)
     */

    if ((objc & 1) == 0) {
	Tcl_WrongNumArgs(interp, 1, objv, "?key value ...?");
	return TCL_ERROR;
    }

    dictObj = Tcl_NewDictObj();
    for (i=1 ; i<objc ; i+=2) {
	/*
	 * The next command is assumed to never fail...
	 */
	Tcl_DictObjPut(interp, dictObj, objv[i], objv[i+1]);
    }
    Tcl_SetObjResult(interp, dictObj);
    return TCL_OK;
}

/*
 *----------------------------------------------------------------------
 *
 * DictGetCmd --
 *
 *	This function implements the "dict get" Tcl command. See the user
 *	documentation for details on what it does, and TIP#111 for the formal
 *	specification.
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
DictGetCmd(
    ClientData dummy,
    Tcl_Interp *interp,
    int objc,
    Tcl_Obj *const *objv)
{
    Tcl_Obj *dictPtr, *valuePtr = NULL;
    int result;

    if (objc < 2) {
	Tcl_WrongNumArgs(interp, 1, objv, "dictionary ?key key ...?");
	return TCL_ERROR;
    }

    /*
     * Test for the special case of no keys, which returns a *list* of all
     * key,value pairs. We produce a copy here because that makes subsequent
     * list handling more efficient.
     */

    if (objc == 2) {
	Tcl_Obj *keyPtr, *listPtr;
	Tcl_DictSearch search;
	int done;

	result = Tcl_DictObjFirst(interp, objv[1], &search,
		&keyPtr, &valuePtr, &done);
	if (result != TCL_OK) {
	    return result;
	}
	listPtr = Tcl_NewListObj(0, NULL);
	while (!done) {
	    /*
	     * Assume these won't fail as we have complete control over the
	     * types of things here.
	     */

	    Tcl_ListObjAppendElement(interp, listPtr, keyPtr);
	    Tcl_ListObjAppendElement(interp, listPtr, valuePtr);

	    Tcl_DictObjNext(&search, &keyPtr, &valuePtr, &done);
	}
	Tcl_SetObjResult(interp, listPtr);
	return TCL_OK;
    }

    /*
     * Loop through the list of keys, looking up the key at the current index
     * in the current dictionary each time. Once we've done the lookup, we set
     * the current dictionary to be the value we looked up (in case the value
     * was not the last one and we are going through a chain of searches.)
     * Note that this loop always executes at least once.
     */

    dictPtr = TclTraceDictPath(interp, objv[1], objc-3,objv+2, DICT_PATH_READ);
    if (dictPtr == NULL) {
	return TCL_ERROR;
    }
    result = Tcl_DictObjGet(interp, dictPtr, objv[objc-1], &valuePtr);
    if (result != TCL_OK) {
	return result;
    }
    if (valuePtr == NULL) {
	Tcl_ResetResult(interp);
	Tcl_AppendResult(interp, "key \"", TclGetString(objv[objc-1]),
		"\" not known in dictionary", NULL);
	return TCL_ERROR;
    }
    Tcl_SetObjResult(interp, valuePtr);
    return TCL_OK;
}

/*
 *----------------------------------------------------------------------
 *
 * DictReplaceCmd --
 *
 *	This function implements the "dict replace" Tcl command. See the user
 *	documentation for details on what it does, and TIP#111 for the formal
 *	specification.
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
DictReplaceCmd(
    ClientData dummy,
    Tcl_Interp *interp,
    int objc,
    Tcl_Obj *const *objv)
{
    Tcl_Obj *dictPtr;
    int i, result;
    int allocatedDict = 0;

    if ((objc < 2) || (objc & 1)) {
	Tcl_WrongNumArgs(interp, 1, objv, "dictionary ?key value ...?");
	return TCL_ERROR;
    }

    dictPtr = objv[1];
    if (Tcl_IsShared(dictPtr)) {
	dictPtr = Tcl_DuplicateObj(dictPtr);
	allocatedDict = 1;
    }
    for (i=2 ; i<objc ; i+=2) {
	result = Tcl_DictObjPut(interp, dictPtr, objv[i], objv[i+1]);
	if (result != TCL_OK) {
	    if (allocatedDict) {
		TclDecrRefCount(dictPtr);
	    }
	    return TCL_ERROR;
	}
    }
    Tcl_SetObjResult(interp, dictPtr);
    return TCL_OK;
}

/*
 *----------------------------------------------------------------------
 *
 * DictRemoveCmd --
 *
 *	This function implements the "dict remove" Tcl command. See the user
 *	documentation for details on what it does, and TIP#111 for the formal
 *	specification.
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
DictRemoveCmd(
    ClientData dummy,
    Tcl_Interp *interp,
    int objc,
    Tcl_Obj *const *objv)
{
    Tcl_Obj *dictPtr;
    int i, result;
    int allocatedDict = 0;

    if (objc < 2) {
	Tcl_WrongNumArgs(interp, 1, objv, "dictionary ?key ...?");
	return TCL_ERROR;
    }

    dictPtr = objv[1];
    if (Tcl_IsShared(dictPtr)) {
	dictPtr = Tcl_DuplicateObj(dictPtr);
	allocatedDict = 1;
    }
    for (i=2 ; i<objc ; i++) {
	result = Tcl_DictObjRemove(interp, dictPtr, objv[i]);
	if (result != TCL_OK) {
	    if (allocatedDict) {
		TclDecrRefCount(dictPtr);
	    }
	    return TCL_ERROR;
	}
    }
    Tcl_SetObjResult(interp, dictPtr);
    return TCL_OK;
}

/*
 *----------------------------------------------------------------------
 *
 * DictMergeCmd --
 *
 *	This function implements the "dict merge" Tcl command. See the user
 *	documentation for details on what it does, and TIP#163 for the formal
 *	specification.
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
DictMergeCmd(
    ClientData dummy,
    Tcl_Interp *interp,
    int objc,
    Tcl_Obj *const *objv)
{
    Tcl_Obj *targetObj, *keyObj, *valueObj;
    int allocatedDict = 0;
    int i, done;
    Tcl_DictSearch search;

    if (objc == 1) {
	/*
	 * No dictionary arguments; return default (empty value).
	 */

	return TCL_OK;
    }

    /*
     * Make sure first argument is a dictionary.
     */

    targetObj = objv[1];
    if (targetObj->typePtr != &tclDictType) {
	if (SetDictFromAny(interp, targetObj) != TCL_OK) {
	    return TCL_ERROR;
	}
    }

    if (objc == 2) {
	/*
	 * Single argument, return it.
	 */

	Tcl_SetObjResult(interp, objv[1]);
	return TCL_OK;
    }

    /*
     * Normal behaviour: combining two (or more) dictionaries.
     */

    if (Tcl_IsShared(targetObj)) {
	targetObj = Tcl_DuplicateObj(targetObj);
	allocatedDict = 1;
    }
    for (i=2 ; i<objc ; i++) {
	if (Tcl_DictObjFirst(interp, objv[i], &search, &keyObj, &valueObj,
		&done) != TCL_OK) {
	    if (allocatedDict) {
		TclDecrRefCount(targetObj);
	    }
	    return TCL_ERROR;
	}
	while (!done) {
	    /*
	     * Next line can't fail; already know we have a dictionary in
	     * targetObj.
	     */

	    Tcl_DictObjPut(NULL, targetObj, keyObj, valueObj);
	    Tcl_DictObjNext(&search, &keyObj, &valueObj, &done);
	}
	Tcl_DictObjDone(&search);
    }
    Tcl_SetObjResult(interp, targetObj);
    return TCL_OK;
}

/*
 *----------------------------------------------------------------------
 *
 * DictKeysCmd --
 *
 *	This function implements the "dict keys" Tcl command. See the user
 *	documentation for details on what it does, and TIP#111 for the formal
 *	specification.
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
DictKeysCmd(
    ClientData dummy,
    Tcl_Interp *interp,
    int objc,
    Tcl_Obj *const *objv)
{
    Tcl_Obj *listPtr;
    char *pattern = NULL;

    if (objc!=2 && objc!=3) {
	Tcl_WrongNumArgs(interp, 1, objv, "dictionary ?pattern?");
	return TCL_ERROR;
    }

    /*
     * A direct check that we have a dictionary. We don't start the iteration
     * yet because that might allocate memory or set locks that we do not
     * need. [Bug 1705778, leak K04]
     */

    if (objv[1]->typePtr != &tclDictType) {
	int result = SetDictFromAny(interp, objv[1]);

	if (result != TCL_OK) {
	    return result;
	}
    }

    if (objc == 3) {
	pattern = TclGetString(objv[2]);
    }
    listPtr = Tcl_NewListObj(0, NULL);
    if ((pattern != NULL) && TclMatchIsTrivial(pattern)) {
	Tcl_Obj *valuePtr = NULL;

	Tcl_DictObjGet(interp, objv[1], objv[2], &valuePtr);
	if (valuePtr != NULL) {
	    Tcl_ListObjAppendElement(NULL, listPtr, objv[2]);
	}
    } else {
	Tcl_DictSearch search;
	Tcl_Obj *keyPtr;
	int done;

	/*
	 * At this point, we know we have a dictionary (or at least something
	 * that can be represented; it could theoretically have shimmered away
	 * when the pattern was fetched, but that shouldn't be damaging) so we
	 * can start the iteration process without checking for failures.
	 */

	Tcl_DictObjFirst(NULL, objv[1], &search, &keyPtr, NULL, &done);
	for (; !done ; Tcl_DictObjNext(&search, &keyPtr, NULL, &done)) {
	    if (!pattern || Tcl_StringMatch(TclGetString(keyPtr), pattern)) {
		Tcl_ListObjAppendElement(NULL, listPtr, keyPtr);
	    }
	}
	Tcl_DictObjDone(&search);
    }

    Tcl_SetObjResult(interp, listPtr);
    return TCL_OK;
}

/*
 *----------------------------------------------------------------------
 *
 * DictValuesCmd --
 *
 *	This function implements the "dict values" Tcl command. See the user
 *	documentation for details on what it does, and TIP#111 for the formal
 *	specification.
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
DictValuesCmd(
    ClientData dummy,
    Tcl_Interp *interp,
    int objc,
    Tcl_Obj *const *objv)
{
    Tcl_Obj *valuePtr, *listPtr;
    Tcl_DictSearch search;
    int done;
    char *pattern;

    if (objc!=2 && objc!=3) {
	Tcl_WrongNumArgs(interp, 1, objv, "dictionary ?pattern?");
	return TCL_ERROR;
    }

    if (Tcl_DictObjFirst(interp, objv[1], &search, NULL, &valuePtr,
	    &done) != TCL_OK) {
	return TCL_ERROR;
    }
    if (objc == 3) {
	pattern = TclGetString(objv[2]);
    } else {
	pattern = NULL;
    }
    listPtr = Tcl_NewListObj(0, NULL);
    for (; !done ; Tcl_DictObjNext(&search, NULL, &valuePtr, &done)) {
	if (pattern==NULL || Tcl_StringMatch(TclGetString(valuePtr),pattern)) {
	    /*
	     * Assume this operation always succeeds.
	     */

	    Tcl_ListObjAppendElement(interp, listPtr, valuePtr);
	}
    }
    Tcl_DictObjDone(&search);

    Tcl_SetObjResult(interp, listPtr);
    return TCL_OK;
}

/*
 *----------------------------------------------------------------------
 *
 * DictSizeCmd --
 *
 *	This function implements the "dict size" Tcl command. See the user
 *	documentation for details on what it does, and TIP#111 for the formal
 *	specification.
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
DictSizeCmd(
    ClientData dummy,
    Tcl_Interp *interp,
    int objc,
    Tcl_Obj *const *objv)
{
    int result, size;

    if (objc != 2) {
	Tcl_WrongNumArgs(interp, 1, objv, "dictionary");
	return TCL_ERROR;
    }
    result = Tcl_DictObjSize(interp, objv[1], &size);
    if (result == TCL_OK) {
	Tcl_SetObjResult(interp, Tcl_NewIntObj(size));
    }
    return result;
}

/*
 *----------------------------------------------------------------------
 *
 * DictExistsCmd --
 *
 *	This function implements the "dict exists" Tcl command. See the user
 *	documentation for details on what it does, and TIP#111 for the formal
 *	specification.
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
DictExistsCmd(
    ClientData dummy,
    Tcl_Interp *interp,
    int objc,
    Tcl_Obj *const *objv)
{
    Tcl_Obj *dictPtr, *valuePtr;
    int result;

    if (objc < 3) {
	Tcl_WrongNumArgs(interp, 1, objv, "dictionary key ?key ...?");
	return TCL_ERROR;
    }

    dictPtr = TclTraceDictPath(interp, objv[1], objc-3, objv+2,
	    DICT_PATH_EXISTS);
    if (dictPtr == NULL) {
	return TCL_ERROR;
    }
    if (dictPtr == DICT_PATH_NON_EXISTENT) {
	Tcl_SetObjResult(interp, Tcl_NewBooleanObj(0));
	return TCL_OK;
    }
    result = Tcl_DictObjGet(interp, dictPtr, objv[objc-1], &valuePtr);
    if (result != TCL_OK) {
	return result;
    }
    Tcl_SetObjResult(interp, Tcl_NewBooleanObj(valuePtr != NULL));
    return TCL_OK;
}

/*
 *----------------------------------------------------------------------
 *
 * DictInfoCmd --
 *
 *	This function implements the "dict info" Tcl command. See the user
 *	documentation for details on what it does, and TIP#111 for the formal
 *	specification.
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
DictInfoCmd(
    ClientData dummy,
    Tcl_Interp *interp,
    int objc,
    Tcl_Obj *const *objv)
{
    Tcl_Obj *dictPtr;
    Dict *dict;

    if (objc != 2) {
	Tcl_WrongNumArgs(interp, 1, objv, "dictionary");
	return TCL_ERROR;
    }

    dictPtr = objv[1];
    if (dictPtr->typePtr != &tclDictType) {
	int result = SetDictFromAny(interp, dictPtr);
	if (result != TCL_OK) {
	    return result;
	}
    }
    dict = dictPtr->internalRep.otherValuePtr;

    /*
     * This next cast is actually OK.
     */

    Tcl_SetResult(interp, (char *) Tcl_HashStats(&dict->table), TCL_DYNAMIC);
    return TCL_OK;
}

/*
 *----------------------------------------------------------------------
 *
 * DictIncrCmd --
 *
 *	This function implements the "dict incr" Tcl command. See the user
 *	documentation for details on what it does, and TIP#111 for the formal
 *	specification.
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
DictIncrCmd(
    ClientData dummy,
    Tcl_Interp *interp,
    int objc,
    Tcl_Obj *const *objv)
{
    int code = TCL_OK;
    Tcl_Obj *dictPtr, *valuePtr = NULL;

    if (objc < 3 || objc > 4) {
	Tcl_WrongNumArgs(interp, 1, objv, "varName key ?increment?");
	return TCL_ERROR;
    }

    dictPtr = Tcl_ObjGetVar2(interp, objv[1], NULL, 0);
    if (dictPtr == NULL) {
	/*
	 * Variable didn't yet exist. Create new dictionary value.
	 */

	dictPtr = Tcl_NewDictObj();
    } else if (Tcl_DictObjGet(interp, dictPtr, objv[2], &valuePtr) != TCL_OK) {
	/*
	 * Variable contents are not a dict, report error.
	 */

	return TCL_ERROR;
    }
    if (Tcl_IsShared(dictPtr)) {
	/*
	 * A little internals surgery to avoid copying a string rep that will
	 * soon be no good.
	 */

	char *saved = dictPtr->bytes;

	dictPtr->bytes = NULL;
	dictPtr = Tcl_DuplicateObj(dictPtr);
	dictPtr->bytes = saved;
    }
    if (valuePtr == NULL) {
	/*
	 * Key not in dictionary. Create new key with increment as value.
	 */

	if (objc == 4) {
	    /*
	     * Verify increment is an integer.
	     */

	    mp_int increment;

	    code = Tcl_GetBignumFromObj(interp, objv[3], &increment);
	    if (code != TCL_OK) {
		Tcl_AddErrorInfo(interp, "\n    (reading increment)");
	    } else {
		Tcl_DictObjPut(interp, dictPtr, objv[2], objv[3]);
	    }
	} else {
	    Tcl_DictObjPut(interp, dictPtr, objv[2], Tcl_NewIntObj(1));
	}
    } else {
	/*
	 * Key in dictionary. Increment its value with minimum dup.
	 */

	if (Tcl_IsShared(valuePtr)) {
	    valuePtr = Tcl_DuplicateObj(valuePtr);
	    Tcl_DictObjPut(interp, dictPtr, objv[2], valuePtr);
	}
	if (objc == 4) {
	    code = TclIncrObj(interp, valuePtr, objv[3]);
	} else {
	    Tcl_Obj *incrPtr = Tcl_NewIntObj(1);

	    Tcl_IncrRefCount(incrPtr);
	    code = TclIncrObj(interp, valuePtr, incrPtr);
	    Tcl_DecrRefCount(incrPtr);
	}
    }
    if (code == TCL_OK) {
	Tcl_InvalidateStringRep(dictPtr);
	valuePtr = Tcl_ObjSetVar2(interp, objv[1], NULL,
		dictPtr, TCL_LEAVE_ERR_MSG);
	if (valuePtr == NULL) {
	    code = TCL_ERROR;
	} else {
	    Tcl_SetObjResult(interp, valuePtr);
	}
    } else if (dictPtr->refCount == 0) {
	Tcl_DecrRefCount(dictPtr);
    }
    return code;
}

/*
 *----------------------------------------------------------------------
 *
 * DictLappendCmd --
 *
 *	This function implements the "dict lappend" Tcl command. See the user
 *	documentation for details on what it does, and TIP#111 for the formal
 *	specification.
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
DictLappendCmd(
    ClientData dummy,
    Tcl_Interp *interp,
    int objc,
    Tcl_Obj *const *objv)
{
    Tcl_Obj *dictPtr, *valuePtr, *resultPtr;
    int i, allocatedDict = 0, allocatedValue = 0;

    if (objc < 3) {
	Tcl_WrongNumArgs(interp, 1, objv, "varName key ?value ...?");
	return TCL_ERROR;
    }

    dictPtr = Tcl_ObjGetVar2(interp, objv[1], NULL, 0);
    if (dictPtr == NULL) {
	allocatedDict = 1;
	dictPtr = Tcl_NewDictObj();
    } else if (Tcl_IsShared(dictPtr)) {
	allocatedDict = 1;
	dictPtr = Tcl_DuplicateObj(dictPtr);
    }

    if (Tcl_DictObjGet(interp, dictPtr, objv[2], &valuePtr) != TCL_OK) {
	if (allocatedDict) {
	    TclDecrRefCount(dictPtr);
	}
	return TCL_ERROR;
    }

    if (valuePtr == NULL) {
	valuePtr = Tcl_NewListObj(objc-3, objv+3);
	allocatedValue = 1;
    } else {
	if (Tcl_IsShared(valuePtr)) {
	    allocatedValue = 1;
	    valuePtr = Tcl_DuplicateObj(valuePtr);
	}

	for (i=3 ; i<objc ; i++) {
	    if (Tcl_ListObjAppendElement(interp, valuePtr,
		    objv[i]) != TCL_OK) {
		if (allocatedValue) {
		    TclDecrRefCount(valuePtr);
		}
		if (allocatedDict) {
		    TclDecrRefCount(dictPtr);
		}
		return TCL_ERROR;
	    }
	}
    }

    if (allocatedValue) {
	Tcl_DictObjPut(interp, dictPtr, objv[2], valuePtr);
    } else if (dictPtr->bytes != NULL) {
	Tcl_InvalidateStringRep(dictPtr);
    }

    resultPtr = Tcl_ObjSetVar2(interp, objv[1], NULL, dictPtr,
	    TCL_LEAVE_ERR_MSG);
    if (resultPtr == NULL) {
	return TCL_ERROR;
    }
    Tcl_SetObjResult(interp, resultPtr);
    return TCL_OK;
}

/*
 *----------------------------------------------------------------------
 *
 * DictAppendCmd --
 *
 *	This function implements the "dict append" Tcl command. See the user
 *	documentation for details on what it does, and TIP#111 for the formal
 *	specification.
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
DictAppendCmd(
    ClientData dummy,
    Tcl_Interp *interp,
    int objc,
    Tcl_Obj *const *objv)
{
    Tcl_Obj *dictPtr, *valuePtr, *resultPtr;
    int i, allocatedDict = 0;

    if (objc < 3) {
	Tcl_WrongNumArgs(interp, 1, objv, "varName key ?value ...?");
	return TCL_ERROR;
    }

    dictPtr = Tcl_ObjGetVar2(interp, objv[1], NULL, 0);
    if (dictPtr == NULL) {
	allocatedDict = 1;
	dictPtr = Tcl_NewDictObj();
    } else if (Tcl_IsShared(dictPtr)) {
	allocatedDict = 1;
	dictPtr = Tcl_DuplicateObj(dictPtr);
    }

    if (Tcl_DictObjGet(interp, dictPtr, objv[2], &valuePtr) != TCL_OK) {
	if (allocatedDict) {
	    TclDecrRefCount(dictPtr);
	}
	return TCL_ERROR;
    }

    if (valuePtr == NULL) {
	TclNewObj(valuePtr);
    } else {
	if (Tcl_IsShared(valuePtr)) {
	    valuePtr = Tcl_DuplicateObj(valuePtr);
	}
    }

    for (i=3 ; i<objc ; i++) {
	Tcl_AppendObjToObj(valuePtr, objv[i]);
    }

    Tcl_DictObjPut(interp, dictPtr, objv[2], valuePtr);

    resultPtr = Tcl_ObjSetVar2(interp, objv[1], NULL, dictPtr,
	    TCL_LEAVE_ERR_MSG);
    if (resultPtr == NULL) {
	return TCL_ERROR;
    }
    Tcl_SetObjResult(interp, resultPtr);
    return TCL_OK;
}

/*
 *----------------------------------------------------------------------
 *
 * DictForCmd --
 *
 *	This function implements the "dict for" Tcl command. See the user
 *	documentation for details on what it does, and TIP#111 for the formal
 *	specification.
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
DictForCmd(
    ClientData dummy,
    Tcl_Interp *interp,
    int objc,
    Tcl_Obj *const *objv)
{
    Interp *iPtr = (Interp *) interp;
    Tcl_Obj *scriptObj, *keyVarObj, *valueVarObj;
    Tcl_Obj **varv, *keyObj, *valueObj;
    Tcl_DictSearch search;
    int varc, done, result;

    if (objc != 4) {
	Tcl_WrongNumArgs(interp, 1, objv,
		"{keyVar valueVar} dictionary script");
	return TCL_ERROR;
    }

    if (TclListObjGetElements(interp, objv[1], &varc, &varv) != TCL_OK) {
	return TCL_ERROR;
    }
    if (varc != 2) {
	Tcl_SetResult(interp, "must have exactly two variable names",
		TCL_STATIC);
	return TCL_ERROR;
    }
    keyVarObj = varv[0];
    valueVarObj = varv[1];
    scriptObj = objv[3];

    if (Tcl_DictObjFirst(interp, objv[2], &search, &keyObj, &valueObj,
	    &done) != TCL_OK) {
	return TCL_ERROR;
    }

    /*
     * Make sure that these objects (which we need throughout the body of the
     * loop) don't vanish. Note that the dictionary internal rep is locked
     * internally so that updates, shimmering, etc are not a problem.
     */

    Tcl_IncrRefCount(keyVarObj);
    Tcl_IncrRefCount(valueVarObj);
    Tcl_IncrRefCount(scriptObj);

    result = TCL_OK;
    while (!done) {
	/*
	 * Stop the value from getting hit in any way by any traces on the key
	 * variable.
	 */

	Tcl_IncrRefCount(valueObj);
	if (Tcl_ObjSetVar2(interp, keyVarObj, NULL, keyObj, 0) == NULL) {
	    Tcl_ResetResult(interp);
	    Tcl_AppendResult(interp, "couldn't set key variable: \"",
		    TclGetString(keyVarObj), "\"", NULL);
	    TclDecrRefCount(valueObj);
	    result = TCL_ERROR;
	    break;
	}
	TclDecrRefCount(valueObj);
	if (Tcl_ObjSetVar2(interp, valueVarObj, NULL, valueObj, 0) == NULL) {
	    Tcl_ResetResult(interp);
	    Tcl_AppendResult(interp, "couldn't set value variable: \"",
		    TclGetString(valueVarObj), "\"", NULL);
	    result = TCL_ERROR;
	    break;
	}

	/*
	 * TIP #280. Make invoking context available to loop body.
	 */

	result = TclEvalObjEx(interp, scriptObj, 0, iPtr->cmdFramePtr, 3);
	if (result == TCL_CONTINUE) {
	    result = TCL_OK;
	} else if (result != TCL_OK) {
	    if (result == TCL_BREAK) {
		result = TCL_OK;
	    } else if (result == TCL_ERROR) {
		Tcl_AppendObjToErrorInfo(interp, Tcl_ObjPrintf(
			"\n    (\"dict for\" body line %d)",
			interp->errorLine));
	    }
	    break;
	}

	Tcl_DictObjNext(&search, &keyObj, &valueObj, &done);
    }

    /*
     * Stop holding a reference to these objects.
     */

    TclDecrRefCount(keyVarObj);
    TclDecrRefCount(valueVarObj);
    TclDecrRefCount(scriptObj);

    Tcl_DictObjDone(&search);
    if (result == TCL_OK) {
	Tcl_ResetResult(interp);
    }
    return result;
}

/*
 *----------------------------------------------------------------------
 *
 * DictSetCmd --
 *
 *	This function implements the "dict set" Tcl command. See the user
 *	documentation for details on what it does, and TIP#111 for the formal
 *	specification.
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
DictSetCmd(
    ClientData dummy,
    Tcl_Interp *interp,
    int objc,
    Tcl_Obj *const *objv)
{
    Tcl_Obj *dictPtr, *resultPtr;
    int result, allocatedDict = 0;

    if (objc < 4) {
	Tcl_WrongNumArgs(interp, 1, objv, "varName key ?key ...? value");
	return TCL_ERROR;
    }

    dictPtr = Tcl_ObjGetVar2(interp, objv[1], NULL, 0);
    if (dictPtr == NULL) {
	allocatedDict = 1;
	dictPtr = Tcl_NewDictObj();
    } else if (Tcl_IsShared(dictPtr)) {
	allocatedDict = 1;
	dictPtr = Tcl_DuplicateObj(dictPtr);
    }

    result = Tcl_DictObjPutKeyList(interp, dictPtr, objc-3, objv+2,
	    objv[objc-1]);
    if (result != TCL_OK) {
	if (allocatedDict) {
	    TclDecrRefCount(dictPtr);
	}
	return TCL_ERROR;
    }

    resultPtr = Tcl_ObjSetVar2(interp, objv[1], NULL, dictPtr,
	    TCL_LEAVE_ERR_MSG);
    if (resultPtr == NULL) {
	return TCL_ERROR;
    }
    Tcl_SetObjResult(interp, resultPtr);
    return TCL_OK;
}

/*
 *----------------------------------------------------------------------
 *
 * DictUnsetCmd --
 *
 *	This function implements the "dict unset" Tcl command. See the user
 *	documentation for details on what it does, and TIP#111 for the formal
 *	specification.
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
DictUnsetCmd(
    ClientData dummy,
    Tcl_Interp *interp,
    int objc,
    Tcl_Obj *const *objv)
{
    Tcl_Obj *dictPtr, *resultPtr;
    int result, allocatedDict = 0;

    if (objc < 3) {
	Tcl_WrongNumArgs(interp, 1, objv, "varName key ?key ...?");
	return TCL_ERROR;
    }

    dictPtr = Tcl_ObjGetVar2(interp, objv[1], NULL, 0);
    if (dictPtr == NULL) {
	allocatedDict = 1;
	dictPtr = Tcl_NewDictObj();
    } else if (Tcl_IsShared(dictPtr)) {
	allocatedDict = 1;
	dictPtr = Tcl_DuplicateObj(dictPtr);
    }

    result = Tcl_DictObjRemoveKeyList(interp, dictPtr, objc-2, objv+2);
    if (result != TCL_OK) {
	if (allocatedDict) {
	    TclDecrRefCount(dictPtr);
	}
	return TCL_ERROR;
    }

    resultPtr = Tcl_ObjSetVar2(interp, objv[1], NULL, dictPtr,
	    TCL_LEAVE_ERR_MSG);
    if (resultPtr == NULL) {
	return TCL_ERROR;
    }
    Tcl_SetObjResult(interp, resultPtr);
    return TCL_OK;
}

/*
 *----------------------------------------------------------------------
 *
 * DictFilterCmd --
 *
 *	This function implements the "dict filter" Tcl command. See the user
 *	documentation for details on what it does, and TIP#111 for the formal
 *	specification.
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
DictFilterCmd(
    ClientData dummy,
    Tcl_Interp *interp,
    int objc,
    Tcl_Obj *const *objv)
{
    Interp *iPtr = (Interp *) interp;
    static const char *filters[] = {
	"key", "script", "value", NULL
    };
    enum FilterTypes {
	FILTER_KEYS, FILTER_SCRIPT, FILTER_VALUES
    };
    Tcl_Obj *scriptObj, *keyVarObj, *valueVarObj;
    Tcl_Obj **varv, *keyObj, *valueObj, *resultObj, *boolObj;
    Tcl_DictSearch search;
    int index, varc, done, result, satisfied;
    char *pattern;

    if (objc < 3) {
	Tcl_WrongNumArgs(interp, 1, objv, "dictionary filterType ...");
	return TCL_ERROR;
    }
    if (Tcl_GetIndexFromObj(interp, objv[2], filters, "filterType",
	     0, &index) != TCL_OK) {
	return TCL_ERROR;
    }

    switch ((enum FilterTypes) index) {
    case FILTER_KEYS:
	if (objc != 4) {
	    Tcl_WrongNumArgs(interp, 1, objv, "dictionary key globPattern");
	    return TCL_ERROR;
	}

	/*
	 * Create a dictionary whose keys all match a certain pattern.
	 */

	if (Tcl_DictObjFirst(interp, objv[1], &search,
		&keyObj, &valueObj, &done) != TCL_OK) {
	    return TCL_ERROR;
	}
	pattern = TclGetString(objv[3]);
	resultObj = Tcl_NewDictObj();
	if (TclMatchIsTrivial(pattern)) {
	    /*
	     * Must release the search lock here to prevent a memory leak
	     * since we are not exhausing the search. [Bug 1705778, leak K05]
	     */

	    Tcl_DictObjDone(&search);
	    Tcl_DictObjGet(interp, objv[1], objv[3], &valueObj);
	    if (valueObj != NULL) {
		Tcl_DictObjPut(interp, resultObj, objv[3], valueObj);
	    }
	} else {
	    while (!done) {
		if (Tcl_StringMatch(TclGetString(keyObj), pattern)) {
		    Tcl_DictObjPut(interp, resultObj, keyObj, valueObj);
		}
		Tcl_DictObjNext(&search, &keyObj, &valueObj, &done);
	    }
	}
	Tcl_SetObjResult(interp, resultObj);
	return TCL_OK;

    case FILTER_VALUES:
	if (objc != 4) {
	    Tcl_WrongNumArgs(interp, 1, objv, "dictionary value globPattern");
	    return TCL_ERROR;
	}

	/*
	 * Create a dictionary whose values all match a certain pattern.
	 */

	if (Tcl_DictObjFirst(interp, objv[1], &search,
		&keyObj, &valueObj, &done) != TCL_OK) {
	    return TCL_ERROR;
	}
	pattern = TclGetString(objv[3]);
	resultObj = Tcl_NewDictObj();
	while (!done) {
	    if (Tcl_StringMatch(TclGetString(valueObj), pattern)) {
		Tcl_DictObjPut(interp, resultObj, keyObj, valueObj);
	    }
	    Tcl_DictObjNext(&search, &keyObj, &valueObj, &done);
	}
	Tcl_SetObjResult(interp, resultObj);
	return TCL_OK;

    case FILTER_SCRIPT:
	if (objc != 5) {
	    Tcl_WrongNumArgs(interp, 1, objv,
		    "dictionary script {keyVar valueVar} filterScript");
	    return TCL_ERROR;
	}

	/*
	 * Create a dictionary whose key,value pairs all satisfy a script
	 * (i.e. get a true boolean result from its evaluation). Massive
	 * copying from the "dict for" implementation has occurred!
	 */

	if (TclListObjGetElements(interp, objv[3], &varc, &varv) != TCL_OK) {
	    return TCL_ERROR;
	}
	if (varc != 2) {
	    Tcl_SetResult(interp, "must have exactly two variable names",
		    TCL_STATIC);
	    return TCL_ERROR;
	}
	keyVarObj = varv[0];
	valueVarObj = varv[1];
	scriptObj = objv[4];

	/*
	 * Make sure that these objects (which we need throughout the body of
	 * the loop) don't vanish. Note that the dictionary internal rep is
	 * locked internally so that updates, shimmering, etc are not a
	 * problem.
	 */

	Tcl_IncrRefCount(keyVarObj);
	Tcl_IncrRefCount(valueVarObj);
	Tcl_IncrRefCount(scriptObj);

	result = Tcl_DictObjFirst(interp, objv[1],
		&search, &keyObj, &valueObj, &done);
	if (result != TCL_OK) {
	    TclDecrRefCount(keyVarObj);
	    TclDecrRefCount(valueVarObj);
	    TclDecrRefCount(scriptObj);
	    return TCL_ERROR;
	}

	resultObj = Tcl_NewDictObj();

	while (!done) {
	    /*
	     * Stop the value from getting hit in any way by any traces on the
	     * key variable.
	     */

	    Tcl_IncrRefCount(keyObj);
	    Tcl_IncrRefCount(valueObj);
	    if (Tcl_ObjSetVar2(interp, keyVarObj, NULL, keyObj,
		    TCL_LEAVE_ERR_MSG) == NULL) {
		Tcl_ResetResult(interp);
		Tcl_AppendResult(interp, "couldn't set key variable: \"",
			TclGetString(keyVarObj), "\"", NULL);
		result = TCL_ERROR;
		goto abnormalResult;
	    }
	    if (Tcl_ObjSetVar2(interp, valueVarObj, NULL, valueObj,
		    TCL_LEAVE_ERR_MSG) == NULL) {
		Tcl_ResetResult(interp);
		Tcl_AppendResult(interp, "couldn't set value variable: \"",
			TclGetString(valueVarObj), "\"", NULL);
		goto abnormalResult;
	    }

	    /*
	     * TIP #280. Make invoking context available to loop body.
	     */

	    result = TclEvalObjEx(interp, scriptObj, 0, iPtr->cmdFramePtr, 4);
	    switch (result) {
	    case TCL_OK:
		boolObj = Tcl_GetObjResult(interp);
		Tcl_IncrRefCount(boolObj);
		Tcl_ResetResult(interp);
		if (Tcl_GetBooleanFromObj(interp, boolObj,
			&satisfied) != TCL_OK) {
		    TclDecrRefCount(boolObj);
		    result = TCL_ERROR;
		    goto abnormalResult;
		}
		TclDecrRefCount(boolObj);
		if (satisfied) {
		    Tcl_DictObjPut(interp, resultObj, keyObj, valueObj);
		}
		break;
	    case TCL_BREAK:
		/*
		 * Force loop termination by calling Tcl_DictObjDone; this
		 * makes the next Tcl_DictObjNext say there is nothing more to
		 * do.
		 */

		Tcl_ResetResult(interp);
		Tcl_DictObjDone(&search);
	    case TCL_CONTINUE:
		result = TCL_OK;
		break;
	    case TCL_ERROR:
		Tcl_AppendObjToErrorInfo(interp, Tcl_ObjPrintf(
			"\n    (\"dict filter\" script line %d)",
			interp->errorLine));
	    default:
		goto abnormalResult;
	    }

	    TclDecrRefCount(keyObj);
	    TclDecrRefCount(valueObj);

	    Tcl_DictObjNext(&search, &keyObj, &valueObj, &done);
	}

	/*
	 * Stop holding a reference to these objects.
	 */

	TclDecrRefCount(keyVarObj);
	TclDecrRefCount(valueVarObj);
	TclDecrRefCount(scriptObj);
	Tcl_DictObjDone(&search);

	if (result == TCL_OK) {
	    Tcl_SetObjResult(interp, resultObj);
	} else {
	    TclDecrRefCount(resultObj);
	}
	return result;

    abnormalResult:
	Tcl_DictObjDone(&search);
	TclDecrRefCount(keyObj);
	TclDecrRefCount(valueObj);
	TclDecrRefCount(keyVarObj);
	TclDecrRefCount(valueVarObj);
	TclDecrRefCount(scriptObj);
	TclDecrRefCount(resultObj);
	return result;
    }
    Tcl_Panic("unexpected fallthrough");
    /* Control never reaches this point. */
    return TCL_ERROR;
}

/*
 *----------------------------------------------------------------------
 *
 * DictUpdateCmd --
 *
 *	This function implements the "dict update" Tcl command. See the user
 *	documentation for details on what it does, and TIP#212 for the formal
 *	specification.
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
DictUpdateCmd(
    ClientData clientData,
    Tcl_Interp *interp,
    int objc,
    Tcl_Obj *const *objv)
{
    Interp *iPtr = (Interp *) interp;
    Tcl_Obj *dictPtr, *objPtr;
    int i, result, dummy;
    Tcl_InterpState state;

    if (objc < 5 || !(objc & 1)) {
	Tcl_WrongNumArgs(interp, 1, objv,
		"varName key varName ?key varName ...? script");
	return TCL_ERROR;
    }

    dictPtr = Tcl_ObjGetVar2(interp, objv[1], NULL, TCL_LEAVE_ERR_MSG);
    if (dictPtr == NULL) {
	return TCL_ERROR;
    }
    if (Tcl_DictObjSize(interp, dictPtr, &dummy) != TCL_OK) {
	return TCL_ERROR;
    }
    Tcl_IncrRefCount(dictPtr);
    for (i=2 ; i+2<objc ; i+=2) {
	if (Tcl_DictObjGet(interp, dictPtr, objv[i], &objPtr) != TCL_OK) {
	    TclDecrRefCount(dictPtr);
	    return TCL_ERROR;
	}
	if (objPtr == NULL) {
	    /* ??? */
	    Tcl_UnsetVar(interp, Tcl_GetString(objv[i+1]), 0);
	} else if (Tcl_ObjSetVar2(interp, objv[i+1], NULL, objPtr,
		TCL_LEAVE_ERR_MSG) == NULL) {
	    TclDecrRefCount(dictPtr);
	    return TCL_ERROR;
	}
    }
    TclDecrRefCount(dictPtr);

    /*
     * Execute the body.
     */

    result = TclEvalObjEx(interp, objv[objc-1], 0, iPtr->cmdFramePtr, objc-1);
    if (result == TCL_ERROR) {
	Tcl_AddErrorInfo(interp, "\n    (body of \"dict update\")");
    }

    /*
     * If the dictionary variable doesn't exist, drop everything silently.
     */

    dictPtr = Tcl_ObjGetVar2(interp, objv[1], NULL, 0);
    if (dictPtr == NULL) {
	return result;
    }

    /*
     * Double-check that it is still a dictionary.
     */

    state = Tcl_SaveInterpState(interp, result);
    if (Tcl_DictObjSize(interp, dictPtr, &dummy) != TCL_OK) {
	Tcl_DiscardInterpState(state);
	return TCL_ERROR;
    }

    if (Tcl_IsShared(dictPtr)) {
	dictPtr = Tcl_DuplicateObj(dictPtr);
    }

    /*
     * Write back the values from the variables, treating failure to read as
     * an instruction to remove the key.
     */

    for (i=2 ; i+2<objc ; i+=2) {
	objPtr = Tcl_ObjGetVar2(interp, objv[i+1], NULL, 0);
	if (objPtr == NULL) {
	    Tcl_DictObjRemove(interp, dictPtr, objv[i]);
	} else if (objPtr == dictPtr) {
	    /*
	     * Someone is messing us around, trying to build a recursive
	     * structure. [Bug 1786481]
	     */

	    Tcl_DictObjPut(interp, dictPtr, objv[i],
		    Tcl_DuplicateObj(objPtr));
	} else {
	    /* Shouldn't fail */
	    Tcl_DictObjPut(interp, dictPtr, objv[i], objPtr);
	}
    }

    /*
     * Write the dictionary back to its variable.
     */

    if (Tcl_ObjSetVar2(interp, objv[1], NULL, dictPtr,
	    TCL_LEAVE_ERR_MSG) == NULL) {
	Tcl_DiscardInterpState(state);
	return TCL_ERROR;
    }

    return Tcl_RestoreInterpState(interp, state);
}

/*
 *----------------------------------------------------------------------
 *
 * DictWithCmd --
 *
 *	This function implements the "dict with" Tcl command. See the user
 *	documentation for details on what it does, and TIP#212 for the formal
 *	specification.
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
DictWithCmd(
    ClientData dummy,
    Tcl_Interp *interp,
    int objc,
    Tcl_Obj *const *objv)
{
    Interp *iPtr = (Interp *) interp;
    Tcl_Obj *dictPtr, *keysPtr, *keyPtr, *valPtr, **keyv, *leafPtr;
    Tcl_DictSearch s;
    Tcl_InterpState state;
    int done, result, keyc, i, allocdict = 0;

    if (objc < 3) {
	Tcl_WrongNumArgs(interp, 1, objv, "dictVar ?key ...? script");
	return TCL_ERROR;
    }

    /*
     * Get the dictionary to open out.
     */

    dictPtr = Tcl_ObjGetVar2(interp, objv[1], NULL, TCL_LEAVE_ERR_MSG);
    if (dictPtr == NULL) {
	return TCL_ERROR;
    }
    if (objc > 3) {
	dictPtr = TclTraceDictPath(interp, dictPtr, objc-3, objv+2,
		DICT_PATH_READ);
	if (dictPtr == NULL) {
	    return TCL_ERROR;
	}
    }

    /*
     * Go over the list of keys and write each corresponding value to a
     * variable in the current context with the same name. Also keep a copy of
     * the keys so we can write back properly later on even if the dictionary
     * has been structurally modified.
     */

    if (Tcl_DictObjFirst(interp, dictPtr, &s, &keyPtr, &valPtr,
	    &done) != TCL_OK) {
	return TCL_ERROR;
    }

    TclNewObj(keysPtr);
    Tcl_IncrRefCount(keysPtr);

    for (; !done ; Tcl_DictObjNext(&s, &keyPtr, &valPtr, &done)) {
	Tcl_ListObjAppendElement(NULL, keysPtr, keyPtr);
	if (Tcl_ObjSetVar2(interp, keyPtr, NULL, valPtr,
		TCL_LEAVE_ERR_MSG) == NULL) {
	    TclDecrRefCount(keysPtr);
	    Tcl_DictObjDone(&s);
	    return TCL_ERROR;
	}
    }

    /*
     * Execute the body, while making the invoking context available to the
     * loop body (TIP#280).
     */

    result = TclEvalObjEx(interp, objv[objc-1], 0, iPtr->cmdFramePtr, objc-1);
    if (result == TCL_ERROR) {
	Tcl_AddErrorInfo(interp, "\n    (body of \"dict with\")");
    }

    /*
     * If the dictionary variable doesn't exist, drop everything silently.
     */

    dictPtr = Tcl_ObjGetVar2(interp, objv[1], NULL, 0);
    if (dictPtr == NULL) {
	TclDecrRefCount(keysPtr);
	return result;
    }

    /*
     * Double-check that it is still a dictionary.
     */

    state = Tcl_SaveInterpState(interp, result);
    if (Tcl_DictObjSize(interp, dictPtr, &i) != TCL_OK) {
	TclDecrRefCount(keysPtr);
	Tcl_DiscardInterpState(state);
	return TCL_ERROR;
    }

    if (Tcl_IsShared(dictPtr)) {
	dictPtr = Tcl_DuplicateObj(dictPtr);
	allocdict = 1;
    }

    if (objc > 3) {
	/*
	 * Want to get to the dictionary which we will update; need to do
	 * prepare-for-update de-sharing along the path *but* avoid generating
	 * an error on a non-existant path (we'll treat that the same as a
	 * non-existant variable. Luckily, the de-sharing operation isn't
	 * deeply damaging if we don't go on to update; it's just less than
	 * perfectly efficient (but no memory should be leaked).
	 */

	leafPtr = TclTraceDictPath(interp, dictPtr, objc-3, objv+2,
		DICT_PATH_EXISTS | DICT_PATH_UPDATE);
	if (leafPtr == NULL) {
	    TclDecrRefCount(keysPtr);
	    if (allocdict) {
		TclDecrRefCount(dictPtr);
	    }
	    Tcl_DiscardInterpState(state);
	    return TCL_ERROR;
	}
	if (leafPtr == DICT_PATH_NON_EXISTENT) {
	    TclDecrRefCount(keysPtr);
	    if (allocdict) {
		TclDecrRefCount(dictPtr);
	    }
	    return Tcl_RestoreInterpState(interp, state);
	}
    } else {
	leafPtr = dictPtr;
    }

    /*
     * Now process our updates on the leaf dictionary.
     */

    TclListObjGetElements(NULL, keysPtr, &keyc, &keyv);
    for (i=0 ; i<keyc ; i++) {
	valPtr = Tcl_ObjGetVar2(interp, keyv[i], NULL, 0);
	if (valPtr == NULL) {
	    Tcl_DictObjRemove(NULL, leafPtr, keyv[i]);
	} else if (leafPtr == valPtr) {
	    /*
	     * Someone is messing us around, trying to build a recursive
	     * structure. [Bug 1786481]
	     */

	    Tcl_DictObjPut(NULL, leafPtr, keyv[i], Tcl_DuplicateObj(valPtr));
	} else {
	    Tcl_DictObjPut(NULL, leafPtr, keyv[i], valPtr);
	}
    }
    TclDecrRefCount(keysPtr);

    /*
     * Ensure that none of the dictionaries in the chain still have a string
     * rep.
     */

    if (objc > 3) {
	InvalidateDictChain(leafPtr);
    }

    /*
     * Write back the outermost dictionary to the variable.
     */

    if (Tcl_ObjSetVar2(interp, objv[1], NULL, dictPtr,
	    TCL_LEAVE_ERR_MSG) == NULL) {
	Tcl_DiscardInterpState(state);
	return TCL_ERROR;
    }
    return Tcl_RestoreInterpState(interp, state);
}

/*
 *----------------------------------------------------------------------
 *
 * TclInitDictCmd --
 *
 *	This function is create the "dict" Tcl command. See the user
 *	documentation for details on what it does, and TIP#111 for the formal
 *	specification.
 *
 * Results:
 *	A Tcl command handle.
 *
 * Side effects:
 *	May advance compilation epoch.
 *
 *----------------------------------------------------------------------
 */

Tcl_Command
TclInitDictCmd(
    Tcl_Interp *interp)
{
    return TclMakeEnsemble(interp, "dict", implementationMap);
}

/*
 * Local Variables:
 * mode: c
 * c-basic-offset: 4
 * fill-column: 78
 * End:
 */
