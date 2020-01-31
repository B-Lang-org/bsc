/*
 * tclThreadStorage.c --
 *
 *	This file implements platform independent thread storage operations.
 *
 * Copyright (c) 2003-2004 by Joe Mistachkin
 *
 * See the file "license.terms" for information on usage and redistribution of
 * this file, and for a DISCLAIMER OF ALL WARRANTIES.
 *
 * RCS: @(#) $Id: tclThreadStorage.c,v 1.15 2007/12/13 15:23:20 dgp Exp $
 */

#include "tclInt.h"

#if defined(TCL_THREADS)

/*
 * This is the thread storage cache array and it's accompanying mutex. The
 * elements are pairs of thread Id and an associated hash table pointer; the
 * hash table being pointed to contains the thread storage for it's associated
 * thread. The purpose of this cache is to minimize the number of hash table
 * lookups in the master thread storage hash table.
 */

static Tcl_Mutex threadStorageLock;

/*
 * This is the struct used for a thread storage cache slot. It contains the
 * owning thread Id and the associated hash table pointer.
 */

typedef struct ThreadStorage {
    Tcl_ThreadId id;		/* the owning thread id */
    Tcl_HashTable *hashTablePtr;/* the hash table for the thread */
} ThreadStorage;

/*
 * These are the prototypes for the custom hash table allocation functions
 * used by the thread storage subsystem.
 */

static Tcl_HashEntry *	AllocThreadStorageEntry(Tcl_HashTable *tablePtr,
			    void *keyPtr);
static void		FreeThreadStorageEntry(Tcl_HashEntry *hPtr);
static Tcl_HashTable *	ThreadStorageGetHashTable(Tcl_ThreadId id);

/*
 * This is the hash key type for thread storage. We MUST use this in
 * combination with the new hash key type flag TCL_HASH_KEY_SYSTEM_HASH
 * because these hash tables MAY be used by the threaded memory allocator.
 */

static Tcl_HashKeyType tclThreadStorageHashKeyType = {
    TCL_HASH_KEY_TYPE_VERSION,		/* version */
    TCL_HASH_KEY_SYSTEM_HASH | TCL_HASH_KEY_RANDOMIZE_HASH,
				        /* flags */
    NULL,				/* hashKeyProc */
    NULL,				/* compareKeysProc */
    AllocThreadStorageEntry,		/* allocEntryProc */
    FreeThreadStorageEntry		/* freeEntryProc */
};

/*
 * This is an invalid thread value.
 */

#define STORAGE_INVALID_THREAD  (Tcl_ThreadId)0

/*
 * This is the value for an invalid thread storage key.
 */

#define STORAGE_INVALID_KEY	0

/*
 * This is the first valid key for use by external callers. All the values
 * below this are RESERVED for future use.
 */

#define STORAGE_FIRST_KEY	1

/*
 * This is the default number of thread storage cache slots. This define may
 * need to be fine tuned for maximum performance.
 */

#define STORAGE_CACHE_SLOTS	97

/*
 * This is the master thread storage hash table. It is keyed on thread Id and
 * contains values that are hash tables for each thread. The thread specific
 * hash tables contain the actual thread storage.
 */

static Tcl_HashTable threadStorageHashTable;

/*
 * This is the next thread data key value to use. We increment this everytime
 * we "allocate" one. It is initially set to 1 in TclInitThreadStorage.
 */

static int nextThreadStorageKey = STORAGE_INVALID_KEY;

/*
 * This is the master thread storage cache. Per Kevin Kenny's idea, this
 * prevents unnecessary lookups for threads that use a lot of thread storage.
 */

static volatile ThreadStorage threadStorageCache[STORAGE_CACHE_SLOTS];

/*
 *----------------------------------------------------------------------
 *
 * AllocThreadStorageEntry --
 *
 *	Allocate space for a Tcl_HashEntry using TclpSysAlloc (not ckalloc).
 *	We do this because the threaded memory allocator MAY use the thread
 *	storage hash tables.
 *
 * Results:
 *	The return value is a pointer to the created entry.
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */

static Tcl_HashEntry *
AllocThreadStorageEntry(
    Tcl_HashTable *tablePtr,	/* Hash table. */
    void *keyPtr)		/* Key to store in the hash table entry. */
{
    Tcl_HashEntry *hPtr;

    hPtr = (Tcl_HashEntry *) TclpSysAlloc(sizeof(Tcl_HashEntry), 0);
    hPtr->key.oneWordValue = keyPtr;
    hPtr->clientData = NULL;
    
    return hPtr;
}

/*
 *----------------------------------------------------------------------
 *
 * FreeThreadStorageEntry --
 *
 *	Frees space for a Tcl_HashEntry using TclpSysFree (not ckfree). We do
 *	this because the threaded memory allocator MAY use the thread storage
 *	hash tables.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */

static void
FreeThreadStorageEntry(
    Tcl_HashEntry *hPtr)	/* Hash entry to free. */
{
    TclpSysFree((char *) hPtr);
}

/*
 *----------------------------------------------------------------------
 *
 * ThreadStorageGetHashTable --
 *
 *	This procedure returns a hash table pointer to be used for thread
 *	storage for the specified thread. This assumes that thread storage
 *	lock is held.
 *
 * Results:
 *	A hash table pointer for the specified thread, or NULL if the hash
 *	table has not been created yet.
 *
 * Side effects:
 *	May change an entry in the master thread storage cache to point to the
 *	specified thread and it's associated hash table.
 *
 *----------------------------------------------------------------------
 */

static Tcl_HashTable *
ThreadStorageGetHashTable(
    Tcl_ThreadId id)		/* Id of thread to get hash table for */
{
    int index = PTR2UINT(id) % STORAGE_CACHE_SLOTS;
    Tcl_HashEntry *hPtr;
    int isNew;

    /*
     * It's important that we pick up the hash table pointer BEFORE comparing
     * thread Id in case another thread is in the critical region changing
     * things out from under you.
     */

    Tcl_HashTable *hashTablePtr = threadStorageCache[index].hashTablePtr;

    if (threadStorageCache[index].id != id) {
	Tcl_MutexLock(&threadStorageLock);

	/*
	 * It's not in the cache, so we look it up...
	 */

	hPtr = Tcl_FindHashEntry(&threadStorageHashTable, (char *) id);

	if (hPtr != NULL) {
	    /*
	     * We found it, extract the hash table pointer.
	     */

	    hashTablePtr = Tcl_GetHashValue(hPtr);
	} else {
	    /*
	     * The thread specific hash table is not found.
	     */

	    hashTablePtr = NULL;
	}

	if (hashTablePtr == NULL) {
	    hashTablePtr = (Tcl_HashTable *)
		    TclpSysAlloc(sizeof(Tcl_HashTable), 0);

	    if (hashTablePtr == NULL) {
		Tcl_Panic("could not allocate thread specific hash table, "
			"TclpSysAlloc failed from ThreadStorageGetHashTable!");
	    }
	    Tcl_InitCustomHashTable(hashTablePtr, TCL_CUSTOM_TYPE_KEYS,
		    &tclThreadStorageHashKeyType);

	    /*
	     * Add new thread storage hash table to the master hash table.
	     */

	    hPtr = Tcl_CreateHashEntry(&threadStorageHashTable, (char *) id,
		    &isNew);

	    if (hPtr == NULL) {
		Tcl_Panic("Tcl_CreateHashEntry failed from "
			"ThreadStorageGetHashTable!");
	    }
	    Tcl_SetHashValue(hPtr, hashTablePtr);
	}

	/*
	 * Now, we put it in the cache since it is highly likely it will be
	 * needed again shortly.
	 */

	threadStorageCache[index].id = id;
	threadStorageCache[index].hashTablePtr = hashTablePtr;

	Tcl_MutexUnlock(&threadStorageLock);
    }

    return hashTablePtr;
}

/*
 *----------------------------------------------------------------------
 *
 * TclInitThreadStorage --
 *
 *	Initializes the thread storage allocator.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	This procedure initializes the master hash table that maps thread ID
 *	onto the individual index tables that map thread data key to thread
 *	data. It also creates a cache that enables fast lookup of the thread
 *	data block array for a recently executing thread without using
 *	spinlocks.
 *
 * This procedure is called from an extremely early point in Tcl's
 * initialization. In particular, it may not use ckalloc/ckfree because they
 * may depend on thread-local storage (it uses TclpSysAlloc and TclpSysFree
 * instead). It may not depend on synchronization primitives - but no threads
 * other than the master thread have yet been launched.
 *
 *----------------------------------------------------------------------
 */

void
TclInitThreadStorage(void)
{
    Tcl_InitCustomHashTable(&threadStorageHashTable, TCL_CUSTOM_TYPE_KEYS,
	    &tclThreadStorageHashKeyType);

    /*
     * We also initialize the cache.
     */

    memset((void*) &threadStorageCache, 0,
	    sizeof(ThreadStorage) * STORAGE_CACHE_SLOTS);

    /*
     * Now, we set the first value to be used for a thread data key.
     */

    nextThreadStorageKey = STORAGE_FIRST_KEY;
}

/*
 *----------------------------------------------------------------------
 *
 * TclpThreadDataKeyGet --
 *
 *	This procedure returns a pointer to a block of thread local storage.
 *
 * Results:
 *	A thread-specific pointer to the data structure, or NULL if the memory
 *	has not been assigned to this key for this thread.
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */

void *
TclpThreadDataKeyGet(
    Tcl_ThreadDataKey *keyPtr)	/* Identifier for the data chunk, really
				 * (int**) */
{
    Tcl_HashTable *hashTablePtr =
	    ThreadStorageGetHashTable(Tcl_GetCurrentThread());
    Tcl_HashEntry *hPtr = Tcl_FindHashEntry(hashTablePtr, (char *) keyPtr);

    if (hPtr == NULL) {
	return NULL;
    }
    return Tcl_GetHashValue(hPtr);
}

/*
 *----------------------------------------------------------------------
 *
 * TclpThreadDataKeySet --
 *
 *	This procedure sets the pointer to a block of thread local storage.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	Sets up the thread so future calls to TclpThreadDataKeyGet with this
 *	key will return the data pointer.
 *
 *----------------------------------------------------------------------
 */

void
TclpThreadDataKeySet(
    Tcl_ThreadDataKey *keyPtr,	/* Identifier for the data chunk, really
				 * (pthread_key_t **) */
    void *data)			/* Thread local storage */
{
    Tcl_HashTable *hashTablePtr;
    Tcl_HashEntry *hPtr;
    int dummy;

    hashTablePtr = ThreadStorageGetHashTable(Tcl_GetCurrentThread());
    hPtr = Tcl_CreateHashEntry(hashTablePtr, (char *)keyPtr, &dummy);

    Tcl_SetHashValue(hPtr, data);
}

/*
 *----------------------------------------------------------------------
 *
 * TclpFinalizeThreadDataThread --
 *
 *	This procedure cleans up the thread storage hash table for the
 *	current thread.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	Frees all associated thread storage, all hash table entries for
 *	the thread's thread storage, and the hash table itself.
 *
 *----------------------------------------------------------------------
 */

void
TclpFinalizeThreadDataThread(void)
{
    Tcl_ThreadId id = Tcl_GetCurrentThread();
				/* Id of the thread to finalize. */
    int index = PTR2UINT(id) % STORAGE_CACHE_SLOTS;
    Tcl_HashEntry *hPtr;	/* Hash entry for current thread in master
				 * table. */
    Tcl_HashTable* hashTablePtr;/* Pointer to the hash table holding TSD
				 * blocks for the current thread*/
    Tcl_HashSearch search;	/* Search object to walk the TSD blocks in the
				 * designated thread */
    Tcl_HashEntry *hPtr2;	/* Hash entry for a TSD block in the
				 * designated thread. */

    Tcl_MutexLock(&threadStorageLock);
    hPtr = Tcl_FindHashEntry(&threadStorageHashTable, (char*)id);
    if (hPtr == NULL) {
	hashTablePtr = NULL;
    } else {
	/*
	 * We found it, extract the hash table pointer.
	 */

	hashTablePtr = Tcl_GetHashValue(hPtr);
	Tcl_DeleteHashEntry(hPtr);

	/*
	 * Make sure cache entry for this thread is NULL.
	 */

	if (threadStorageCache[index].id == id) {
	    /*
	     * We do not step on another thread's cache entry. This is
	     * especially important if we are creating and exiting a lot of
	     * threads.
	     */

	    threadStorageCache[index].id = STORAGE_INVALID_THREAD;
	    threadStorageCache[index].hashTablePtr = NULL;
	}
    }
    Tcl_MutexUnlock(&threadStorageLock);

    /*
     * The thread's hash table has been extracted and removed from the master
     * hash table. Now clean up the thread.
     */

    if (hashTablePtr != NULL) {
	/*
	 * Free all TSD
	 */

	for (hPtr2 = Tcl_FirstHashEntry(hashTablePtr, &search); hPtr2 != NULL;
		hPtr2 = Tcl_NextHashEntry(&search)) {
	    void *blockPtr = Tcl_GetHashValue(hPtr2);

	    if (blockPtr != NULL) {
		/*
		 * The block itself was allocated in Tcl_GetThreadData using
		 * ckalloc; use ckfree to dispose of it.
		 */

		ckfree(blockPtr);
	    }
	}

	/*
	 * Delete thread specific hash table and free the struct.
	 */

	Tcl_DeleteHashTable(hashTablePtr);
	TclpSysFree((char *) hashTablePtr);
    }
}

/*
 *----------------------------------------------------------------------
 *
 * TclFinalizeThreadStorage --
 *
 *	This procedure cleans up the master thread storage hash table, all
 *	thread specific hash tables, and the thread storage cache.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	The master thread storage hash table and thread storage cache are
 *	reset to their initial (empty) state.
 *
 *----------------------------------------------------------------------
 */

void
TclFinalizeThreadStorage(void)
{
    Tcl_HashSearch search;	/* We need to hit every thread with this
				 * search. */
    Tcl_HashEntry *hPtr;	/* Hash entry for current thread in master
				 * table. */
    Tcl_MutexLock(&threadStorageLock);

    /*
     * We are going to delete the hash table for every thread now. This hash
     * table should be empty at this point, except for one entry for the
     * current thread.
     */

    for (hPtr = Tcl_FirstHashEntry(&threadStorageHashTable, &search);
	    hPtr != NULL; hPtr = Tcl_NextHashEntry(&search)) {
	Tcl_HashTable *hashTablePtr = Tcl_GetHashValue(hPtr);

	if (hashTablePtr != NULL) {
	    /*
	     * Delete thread specific hash table for the thread in question
	     * and free the struct.
	     */

	    Tcl_DeleteHashTable(hashTablePtr);
	    TclpSysFree((char *)hashTablePtr);
	}

	/*
	 * Delete thread specific entry from master hash table.
	 */

	Tcl_SetHashValue(hPtr, NULL);
    }

    Tcl_DeleteHashTable(&threadStorageHashTable);

    /*
     * Clear out the thread storage cache as well.
     */

    memset((void*) &threadStorageCache, 0,
	    sizeof(ThreadStorage) * STORAGE_CACHE_SLOTS);

    /*
     * Reset this to zero, it will be set to STORAGE_FIRST_KEY if the thread
     * storage subsystem gets reinitialized
     */

    nextThreadStorageKey = STORAGE_INVALID_KEY;

    Tcl_MutexUnlock(&threadStorageLock);
}

#else /* !defined(TCL_THREADS) */

/*
 * Stub functions for non-threaded builds
 */

void
TclInitThreadStorage(void)
{
}

void
TclpFinalizeThreadDataThread(void)
{
}

void
TclFinalizeThreadStorage(void)
{
}

#endif /* defined(TCL_THREADS) && defined(USE_THREAD_STORAGE) */

/*
 * Local Variables:
 * mode: c
 * c-basic-offset: 4
 * fill-column: 78
 * End:
 */
