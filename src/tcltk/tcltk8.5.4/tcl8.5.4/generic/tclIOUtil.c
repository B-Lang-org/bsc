/*
 * tclIOUtil.c --
 *
 *	This file contains the implementation of Tcl's generic filesystem
 *	code, which supports a pluggable filesystem architecture allowing both
 *	platform specific filesystems and 'virtual filesystems'. All
 *	filesystem access should go through the functions defined in this
 *	file. Most of this code was contributed by Vince Darley.
 *
 *	Parts of this file are based on code contributed by Karl Lehenbauer,
 *	Mark Diekhans and Peter da Silva.
 *
 * Copyright (c) 1991-1994 The Regents of the University of California.
 * Copyright (c) 1994-1997 Sun Microsystems, Inc.
 * Copyright (c) 2001-2004 Vincent Darley.
 *
 * See the file "license.terms" for information on usage and redistribution of
 * this file, and for a DISCLAIMER OF ALL WARRANTIES.
 *
 * RCS: @(#) $Id: tclIOUtil.c,v 1.151 2008/02/27 03:35:49 jenglish Exp $
 */

#include "tclInt.h"
#ifdef __WIN32__
#   include "tclWinInt.h"
#endif
#include "tclFileSystem.h"

/*
 * Prototypes for functions defined later in this file.
 */

static FilesystemRecord*FsGetFirstFilesystem(void);
static void		FsThrExitProc(ClientData cd);
static Tcl_Obj *	FsListMounts(Tcl_Obj *pathPtr, const char *pattern);
static void		FsAddMountsToGlobResult(Tcl_Obj *resultPtr,
			    Tcl_Obj *pathPtr, const char *pattern,
			    Tcl_GlobTypeData *types);
static void		FsUpdateCwd(Tcl_Obj *cwdObj, ClientData clientData);

#ifdef TCL_THREADS
static void		FsRecacheFilesystemList(void);
#endif

/*
 * These form part of the native filesystem support. They are needed here
 * because we have a few native filesystem functions (which are the same for
 * win/unix) in this file. There is no need to place them in tclInt.h, because
 * they are not (and should not be) used anywhere else.
 */

MODULE_SCOPE const char *		tclpFileAttrStrings[];
MODULE_SCOPE const TclFileAttrProcs	tclpFileAttrProcs[];

/*
 * The following functions are obsolete string based APIs, and should be
 * removed in a future release (Tcl 9 would be a good time).
 */


/* Obsolete */
int
Tcl_Stat(
    const char *path,		/* Path of file to stat (in current CP). */
    struct stat *oldStyleBuf)	/* Filled with results of stat call. */
{
    int ret;
    Tcl_StatBuf buf;
    Tcl_Obj *pathPtr = Tcl_NewStringObj(path,-1);

#ifndef TCL_WIDE_INT_IS_LONG
    Tcl_WideInt tmp1, tmp2;
#ifdef HAVE_ST_BLOCKS
    Tcl_WideInt tmp3;
#endif
#endif

    Tcl_IncrRefCount(pathPtr);
    ret = Tcl_FSStat(pathPtr, &buf);
    Tcl_DecrRefCount(pathPtr);
    if (ret != -1) {
#ifndef TCL_WIDE_INT_IS_LONG
# define OUT_OF_RANGE(x) \
	(((Tcl_WideInt)(x)) < Tcl_LongAsWide(LONG_MIN) || \
	 ((Tcl_WideInt)(x)) > Tcl_LongAsWide(LONG_MAX))
# define OUT_OF_URANGE(x) \
	(((Tcl_WideUInt)(x)) > ((Tcl_WideUInt)ULONG_MAX))

	/*
	 * Perform the result-buffer overflow check manually.
	 *
	 * Note that ino_t/ino64_t is unsigned...
	 *
	 * Workaround gcc warning of "comparison is always false due to limited range of
	 * data type" by assigning to tmp var of type Tcl_WideInt.
	 */

        tmp1 = (Tcl_WideInt) buf.st_ino;
        tmp2 = (Tcl_WideInt) buf.st_size;
#ifdef HAVE_ST_BLOCKS
        tmp3 = (Tcl_WideInt) buf.st_blocks;
#endif

	if (OUT_OF_URANGE(tmp1) || OUT_OF_RANGE(tmp2)
#ifdef HAVE_ST_BLOCKS
		|| OUT_OF_RANGE(tmp3)
#endif
	    ) {
#ifdef EFBIG
	    errno = EFBIG;
#else
#  ifdef EOVERFLOW
	    errno = EOVERFLOW;
#  else
#    error "What status should be returned for file size out of range?"
#  endif
#endif
	    return -1;
	}

#   undef OUT_OF_RANGE
#   undef OUT_OF_URANGE
#endif /* !TCL_WIDE_INT_IS_LONG */

	/*
	 * Copy across all supported fields, with possible type coercions on
	 * those fields that change between the normal and lf64 versions of
	 * the stat structure (on Solaris at least). This is slow when the
	 * structure sizes coincide, but that's what you get for using an
	 * obsolete interface.
	 */

	oldStyleBuf->st_mode	= buf.st_mode;
	oldStyleBuf->st_ino	= (ino_t) buf.st_ino;
	oldStyleBuf->st_dev	= buf.st_dev;
	oldStyleBuf->st_rdev	= buf.st_rdev;
	oldStyleBuf->st_nlink	= buf.st_nlink;
	oldStyleBuf->st_uid	= buf.st_uid;
	oldStyleBuf->st_gid	= buf.st_gid;
	oldStyleBuf->st_size	= (off_t) buf.st_size;
	oldStyleBuf->st_atime	= buf.st_atime;
	oldStyleBuf->st_mtime	= buf.st_mtime;
	oldStyleBuf->st_ctime	= buf.st_ctime;
#ifdef HAVE_ST_BLOCKS
	oldStyleBuf->st_blksize	= buf.st_blksize;
	oldStyleBuf->st_blocks	= (blkcnt_t) buf.st_blocks;
#endif
    }
    return ret;
}

/* Obsolete */
int
Tcl_Access(
    const char *path,		/* Path of file to access (in current CP). */
    int mode)			/* Permission setting. */
{
    int ret;
    Tcl_Obj *pathPtr = Tcl_NewStringObj(path,-1);

    Tcl_IncrRefCount(pathPtr);
    ret = Tcl_FSAccess(pathPtr,mode);
    Tcl_DecrRefCount(pathPtr);

    return ret;
}

/* Obsolete */
Tcl_Channel
Tcl_OpenFileChannel(
    Tcl_Interp *interp,		/* Interpreter for error reporting; can be
				 * NULL. */
    const char *path,		/* Name of file to open. */
    const char *modeString,	/* A list of POSIX open modes or a string such
				 * as "rw". */
    int permissions)		/* If the open involves creating a file, with
				 * what modes to create it? */
{
    Tcl_Channel ret;
    Tcl_Obj *pathPtr = Tcl_NewStringObj(path,-1);

    Tcl_IncrRefCount(pathPtr);
    ret = Tcl_FSOpenFileChannel(interp, pathPtr, modeString, permissions);
    Tcl_DecrRefCount(pathPtr);

    return ret;
}

/* Obsolete */
int
Tcl_Chdir(
    const char *dirName)
{
    int ret;
    Tcl_Obj *pathPtr = Tcl_NewStringObj(dirName,-1);
    Tcl_IncrRefCount(pathPtr);
    ret = Tcl_FSChdir(pathPtr);
    Tcl_DecrRefCount(pathPtr);
    return ret;
}

/* Obsolete */
char *
Tcl_GetCwd(
    Tcl_Interp *interp,
    Tcl_DString *cwdPtr)
{
    Tcl_Obj *cwd;
    cwd = Tcl_FSGetCwd(interp);
    if (cwd == NULL) {
	return NULL;
    } else {
	Tcl_DStringInit(cwdPtr);
	Tcl_DStringAppend(cwdPtr, Tcl_GetString(cwd), -1);
	Tcl_DecrRefCount(cwd);
	return Tcl_DStringValue(cwdPtr);
    }
}

/* Obsolete */
int
Tcl_EvalFile(
    Tcl_Interp *interp,		/* Interpreter in which to process file. */
    const char *fileName)	/* Name of file to process. Tilde-substitution
				 * will be performed on this name. */
{
    int ret;
    Tcl_Obj *pathPtr = Tcl_NewStringObj(fileName,-1);
    Tcl_IncrRefCount(pathPtr);
    ret = Tcl_FSEvalFile(interp, pathPtr);
    Tcl_DecrRefCount(pathPtr);
    return ret;
}

/*
 * The 3 hooks for Stat, Access and OpenFileChannel are obsolete. The
 * complete, general hooked filesystem APIs should be used instead. This
 * define decides whether to include the obsolete hooks and related code. If
 * these are removed, we'll also want to remove them from stubs/tclInt. The
 * only known users of these APIs are prowrap and mktclapp. New
 * code/extensions should not use them, since they do not provide as full
 * support as the full filesystem API.
 *
 * As soon as prowrap and mktclapp are updated to use the full filesystem
 * support, I suggest all these hooks are removed.
 */

#undef USE_OBSOLETE_FS_HOOKS

#ifdef USE_OBSOLETE_FS_HOOKS

/*
 * The following typedef declarations allow for hooking into the chain of
 * functions maintained for 'Tcl_Stat(...)', 'Tcl_Access(...)' &
 * 'Tcl_OpenFileChannel(...)'. Basically for each hookable function a linked
 * list is defined.
 */

typedef struct StatProc {
    TclStatProc_ *proc;		/* Function to process a 'stat()' call */
    struct StatProc *nextPtr;	/* The next 'stat()' function to call */
} StatProc;

typedef struct AccessProc {
    TclAccessProc_ *proc;	/* Function to process a 'access()' call */
    struct AccessProc *nextPtr;	/* The next 'access()' function to call */
} AccessProc;

typedef struct OpenFileChannelProc {
    TclOpenFileChannelProc_ *proc;
				/* Function to process a
				 * 'Tcl_OpenFileChannel()' call */
    struct OpenFileChannelProc *nextPtr;
				/* The next 'Tcl_OpenFileChannel()' function
				 * to call */
} OpenFileChannelProc;

/*
 * For each type of (obsolete) hookable function, a static node is declared to
 * hold the function pointer for the "built-in" routine (e.g. 'TclpStat(...)')
 * and the respective list is initialized as a pointer to that node.
 *
 * The "delete" functions (e.g. 'TclStatDeleteProc(...)') ensure that these
 * statically declared list entry cannot be inadvertently removed.
 *
 * This method avoids the need to call any sort of "initialization" function.
 *
 * All three lists are protected by a global obsoleteFsHookMutex.
 */

static StatProc *statProcList = NULL;
static AccessProc *accessProcList = NULL;
static OpenFileChannelProc *openFileChannelProcList = NULL;

TCL_DECLARE_MUTEX(obsoleteFsHookMutex)

#endif /* USE_OBSOLETE_FS_HOOKS */

/*
 * Declare the native filesystem support. These functions should be considered
 * private to Tcl, and should really not be called directly by any code other
 * than this file (i.e. neither by Tcl's core nor by extensions). Similarly,
 * the old string-based Tclp... native filesystem functions should not be
 * called.
 *
 * The correct API to use now is the Tcl_FS... set of functions, which ensure
 * correct and complete virtual filesystem support.
 *
 * We cannot make all of these static, since some of them are implemented in
 * the platform-specific directories.
 */

static Tcl_FSFilesystemSeparatorProc NativeFilesystemSeparator;
static Tcl_FSFreeInternalRepProc NativeFreeInternalRep;
static Tcl_FSFileAttrStringsProc NativeFileAttrStrings;
static Tcl_FSFileAttrsGetProc	NativeFileAttrsGet;
static Tcl_FSFileAttrsSetProc	NativeFileAttrsSet;

/*
 * The only reason these functions are not static is that they are either
 * called by code in the native (win/unix) directories or they are actually
 * implemented in those directories. They should simply not be called by code
 * outside Tcl's native filesystem core i.e. they should be considered
 * 'static' to Tcl's filesystem code (if we ever built the native filesystem
 * support into a separate code library, this could actually be enforced).
 */

Tcl_FSFilesystemPathTypeProc	TclpFilesystemPathType;
Tcl_FSInternalToNormalizedProc	TclpNativeToNormalized;
Tcl_FSStatProc			TclpObjStat;
Tcl_FSAccessProc		TclpObjAccess;
Tcl_FSMatchInDirectoryProc	TclpMatchInDirectory;
Tcl_FSChdirProc			TclpObjChdir;
Tcl_FSLstatProc			TclpObjLstat;
Tcl_FSCopyFileProc		TclpObjCopyFile;
Tcl_FSDeleteFileProc		TclpObjDeleteFile;
Tcl_FSRenameFileProc		TclpObjRenameFile;
Tcl_FSCreateDirectoryProc	TclpObjCreateDirectory;
Tcl_FSCopyDirectoryProc		TclpObjCopyDirectory;
Tcl_FSRemoveDirectoryProc	TclpObjRemoveDirectory;
Tcl_FSUnloadFileProc		TclpUnloadFile;
Tcl_FSLinkProc			TclpObjLink;
Tcl_FSListVolumesProc		TclpObjListVolumes;

/*
 * Define the native filesystem dispatch table. If necessary, it is ok to make
 * this non-static, but it should only be accessed by the functions actually
 * listed within it (or perhaps other helper functions of them). Anything
 * which is not part of this 'native filesystem implementation' should not be
 * delving inside here!
 */

Tcl_Filesystem tclNativeFilesystem = {
    "native",
    sizeof(Tcl_Filesystem),
    TCL_FILESYSTEM_VERSION_2,
    &TclNativePathInFilesystem,
    &TclNativeDupInternalRep,
    &NativeFreeInternalRep,
    &TclpNativeToNormalized,
    &TclNativeCreateNativeRep,
    &TclpObjNormalizePath,
    &TclpFilesystemPathType,
    &NativeFilesystemSeparator,
    &TclpObjStat,
    &TclpObjAccess,
    &TclpOpenFileChannel,
    &TclpMatchInDirectory,
    &TclpUtime,
#ifndef S_IFLNK
    NULL,
#else
    &TclpObjLink,
#endif /* S_IFLNK */
    &TclpObjListVolumes,
    &NativeFileAttrStrings,
    &NativeFileAttrsGet,
    &NativeFileAttrsSet,
    &TclpObjCreateDirectory,
    &TclpObjRemoveDirectory,
    &TclpObjDeleteFile,
    &TclpObjCopyFile,
    &TclpObjRenameFile,
    &TclpObjCopyDirectory,
    &TclpObjLstat,
    &TclpDlopen,
    /* Needs a cast since we're using version_2 */
    (Tcl_FSGetCwdProc *) &TclpGetNativeCwd,
    &TclpObjChdir
};

/*
 * Define the tail of the linked list. Note that for unconventional uses of
 * Tcl without a native filesystem, we may in the future wish to modify the
 * current approach of hard-coding the native filesystem in the lookup list
 * 'filesystemList' below.
 *
 * We initialize the record so that it thinks one file uses it. This means it
 * will never be freed.
 */

static FilesystemRecord nativeFilesystemRecord = {
    NULL,
    &tclNativeFilesystem,
    1,
    NULL
};

/*
 * This is incremented each time we modify the linked list of filesystems. Any
 * time it changes, all cached filesystem representations are suspect and must
 * be freed. For multithreading builds, change of the filesystem epoch will
 * trigger cache cleanup in all threads.
 */

static int theFilesystemEpoch = 0;

/*
 * Stores the linked list of filesystems. A 1:1 copy of this list is also
 * maintained in the TSD for each thread. This is to avoid synchronization
 * issues.
 */

static FilesystemRecord *filesystemList = &nativeFilesystemRecord;
TCL_DECLARE_MUTEX(filesystemMutex)

/*
 * Used to implement Tcl_FSGetCwd in a file-system independent way.
 */

static Tcl_Obj* cwdPathPtr = NULL;
static int cwdPathEpoch = 0;
static ClientData cwdClientData = NULL;
TCL_DECLARE_MUTEX(cwdMutex)

Tcl_ThreadDataKey tclFsDataKey;

/*
 * Declare fallback support function and information for Tcl_FSLoadFile
 */

static Tcl_FSUnloadFileProc	FSUnloadTempFile;

/*
 * One of these structures is used each time we successfully load a file from
 * a file system by way of making a temporary copy of the file on the native
 * filesystem. We need to store both the actual unloadProc/clientData
 * combination which was used, and the original and modified filenames, so
 * that we can correctly undo the entire operation when we want to unload the
 * code.
 */

typedef struct FsDivertLoad {
    Tcl_LoadHandle loadHandle;
    Tcl_FSUnloadFileProc *unloadProcPtr;
    Tcl_Obj *divertedFile;
    const Tcl_Filesystem *divertedFilesystem;
    ClientData divertedFileNativeRep;
} FsDivertLoad;

/*
 * Now move on to the basic filesystem implementation
 */

static void
FsThrExitProc(
    ClientData cd)
{
    ThreadSpecificData *tsdPtr = (ThreadSpecificData *) cd;
    FilesystemRecord *fsRecPtr = NULL, *tmpFsRecPtr = NULL;

    /*
     * Trash the cwd copy.
     */

    if (tsdPtr->cwdPathPtr != NULL) {
	Tcl_DecrRefCount(tsdPtr->cwdPathPtr);
	tsdPtr->cwdPathPtr = NULL;
    }
    if (tsdPtr->cwdClientData != NULL) {
	NativeFreeInternalRep(tsdPtr->cwdClientData);
    }

    /*
     * Trash the filesystems cache.
     */

    fsRecPtr = tsdPtr->filesystemList;
    while (fsRecPtr != NULL) {
	tmpFsRecPtr = fsRecPtr->nextPtr;
	if (--fsRecPtr->fileRefCount <= 0) {
	    ckfree((char *)fsRecPtr);
	}
	fsRecPtr = tmpFsRecPtr;
    }
    tsdPtr->initialized = 0;
}

int
TclFSCwdIsNative(void)
{
    ThreadSpecificData *tsdPtr = TCL_TSD_INIT(&tclFsDataKey);

    if (tsdPtr->cwdClientData != NULL) {
	return 1;
    } else {
	return 0;
    }
}

/*
 *----------------------------------------------------------------------
 *
 * TclFSCwdPointerEquals --
 *
 *	Check whether the current working directory is equal to the path
 *	given.
 *
 * Results:
 *	1 (equal) or 0 (un-equal) as appropriate.
 *
 * Side effects:
 *	If the paths are equal, but are not the same object, this method will
 *	modify the given pathPtrPtr to refer to the same object. In this case
 *	the object pointed to by pathPtrPtr will have its refCount
 *	decremented, and it will be adjusted to point to the cwd (with a new
 *	refCount).
 *
 *----------------------------------------------------------------------
 */

int
TclFSCwdPointerEquals(
    Tcl_Obj** pathPtrPtr)
{
    ThreadSpecificData *tsdPtr = TCL_TSD_INIT(&tclFsDataKey);

    Tcl_MutexLock(&cwdMutex);
    if (tsdPtr->cwdPathPtr == NULL
	    || tsdPtr->cwdPathEpoch != cwdPathEpoch) {
	if (tsdPtr->cwdPathPtr != NULL) {
	    Tcl_DecrRefCount(tsdPtr->cwdPathPtr);
	}
	if (tsdPtr->cwdClientData != NULL) {
	    NativeFreeInternalRep(tsdPtr->cwdClientData);
	}
	if (cwdPathPtr == NULL) {
	    tsdPtr->cwdPathPtr = NULL;
	} else {
	    tsdPtr->cwdPathPtr = Tcl_DuplicateObj(cwdPathPtr);
	    Tcl_IncrRefCount(tsdPtr->cwdPathPtr);
	}
	if (cwdClientData == NULL) {
	    tsdPtr->cwdClientData = NULL;
	} else {
	    tsdPtr->cwdClientData = TclNativeDupInternalRep(cwdClientData);
	}
	tsdPtr->cwdPathEpoch = cwdPathEpoch;
    }
    Tcl_MutexUnlock(&cwdMutex);

    if (tsdPtr->initialized == 0) {
	Tcl_CreateThreadExitHandler(FsThrExitProc, (ClientData) tsdPtr);
	tsdPtr->initialized = 1;
    }

    if (pathPtrPtr == NULL) {
	return (tsdPtr->cwdPathPtr == NULL);
    }

    if (tsdPtr->cwdPathPtr == *pathPtrPtr) {
	return 1;
    } else {
	int len1, len2;
	const char *str1, *str2;

	str1 = Tcl_GetStringFromObj(tsdPtr->cwdPathPtr, &len1);
	str2 = Tcl_GetStringFromObj(*pathPtrPtr, &len2);
	if (len1 == len2 && !strcmp(str1,str2)) {
	    /*
	     * They are equal, but different objects. Update so they will be
	     * the same object in the future.
	     */

	    Tcl_DecrRefCount(*pathPtrPtr);
	    *pathPtrPtr = tsdPtr->cwdPathPtr;
	    Tcl_IncrRefCount(*pathPtrPtr);
	    return 1;
	} else {
	    return 0;
	}
    }
}

#ifdef TCL_THREADS
static void
FsRecacheFilesystemList(void)
{
    ThreadSpecificData *tsdPtr = TCL_TSD_INIT(&tclFsDataKey);
    FilesystemRecord *fsRecPtr, *tmpFsRecPtr = NULL;

    /*
     * Trash the current cache.
     */

    fsRecPtr = tsdPtr->filesystemList;
    while (fsRecPtr != NULL) {
	tmpFsRecPtr = fsRecPtr->nextPtr;
	if (--fsRecPtr->fileRefCount <= 0) {
	    ckfree((char *)fsRecPtr);
	}
	fsRecPtr = tmpFsRecPtr;
    }
    tsdPtr->filesystemList = NULL;

    /*
     * Code below operates on shared data. We are already called under mutex
     * lock so we can safely proceed.
     *
     * Locate tail of the global filesystem list.
     */

    fsRecPtr = filesystemList;
    while (fsRecPtr != NULL) {
	tmpFsRecPtr = fsRecPtr;
	fsRecPtr = fsRecPtr->nextPtr;
    }

    /*
     * Refill the cache honouring the order.
     */

    fsRecPtr = tmpFsRecPtr;
    while (fsRecPtr != NULL) {
	tmpFsRecPtr = (FilesystemRecord *) ckalloc(sizeof(FilesystemRecord));
	*tmpFsRecPtr = *fsRecPtr;
	tmpFsRecPtr->nextPtr = tsdPtr->filesystemList;
	tmpFsRecPtr->prevPtr = NULL;
	if (tsdPtr->filesystemList) {
	    tsdPtr->filesystemList->prevPtr = tmpFsRecPtr;
	}
	tsdPtr->filesystemList = tmpFsRecPtr;
	fsRecPtr = fsRecPtr->prevPtr;
    }

    /*
     * Make sure the above gets released on thread exit.
     */

    if (tsdPtr->initialized == 0) {
	Tcl_CreateThreadExitHandler(FsThrExitProc, (ClientData) tsdPtr);
	tsdPtr->initialized = 1;
    }
}
#endif /* TCL_THREADS */

static FilesystemRecord *
FsGetFirstFilesystem(void)
{
    ThreadSpecificData *tsdPtr = TCL_TSD_INIT(&tclFsDataKey);
    FilesystemRecord *fsRecPtr;
#ifndef TCL_THREADS
    tsdPtr->filesystemEpoch = theFilesystemEpoch;
    fsRecPtr = filesystemList;
#else
    Tcl_MutexLock(&filesystemMutex);
    if (tsdPtr->filesystemList == NULL
	    || (tsdPtr->filesystemEpoch != theFilesystemEpoch)) {
	FsRecacheFilesystemList();
	tsdPtr->filesystemEpoch = theFilesystemEpoch;
    }
    Tcl_MutexUnlock(&filesystemMutex);
    fsRecPtr = tsdPtr->filesystemList;
#endif
    return fsRecPtr;
}

/*
 * The epoch can be changed both by filesystems being added or removed and by
 * env(HOME) changing.
 */

int
TclFSEpochOk(
    int filesystemEpoch)
{
    ThreadSpecificData *tsdPtr = TCL_TSD_INIT(&tclFsDataKey);
    (void) FsGetFirstFilesystem();
    return (filesystemEpoch == tsdPtr->filesystemEpoch);
}

/*
 * If non-NULL, clientData is owned by us and must be freed later.
 */

static void
FsUpdateCwd(
    Tcl_Obj *cwdObj,
    ClientData clientData)
{
    int len;
    char *str = NULL;
    ThreadSpecificData *tsdPtr = TCL_TSD_INIT(&tclFsDataKey);

    if (cwdObj != NULL) {
	str = Tcl_GetStringFromObj(cwdObj, &len);
    }

    Tcl_MutexLock(&cwdMutex);
    if (cwdPathPtr != NULL) {
	Tcl_DecrRefCount(cwdPathPtr);
    }
    if (cwdClientData != NULL) {
	NativeFreeInternalRep(cwdClientData);
    }

    if (cwdObj == NULL) {
	cwdPathPtr = NULL;
	cwdClientData = NULL;
    } else {
	/*
	 * This must be stored as string obj!
	 */

	cwdPathPtr = Tcl_NewStringObj(str, len);
    	Tcl_IncrRefCount(cwdPathPtr);
	cwdClientData = TclNativeDupInternalRep(clientData);
    }

    cwdPathEpoch++;
    tsdPtr->cwdPathEpoch = cwdPathEpoch;
    Tcl_MutexUnlock(&cwdMutex);

    if (tsdPtr->cwdPathPtr) {
	Tcl_DecrRefCount(tsdPtr->cwdPathPtr);
    }
    if (tsdPtr->cwdClientData) {
	NativeFreeInternalRep(tsdPtr->cwdClientData);
    }

    if (cwdObj == NULL) {
	tsdPtr->cwdPathPtr = NULL;
	tsdPtr->cwdClientData = NULL;
    } else {
	tsdPtr->cwdPathPtr = Tcl_NewStringObj(str, len);
	tsdPtr->cwdClientData = clientData;
	Tcl_IncrRefCount(tsdPtr->cwdPathPtr);
    }
}

/*
 *----------------------------------------------------------------------
 *
 * TclFinalizeFilesystem --
 *
 *	Clean up the filesystem. After this, calls to all Tcl_FS... functions
 *	will fail.
 *
 *	We will later call TclResetFilesystem to restore the FS to a pristine
 *	state.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	Frees any memory allocated by the filesystem.
 *
 *----------------------------------------------------------------------
 */

void
TclFinalizeFilesystem(void)
{
    FilesystemRecord *fsRecPtr;

    /*
     * Assumption that only one thread is active now. Otherwise we would need
     * to put various mutexes around this code.
     */

    if (cwdPathPtr != NULL) {
	Tcl_DecrRefCount(cwdPathPtr);
	cwdPathPtr = NULL;
	cwdPathEpoch = 0;
    }
    if (cwdClientData != NULL) {
	NativeFreeInternalRep(cwdClientData);
	cwdClientData = NULL;
    }

    /*
     * Remove all filesystems, freeing any allocated memory that is no longer
     * needed
     */

    fsRecPtr = filesystemList;
    while (fsRecPtr != NULL) {
	FilesystemRecord *tmpFsRecPtr = fsRecPtr->nextPtr;
	if (fsRecPtr->fileRefCount <= 0) {
	    /*
	     * The native filesystem is static, so we don't free it.
	     */

	    if (fsRecPtr->fsPtr != &tclNativeFilesystem) {
		ckfree((char *)fsRecPtr);
	    }
	}
	fsRecPtr = tmpFsRecPtr;
    }
    filesystemList = NULL;

    /*
     * Now filesystemList is NULL. This means that any attempt to use the
     * filesystem is likely to fail.
     */

#ifdef USE_OBSOLETE_FS_HOOKS
    statProcList = NULL;
    accessProcList = NULL;
    openFileChannelProcList = NULL;
#endif
#ifdef __WIN32__
    TclWinEncodingsCleanup();
#endif
}

/*
 *----------------------------------------------------------------------
 *
 * TclResetFilesystem --
 *
 *	Restore the filesystem to a pristine state.
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
TclResetFilesystem(void)
{
    filesystemList = &nativeFilesystemRecord;

    /*
     * Note, at this point, I believe nativeFilesystemRecord -> fileRefCount
     * should equal 1 and if not, we should try to track down the cause.
     */

#ifdef __WIN32__
    /*
     * Cleans up the win32 API filesystem proc lookup table. This must happen
     * very late in finalization so that deleting of copied dlls can occur.
     */

    TclWinResetInterfaces();
#endif
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_FSRegister --
 *
 *	Insert the filesystem function table at the head of the list of
 *	functions which are used during calls to all file-system operations.
 *	The filesystem will be added even if it is already in the list. (You
 *	can use Tcl_FSData to check if it is in the list, provided the
 *	ClientData used was not NULL).
 *
 *	Note that the filesystem handling is head-to-tail of the list. Each
 *	filesystem is asked in turn whether it can handle a particular
 *	request, until one of them says 'yes'. At that point no further
 *	filesystems are asked.
 *
 *	In particular this means if you want to add a diagnostic filesystem
 *	(which simply reports all fs activity), it must be at the head of the
 *	list: i.e. it must be the last registered.
 *
 * Results:
 *	Normally TCL_OK; TCL_ERROR if memory for a new node in the list could
 *	not be allocated.
 *
 * Side effects:
 *	Memory allocated and modifies the link list for filesystems.
 *
 *----------------------------------------------------------------------
 */

int
Tcl_FSRegister(
    ClientData clientData,	/* Client specific data for this fs */
    Tcl_Filesystem *fsPtr)	/* The filesystem record for the new fs. */
{
    FilesystemRecord *newFilesystemPtr;

    if (fsPtr == NULL) {
	return TCL_ERROR;
    }

    newFilesystemPtr = (FilesystemRecord *) ckalloc(sizeof(FilesystemRecord));

    newFilesystemPtr->clientData = clientData;
    newFilesystemPtr->fsPtr = fsPtr;

    /*
     * We start with a refCount of 1. If this drops to zero, then anyone is
     * welcome to ckfree us.
     */

    newFilesystemPtr->fileRefCount = 1;

    /*
     * Is this lock and wait strictly speaking necessary? Since any iterators
     * out there will have grabbed a copy of the head of the list and be
     * iterating away from that, if we add a new element to the head of the
     * list, it can't possibly have any effect on any of their loops. In fact
     * it could be better not to wait, since we are adjusting the filesystem
     * epoch, any cached representations calculated by existing iterators are
     * going to have to be thrown away anyway.
     *
     * However, since registering and unregistering filesystems is a very rare
     * action, this is not a very important point.
     */

    Tcl_MutexLock(&filesystemMutex);

    newFilesystemPtr->nextPtr = filesystemList;
    newFilesystemPtr->prevPtr = NULL;
    if (filesystemList) {
	filesystemList->prevPtr = newFilesystemPtr;
    }
    filesystemList = newFilesystemPtr;

    /*
     * Increment the filesystem epoch counter, since existing paths might
     * conceivably now belong to different filesystems.
     */

    theFilesystemEpoch++;
    Tcl_MutexUnlock(&filesystemMutex);

    return TCL_OK;
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_FSUnregister --
 *
 *	Remove the passed filesystem from the list of filesystem function
 *	tables. It also ensures that the built-in (native) filesystem is not
 *	removable, although we may wish to change that decision in the future
 *	to allow a smaller Tcl core, in which the native filesystem is not
 *	used at all (we could, say, initialise Tcl completely over a network
 *	connection).
 *
 * Results:
 *	TCL_OK if the function pointer was successfully removed, TCL_ERROR
 *	otherwise.
 *
 * Side effects:
 *	Memory may be deallocated (or will be later, once no "path" objects
 *	refer to this filesystem), but the list of registered filesystems is
 *	updated immediately.
 *
 *----------------------------------------------------------------------
 */

int
Tcl_FSUnregister(
    Tcl_Filesystem *fsPtr)	/* The filesystem record to remove. */
{
    int retVal = TCL_ERROR;
    FilesystemRecord *fsRecPtr;

    Tcl_MutexLock(&filesystemMutex);

    /*
     * Traverse the 'filesystemList' looking for the particular node whose
     * 'fsPtr' member matches 'fsPtr' and remove that one from the list.
     * Ensure that the "default" node cannot be removed.
     */

    fsRecPtr = filesystemList;
    while ((retVal == TCL_ERROR) && (fsRecPtr->fsPtr != &tclNativeFilesystem)) {
	if (fsRecPtr->fsPtr == fsPtr) {
	    if (fsRecPtr->prevPtr) {
		fsRecPtr->prevPtr->nextPtr = fsRecPtr->nextPtr;
	    } else {
		filesystemList = fsRecPtr->nextPtr;
	    }
	    if (fsRecPtr->nextPtr) {
		fsRecPtr->nextPtr->prevPtr = fsRecPtr->prevPtr;
	    }

	    /*
	     * Increment the filesystem epoch counter, since existing paths
	     * might conceivably now belong to different filesystems. This
	     * should also ensure that paths which have cached the filesystem
	     * which is about to be deleted do not reference that filesystem
	     * (which would of course lead to memory exceptions).
	     */

	    theFilesystemEpoch++;

	    fsRecPtr->fileRefCount--;
	    if (fsRecPtr->fileRefCount <= 0) {
		ckfree((char *)fsRecPtr);
	    }

	    retVal = TCL_OK;
	} else {
	    fsRecPtr = fsRecPtr->nextPtr;
	}
    }

    Tcl_MutexUnlock(&filesystemMutex);
    return retVal;
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_FSMatchInDirectory --
 *
 *	This routine is used by the globbing code to search a directory for
 *	all files which match a given pattern. The appropriate function for
 *	the filesystem to which pathPtr belongs will be called. If pathPtr
 *	does not belong to any filesystem and if it is NULL or the empty
 *	string, then we assume the pattern is to be matched in the current
 *	working directory. To avoid have the Tcl_FSMatchInDirectoryProc for
 *	each filesystem from having to deal with this issue, we create a
 *	pathPtr on the fly (equal to the cwd), and then remove it from the
 *	results returned. This makes filesystems easy to write, since they can
 *	assume the pathPtr passed to them is an ordinary path. In fact this
 *	means we could remove such special case handling from Tcl's native
 *	filesystems.
 *
 *	If 'pattern' is NULL, then pathPtr is assumed to be a fully specified
 *	path of a single file/directory which must be checked for existence
 *	and correct type.
 *
 * Results:
 *
 *	The return value is a standard Tcl result indicating whether an error
 *	occurred in globbing. Error messages are placed in interp, but good
 *	results are placed in the resultPtr given.
 *
 *	Recursive searches, e.g.
 *		glob -dir $dir -join * pkgIndex.tcl
 *	which must recurse through each directory matching '*' are handled
 *	internally by Tcl, by passing specific flags in a modified 'types'
 *	parameter. This means the actual filesystem only ever sees patterns
 *	which match in a single directory.
 *
 * Side effects:
 *	The interpreter may have an error message inserted into it.
 *
 *----------------------------------------------------------------------
 */

int
Tcl_FSMatchInDirectory(
    Tcl_Interp *interp,		/* Interpreter to receive error messages, but
                       		 * may be NULL. */
    Tcl_Obj *resultPtr,		/* List object to receive results. */
    Tcl_Obj *pathPtr,		/* Contains path to directory to search. */
    const char *pattern,	/* Pattern to match against. */
    Tcl_GlobTypeData *types)	/* Object containing list of acceptable types.
				 * May be NULL. In particular the directory
				 * flag is very important. */
{
    const Tcl_Filesystem *fsPtr;
    Tcl_Obj *cwd, *tmpResultPtr, **elemsPtr;
    int resLength, i, ret = -1;

    if (types != NULL && types->type & TCL_GLOB_TYPE_MOUNT) {
	/*
	 * We don't currently allow querying of mounts by external code (a
	 * valuable future step), so since we're the only function that
	 * actually knows about mounts, this means we're being called
	 * recursively by ourself. Return no matches.
	 */

	return TCL_OK;
    }

    if (pathPtr != NULL) {
	fsPtr = Tcl_FSGetFileSystemForPath(pathPtr);
    } else {
	fsPtr = NULL;
    }

    /*
     * Check if we've successfully mapped the path to a filesystem within
     * which to search.
     */

    if (fsPtr != NULL) {
	if (fsPtr->matchInDirectoryProc == NULL) {
	    Tcl_SetErrno(ENOENT);
	    return -1;
	}
	ret = (*fsPtr->matchInDirectoryProc)(interp, resultPtr, pathPtr,
		pattern, types);
	if (ret == TCL_OK && pattern != NULL) {
	    FsAddMountsToGlobResult(resultPtr, pathPtr, pattern, types);
	}
	return ret;
    }

    /*
     * If the path isn't empty, we have no idea how to match files in a
     * directory which belongs to no known filesystem
     */

    if (pathPtr != NULL && TclGetString(pathPtr)[0] != '\0') {
	Tcl_SetErrno(ENOENT);
	return -1;
    }

    /*
     * We have an empty or NULL path. This is defined to mean we must search
     * for files within the current 'cwd'. We therefore use that, but then
     * since the proc we call will return results which include the cwd we
     * must then trim it off the front of each path in the result. We choose
     * to deal with this here (in the generic code), since if we don't, every
     * single filesystem's implementation of Tcl_FSMatchInDirectory will have
     * to deal with it for us.
     */

    cwd = Tcl_FSGetCwd(NULL);
    if (cwd == NULL) {
	if (interp != NULL) {
	    Tcl_SetResult(interp, "glob couldn't determine "
		    "the current working directory", TCL_STATIC);
	}
	return TCL_ERROR;
    }

    fsPtr = Tcl_FSGetFileSystemForPath(cwd);
    if (fsPtr != NULL && fsPtr->matchInDirectoryProc != NULL) {
	TclNewObj(tmpResultPtr);
	Tcl_IncrRefCount(tmpResultPtr);
	ret = (*fsPtr->matchInDirectoryProc)(interp, tmpResultPtr, cwd,
		pattern, types);
	if (ret == TCL_OK) {
	    FsAddMountsToGlobResult(tmpResultPtr, cwd, pattern, types);

	    /*
	     * Note that we know resultPtr and tmpResultPtr are distinct.
	     */

	    ret = Tcl_ListObjGetElements(interp, tmpResultPtr,
		    &resLength, &elemsPtr);
	    for (i=0 ; ret==TCL_OK && i<resLength ; i++) {
		ret = Tcl_ListObjAppendElement(interp, resultPtr,
			TclFSMakePathRelative(interp, elemsPtr[i], cwd));
	    }
	}
	TclDecrRefCount(tmpResultPtr);
    }
    Tcl_DecrRefCount(cwd);
    return ret;
}

/*
 *----------------------------------------------------------------------
 *
 * FsAddMountsToGlobResult --
 *
 *	This routine is used by the globbing code to take the results of a
 *	directory listing and add any mounted paths to that listing. This is
 *	required so that simple things like 'glob *' merge mounts and listings
 *	correctly.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	Modifies the resultPtr.
 *
 *----------------------------------------------------------------------
 */

static void
FsAddMountsToGlobResult(
    Tcl_Obj *resultPtr,		/* The current list of matching paths; must
				 * not be shared! */
    Tcl_Obj *pathPtr,		/* The directory in question */
    const char *pattern,	/* Pattern to match against. */
    Tcl_GlobTypeData *types)	/* Object containing list of acceptable types.
				 * May be NULL. In particular the directory
				 * flag is very important. */
{
    int mLength, gLength, i;
    int dir = (types == NULL || (types->type & TCL_GLOB_TYPE_DIR));
    Tcl_Obj *mounts = FsListMounts(pathPtr, pattern);

    if (mounts == NULL) {
	return;
    }

    if (Tcl_ListObjLength(NULL, mounts, &mLength) != TCL_OK || mLength == 0) {
	goto endOfMounts;
    }
    if (Tcl_ListObjLength(NULL, resultPtr, &gLength) != TCL_OK) {
	goto endOfMounts;
    }
    for (i=0 ; i<mLength ; i++) {
	Tcl_Obj *mElt;
	int j;
	int found = 0;

	Tcl_ListObjIndex(NULL, mounts, i, &mElt);

	for (j=0 ; j<gLength ; j++) {
	    Tcl_Obj *gElt;

	    Tcl_ListObjIndex(NULL, resultPtr, j, &gElt);
	    if (Tcl_FSEqualPaths(mElt, gElt)) {
		found = 1;
		if (!dir) {
		    /*
		     * We don't want to list this.
		     */

		    Tcl_ListObjReplace(NULL, resultPtr, j, 1, 0, NULL);
		    gLength--;
		}
		break;		/* Break out of for loop */
	    }
	}
	if (!found && dir) {
	    Tcl_Obj *norm;
	    int len, mlen;

	    /*
	     * We know mElt is absolute normalized and lies inside pathPtr, so
	     * now we must add to the result the right representation of mElt,
	     * i.e. the representation which is relative to pathPtr.
	     */

	    norm = Tcl_FSGetNormalizedPath(NULL, pathPtr);
	    if (norm != NULL) {
		const char *path, *mount;

		mount = Tcl_GetStringFromObj(mElt, &mlen);
		path = Tcl_GetStringFromObj(norm, &len);
		if (path[len-1] == '/') {
		    /*
		     * Deal with the root of the volume.
		     */

		    len--;
		}
		len++; /* account for '/' in the mElt [Bug 1602539] */
		mElt = TclNewFSPathObj(pathPtr, mount + len, mlen - len);
		Tcl_ListObjAppendElement(NULL, resultPtr, mElt);
	    }
	    /*
	     * No need to increment gLength, since we don't want to compare
	     * mounts against mounts.
	     */
	}
    }

  endOfMounts:
    Tcl_DecrRefCount(mounts);
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_FSMountsChanged --
 *
 *	Notify the filesystem that the available mounted filesystems (or
 *	within any one filesystem type, the number or location of mount
 *	points) have changed.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	The global filesystem variable 'theFilesystemEpoch' is incremented.
 *	The effect of this is to make all cached path representations invalid.
 *	Clearly it should only therefore be called when it is really required!
 *	There are a few circumstances when it should be called:
 *
 *	(1) when a new filesystem is registered or unregistered. Strictly
 *	speaking this is only necessary if the new filesystem accepts file
 *	paths as is (normally the filesystem itself is really a shell which
 *	hasn't yet had any mount points established and so its
 *	'pathInFilesystem' proc will always fail). However, for safety, Tcl
 *	always calls this for you in these circumstances.
 *
 *	(2) when additional mount points are established inside any existing
 *	filesystem (except the native fs)
 *
 *	(3) when any filesystem (except the native fs) changes the list of
 *	available volumes.
 *
 *	(4) when the mapping from a string representation of a file to a full,
 *	normalized path changes. For example, if 'env(HOME)' is modified, then
 *	any path containing '~' will map to a different filesystem location.
 *	Therefore all such paths need to have their internal representation
 *	invalidated.
 *
 *	Tcl has no control over (2) and (3), so any registered filesystem must
 *	make sure it calls this function when those situations occur.
 *
 *	(Note: the reason for the exception in 2,3 for the native filesystem
 *	is that the native filesystem by default claims all unknown files even
 *	if it really doesn't understand them or if they don't exist).
 *
 *----------------------------------------------------------------------
 */

void
Tcl_FSMountsChanged(
    Tcl_Filesystem *fsPtr)
{
    /*
     * We currently don't do anything with this parameter. We could in the
     * future only invalidate files for this filesystem or otherwise take more
     * advanced action.
     */

    (void)fsPtr;

    /*
     * Increment the filesystem epoch counter, since existing paths might now
     * belong to different filesystems.
     */

    Tcl_MutexLock(&filesystemMutex);
    theFilesystemEpoch++;
    Tcl_MutexUnlock(&filesystemMutex);
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_FSData --
 *
 *	Retrieve the clientData field for the filesystem given, or NULL if
 *	that filesystem is not registered.
 *
 * Results:
 *	A clientData value, or NULL. Note that if the filesystem was
 *	registered with a NULL clientData field, this function will return
 *	that NULL value.
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */

ClientData
Tcl_FSData(
    Tcl_Filesystem *fsPtr) /* The filesystem record to query. */
{
    ClientData retVal = NULL;
    FilesystemRecord *fsRecPtr = FsGetFirstFilesystem();

    /*
     * Traverse the list of filesystems look for a particular one. If found,
     * return that filesystem's clientData (originally provided when calling
     * Tcl_FSRegister).
     */

    while ((retVal == NULL) && (fsRecPtr != NULL)) {
	if (fsRecPtr->fsPtr == fsPtr) {
	    retVal = fsRecPtr->clientData;
	}
	fsRecPtr = fsRecPtr->nextPtr;
    }

    return retVal;
}

/*
 *---------------------------------------------------------------------------
 *
 * TclFSNormalizeToUniquePath --
 *
 *	Takes a path specification containing no ../, ./ sequences, and
 *	converts it into a unique path for the given platform. On Unix, this
 *	means the path must be free of symbolic links/aliases, and on Windows
 *	it means we want the long form, with that long form's case-dependence
 *	(which gives us a unique, case-dependent path).
 *
 * Results:
 *	The pathPtr is modified in place. The return value is the last byte
 *	offset which was recognised in the path string.
 *
 * Side effects:
 *	None (beyond the memory allocation for the result).
 *
 * Special notes:
 *	If the filesystem-specific normalizePathProcs can re-introduce ../, ./
 *	sequences into the path, then this function will not return the
 *	correct result. This may be possible with symbolic links on unix.
 *
 *	Important assumption: if startAt is non-zero, it must point to a
 *	directory separator that we know exists and is already normalized (so
 *	it is important not to point to the char just after the separator).
 *
 *---------------------------------------------------------------------------
 */

int
TclFSNormalizeToUniquePath(
    Tcl_Interp *interp,		/* Used for error messages. */
    Tcl_Obj *pathPtr,		/* The path to normalize in place */
    int startAt,		/* Start at this char-offset */
    ClientData *clientDataPtr)	/* If we generated a complete normalized path
				 * for a given filesystem, we can optionally
				 * return an fs-specific clientdata here. */
{
    FilesystemRecord *fsRecPtr, *firstFsRecPtr;
    /* Ignore this variable */
    (void) clientDataPtr;

    /*
     * Call each of the "normalise path" functions in succession. This is a
     * special case, in which if we have a native filesystem handler, we call
     * it first. This is because the root of Tcl's filesystem is always a
     * native filesystem (i.e. '/' on unix is native).
     */

    firstFsRecPtr = FsGetFirstFilesystem();

    fsRecPtr = firstFsRecPtr;
    while (fsRecPtr != NULL) {
	if (fsRecPtr->fsPtr == &tclNativeFilesystem) {
	    Tcl_FSNormalizePathProc *proc = fsRecPtr->fsPtr->normalizePathProc;
	    if (proc != NULL) {
		startAt = (*proc)(interp, pathPtr, startAt);
	    }
	    break;
	}
	fsRecPtr = fsRecPtr->nextPtr;
    }

    fsRecPtr = firstFsRecPtr;
    while (fsRecPtr != NULL) {
	/*
	 * Skip the native system next time through.
	 */

	if (fsRecPtr->fsPtr != &tclNativeFilesystem) {
	    Tcl_FSNormalizePathProc *proc = fsRecPtr->fsPtr->normalizePathProc;
	    if (proc != NULL) {
		startAt = (*proc)(interp, pathPtr, startAt);
	    }

	    /*
	     * We could add an efficiency check like this:
	     *		if (retVal == length-of(pathPtr)) {break;}
	     * but there's not much benefit.
	     */
	}
	fsRecPtr = fsRecPtr->nextPtr;
    }

    return startAt;
}

/*
 *---------------------------------------------------------------------------
 *
 * TclGetOpenMode --
 *
 *	This routine is an obsolete, limited version of TclGetOpenModeEx()
 *	below. It exists only to satisfy any extensions imprudently using it
 *	via Tcl's internal stubs table.
 *
 * Results:
 *	Same as TclGetOpenModeEx().
 *
 * Side effects:
 *	Same as TclGetOpenModeEx().
 *
 *---------------------------------------------------------------------------
 */

int
TclGetOpenMode(
    Tcl_Interp *interp,		/* Interpreter to use for error reporting -
				 * may be NULL. */
    const char *modeString,	/* Mode string, e.g. "r+" or "RDONLY CREAT" */
    int *seekFlagPtr)		/* Set this to 1 if the caller should seek to
				 * EOF during the opening of the file. */
{
    int binary = 0;
    return TclGetOpenModeEx(interp, modeString, seekFlagPtr, &binary);
}

/*
 *---------------------------------------------------------------------------
 *
 * TclGetOpenModeEx --
 *
 *	Computes a POSIX mode mask for opening a file, from a given string,
 *	and also sets flags to indicate whether the caller should seek to EOF
 *	after opening the file, and whether the caller should configure the
 *	channel for binary data.
 *
 * Results:
 *	On success, returns mode to pass to "open". If an error occurs, the
 *	return value is -1 and if interp is not NULL, sets interp's result
 *	object to an error message.
 *
 * Side effects:
 *	Sets the integer referenced by seekFlagPtr to 1 to tell the caller to
 *	seek to EOF after opening the file, or to 0 otherwise. Sets the
 *	integer referenced by binaryPtr to 1 to tell the caller to seek to
 *	configure the channel for binary data, or to 0 otherwise.
 *
 * Special note:
 *	This code is based on a prototype implementation contributed by Mark
 *	Diekhans.
 *
 *---------------------------------------------------------------------------
 */

int
TclGetOpenModeEx(
    Tcl_Interp *interp,		/* Interpreter to use for error reporting -
				 * may be NULL. */
    const char *modeString,	/* Mode string, e.g. "r+" or "RDONLY CREAT" */
    int *seekFlagPtr,		/* Set this to 1 if the caller should seek to
				 * EOF during the opening of the file. */
    int *binaryPtr)		/* Set this to 1 if the caller should
				 * configure the opened channel for binary
				 * operations */
{
    int mode, modeArgc, c, i, gotRW;
    const char **modeArgv, *flag;
#define RW_MODES (O_RDONLY|O_WRONLY|O_RDWR)

    /*
     * Check for the simpler fopen-like access modes (e.g. "r"). They are
     * distinguished from the POSIX access modes by the presence of a
     * lower-case first letter.
     */

    *seekFlagPtr = 0;
    *binaryPtr = 0;
    mode = 0;

    /*
     * Guard against international characters before using byte oriented
     * routines.
     */

    if (!(modeString[0] & 0x80)
	    && islower(UCHAR(modeString[0]))) { /* INTL: ISO only. */
	switch (modeString[0]) {
	case 'r':
	    mode = O_RDONLY;
	    break;
	case 'w':
	    mode = O_WRONLY|O_CREAT|O_TRUNC;
	    break;
	case 'a':
	    /*
	     * Added O_APPEND for proper automatic seek-to-end-on-write by the
	     * OS. [Bug 680143]
	     */

	    mode = O_WRONLY|O_CREAT|O_APPEND;
	    *seekFlagPtr = 1;
	    break;
	default:
	    goto error;
	}
	i=1;
	while (i<3 && modeString[i]) {
	    if (modeString[i] == modeString[i-1]) {
		goto error;
	    }
	    switch (modeString[i++]) {
	    case '+':
		/*
		 * Must remove the O_APPEND flag so that the seek command
		 * works. [Bug 1773127]
		 */

		mode &= ~(O_RDONLY|O_WRONLY|O_APPEND);
		mode |= O_RDWR;
		break;
	    case 'b':
		*binaryPtr = 1;
		break;
	    default:
		goto error;
	    }
	}
	if (modeString[i] != 0) {
	    goto error;
	}
	return mode;

    error:
	*seekFlagPtr = 0;
	*binaryPtr = 0;
	if (interp != NULL) {
	    Tcl_AppendResult(interp, "illegal access mode \"", modeString,
		    "\"", NULL);
	}
	return -1;
    }

    /*
     * The access modes are specified using a list of POSIX modes such as
     * O_CREAT.
     *
     * IMPORTANT NOTE: We rely on Tcl_SplitList working correctly when a NULL
     * interpreter is passed in.
     */

    if (Tcl_SplitList(interp, modeString, &modeArgc, &modeArgv) != TCL_OK) {
	if (interp != NULL) {
	    Tcl_AddErrorInfo(interp,
		    "\n    while processing open access modes \"");
	    Tcl_AddErrorInfo(interp, modeString);
	    Tcl_AddErrorInfo(interp, "\"");
	}
	return -1;
    }

    gotRW = 0;
    for (i = 0; i < modeArgc; i++) {
	flag = modeArgv[i];
	c = flag[0];
	if ((c == 'R') && (strcmp(flag, "RDONLY") == 0)) {
	    mode = (mode & ~RW_MODES) | O_RDONLY;
	    gotRW = 1;
	} else if ((c == 'W') && (strcmp(flag, "WRONLY") == 0)) {
	    mode = (mode & ~RW_MODES) | O_WRONLY;
	    gotRW = 1;
	} else if ((c == 'R') && (strcmp(flag, "RDWR") == 0)) {
	    mode = (mode & ~RW_MODES) | O_RDWR;
	    gotRW = 1;
	} else if ((c == 'A') && (strcmp(flag, "APPEND") == 0)) {
	    mode |= O_APPEND;
	    *seekFlagPtr = 1;
	} else if ((c == 'C') && (strcmp(flag, "CREAT") == 0)) {
	    mode |= O_CREAT;
	} else if ((c == 'E') && (strcmp(flag, "EXCL") == 0)) {
	    mode |= O_EXCL;

	} else if ((c == 'N') && (strcmp(flag, "NOCTTY") == 0)) {
#ifdef O_NOCTTY
	    mode |= O_NOCTTY;
#else
	    if (interp != NULL) {
		Tcl_AppendResult(interp, "access mode \"", flag,
			"\" not supported by this system", NULL);
	    }
	    ckfree((char *) modeArgv);
	    return -1;
#endif

	} else if ((c == 'N') && (strcmp(flag, "NONBLOCK") == 0)) {
#ifdef O_NONBLOCK
	    mode |= O_NONBLOCK;
#else
	    if (interp != NULL) {
		Tcl_AppendResult(interp, "access mode \"", flag,
			"\" not supported by this system", NULL);
	    }
	    ckfree((char *) modeArgv);
	    return -1;
#endif

	} else if ((c == 'T') && (strcmp(flag, "TRUNC") == 0)) {
	    mode |= O_TRUNC;
	} else if ((c == 'B') && (strcmp(flag, "BINARY") == 0)) {
	    *binaryPtr = 1;
	} else {

	    if (interp != NULL) {
		Tcl_AppendResult(interp, "invalid access mode \"", flag,
			"\": must be RDONLY, WRONLY, RDWR, APPEND, BINARY, "
			"CREAT, EXCL, NOCTTY, NONBLOCK, or TRUNC", NULL);
	    }
	    ckfree((char *) modeArgv);
	    return -1;
	}
    }

    ckfree((char *) modeArgv);

    if (!gotRW) {
	if (interp != NULL) {
	    Tcl_AppendResult(interp, "access mode must include either"
		    " RDONLY, WRONLY, or RDWR", NULL);
	}
	return -1;
    }
    return mode;
}

/*
 * Tcl_FSEvalFile is Tcl_FSEvalFileEx without encoding argument.
 */

int
Tcl_FSEvalFile(
    Tcl_Interp *interp,		/* Interpreter in which to process file. */
    Tcl_Obj *pathPtr)		/* Path of file to process. Tilde-substitution
				 * will be performed on this name. */
{
    return Tcl_FSEvalFileEx(interp, pathPtr, NULL);
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_FSEvalFileEx --
 *
 *	Read in a file and process the entire file as one gigantic Tcl
 *	command.
 *
 * Results:
 *	A standard Tcl result, which is either the result of executing the
 *	file or an error indicating why the file couldn't be read.
 *
 * Side effects:
 *	Depends on the commands in the file. During the evaluation of the
 *	contents of the file, iPtr->scriptFile is made to point to pathPtr
 *	(the old value is cached and replaced when this function returns).
 *
 *----------------------------------------------------------------------
 */

int
Tcl_FSEvalFileEx(
    Tcl_Interp *interp,		/* Interpreter in which to process file. */
    Tcl_Obj *pathPtr,		/* Path of file to process. Tilde-substitution
				 * will be performed on this name. */
    const char *encodingName)	/* If non-NULL, then use this encoding for the
				 * file. NULL means use the system encoding. */
{
    int length, result = TCL_ERROR;
    Tcl_StatBuf statBuf;
    Tcl_Obj *oldScriptFile;
    Interp *iPtr;
    char *string;
    Tcl_Channel chan;
    Tcl_Obj *objPtr;

    if (Tcl_FSGetNormalizedPath(interp, pathPtr) == NULL) {
	return result;
    }

    if (Tcl_FSStat(pathPtr, &statBuf) == -1) {
	Tcl_SetErrno(errno);
	Tcl_AppendResult(interp, "couldn't read file \"",
		Tcl_GetString(pathPtr), "\": ", Tcl_PosixError(interp), NULL);
	return result;
    }
    chan = Tcl_FSOpenFileChannel(interp, pathPtr, "r", 0644);
    if (chan == (Tcl_Channel) NULL) {
	Tcl_ResetResult(interp);
	Tcl_AppendResult(interp, "couldn't read file \"",
		Tcl_GetString(pathPtr), "\": ", Tcl_PosixError(interp), NULL);
	return result;
    }

    /*
     * The eofchar is \32 (^Z). This is the usual on Windows, but we effect
     * this cross-platform to allow for scripted documents. [Bug: 2040]
     */

    Tcl_SetChannelOption(interp, chan, "-eofchar", "\32");

    /*
     * If the encoding is specified, set it for the channel. Else don't touch
     * it (and use the system encoding) Report error on unknown encoding.
     */

    if (encodingName != NULL) {
	if (Tcl_SetChannelOption(interp, chan, "-encoding", encodingName)
		!= TCL_OK) {
	    Tcl_Close(interp,chan);
	    return result;
	}
    }

    objPtr = Tcl_NewObj();
    Tcl_IncrRefCount(objPtr);
    if (Tcl_ReadChars(chan, objPtr, -1, 0) < 0) {
	Tcl_Close(interp, chan);
	Tcl_AppendResult(interp, "couldn't read file \"",
		Tcl_GetString(pathPtr), "\": ", Tcl_PosixError(interp), NULL);
	goto end;
    }

    if (Tcl_Close(interp, chan) != TCL_OK) {
	goto end;
    }

    iPtr = (Interp *) interp;
    oldScriptFile = iPtr->scriptFile;
    iPtr->scriptFile = pathPtr;
    Tcl_IncrRefCount(iPtr->scriptFile);
    string = Tcl_GetStringFromObj(objPtr, &length);
    /* TIP #280 Force the evaluator to open a frame for a sourced
     * file. */
    iPtr->evalFlags |= TCL_EVAL_FILE;
    result = Tcl_EvalEx(interp, string, length, 0);

    /*
     * Now we have to be careful; the script may have changed the
     * iPtr->scriptFile value, so we must reset it without assuming it still
     * points to 'pathPtr'.
     */

    if (iPtr->scriptFile != NULL) {
	Tcl_DecrRefCount(iPtr->scriptFile);
    }
    iPtr->scriptFile = oldScriptFile;

    if (result == TCL_RETURN) {
	result = TclUpdateReturnInfo(iPtr);
    } else if (result == TCL_ERROR) {
	/*
	 * Record information telling where the error occurred.
	 */

	const char *pathString = Tcl_GetStringFromObj(pathPtr, &length);
	int limit = 150;
	int overflow = (length > limit);

	Tcl_AppendObjToErrorInfo(interp, Tcl_ObjPrintf(
		"\n    (file \"%.*s%s\" line %d)",
		(overflow ? limit : length), pathString,
		(overflow ? "..." : ""), interp->errorLine));
    }

  end:
    Tcl_DecrRefCount(objPtr);
    return result;
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_GetErrno --
 *
 *	Gets the current value of the Tcl error code variable. This is
 *	currently the global variable "errno" but could in the future change
 *	to something else.
 *
 * Results:
 *	The value of the Tcl error code variable.
 *
 * Side effects:
 *	None. Note that the value of the Tcl error code variable is UNDEFINED
 *	if a call to Tcl_SetErrno did not precede this call.
 *
 *----------------------------------------------------------------------
 */

int
Tcl_GetErrno(void)
{
    return errno;
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_SetErrno --
 *
 *	Sets the Tcl error code variable to the supplied value.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	Modifies the value of the Tcl error code variable.
 *
 *----------------------------------------------------------------------
 */

void
Tcl_SetErrno(
    int err)			/* The new value. */
{
    errno = err;
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_PosixError --
 *
 *	This function is typically called after UNIX kernel calls return
 *	errors. It stores machine-readable information about the error in
 *	errorCode field of interp and returns an information string for the
 *	caller's use.
 *
 * Results:
 *	The return value is a human-readable string describing the error.
 *
 * Side effects:
 *	The errorCode field of the interp is set.
 *
 *----------------------------------------------------------------------
 */

const char *
Tcl_PosixError(
    Tcl_Interp *interp)		/* Interpreter whose errorCode field is to be
				 * set. */
{
    const char *id, *msg;

    msg = Tcl_ErrnoMsg(errno);
    id = Tcl_ErrnoId();
    if (interp) {
	Tcl_SetErrorCode(interp, "POSIX", id, msg, NULL);
    }
    return msg;
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_FSStat --
 *
 *	This function replaces the library version of stat and lsat.
 *
 *	The appropriate function for the filesystem to which pathPtr belongs
 *	will be called.
 *
 * Results:
 *	See stat documentation.
 *
 * Side effects:
 *	See stat documentation.
 *
 *----------------------------------------------------------------------
 */

int
Tcl_FSStat(
    Tcl_Obj *pathPtr,		/* Path of file to stat (in current CP). */
    Tcl_StatBuf *buf)		/* Filled with results of stat call. */
{
    const Tcl_Filesystem *fsPtr;
#ifdef USE_OBSOLETE_FS_HOOKS
    struct stat oldStyleStatBuffer;
    int retVal = -1;

    /*
     * Call each of the "stat" function in succession. A non-return value of
     * -1 indicates the particular function has succeeded.
     */

    Tcl_MutexLock(&obsoleteFsHookMutex);

    if (statProcList != NULL) {
	StatProc *statProcPtr;
	char *path;
	Tcl_Obj *transPtr = Tcl_FSGetTranslatedPath(NULL, pathPtr);
	if (transPtr == NULL) {
	    path = NULL;
	} else {
	    path = Tcl_GetString(transPtr);
	}

	statProcPtr = statProcList;
	while ((retVal == -1) && (statProcPtr != NULL)) {
	    retVal = (*statProcPtr->proc)(path, &oldStyleStatBuffer);
	    statProcPtr = statProcPtr->nextPtr;
	}
	if (transPtr != NULL) {
	    Tcl_DecrRefCount(transPtr);
	}
    }

    Tcl_MutexUnlock(&obsoleteFsHookMutex);
    if (retVal != -1) {
	/*
	 * Note that EOVERFLOW is not a problem here, and these assignments
	 * should all be widening (if not identity.)
	 */

	buf->st_mode = oldStyleStatBuffer.st_mode;
	buf->st_ino = oldStyleStatBuffer.st_ino;
	buf->st_dev = oldStyleStatBuffer.st_dev;
	buf->st_rdev = oldStyleStatBuffer.st_rdev;
	buf->st_nlink = oldStyleStatBuffer.st_nlink;
	buf->st_uid = oldStyleStatBuffer.st_uid;
	buf->st_gid = oldStyleStatBuffer.st_gid;
	buf->st_size = Tcl_LongAsWide(oldStyleStatBuffer.st_size);
	buf->st_atime = oldStyleStatBuffer.st_atime;
	buf->st_mtime = oldStyleStatBuffer.st_mtime;
	buf->st_ctime = oldStyleStatBuffer.st_ctime;
#ifdef HAVE_ST_BLOCKS
	buf->st_blksize = oldStyleStatBuffer.st_blksize;
	buf->st_blocks = Tcl_LongAsWide(oldStyleStatBuffer.st_blocks);
#endif
	return retVal;
    }
#endif /* USE_OBSOLETE_FS_HOOKS */

    fsPtr = Tcl_FSGetFileSystemForPath(pathPtr);
    if (fsPtr != NULL) {
	Tcl_FSStatProc *proc = fsPtr->statProc;
	if (proc != NULL) {
	    return (*proc)(pathPtr, buf);
	}
    }
    Tcl_SetErrno(ENOENT);
    return -1;
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_FSLstat --
 *
 *	This function replaces the library version of lstat. The appropriate
 *	function for the filesystem to which pathPtr belongs will be called.
 *	If no 'lstat' function is listed, but a 'stat' function is, then Tcl
 *	will fall back on the stat function.
 *
 * Results:
 *	See lstat documentation.
 *
 * Side effects:
 *	See lstat documentation.
 *
 *----------------------------------------------------------------------
 */

int
Tcl_FSLstat(
    Tcl_Obj *pathPtr,		/* Path of file to stat (in current CP). */
    Tcl_StatBuf *buf)		/* Filled with results of stat call. */
{
    const Tcl_Filesystem *fsPtr = Tcl_FSGetFileSystemForPath(pathPtr);
    if (fsPtr != NULL) {
	Tcl_FSLstatProc *proc = fsPtr->lstatProc;
	if (proc != NULL) {
	    return (*proc)(pathPtr, buf);
	} else {
	    Tcl_FSStatProc *sproc = fsPtr->statProc;
	    if (sproc != NULL) {
		return (*sproc)(pathPtr, buf);
	    }
	}
    }
    Tcl_SetErrno(ENOENT);
    return -1;
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_FSAccess --
 *
 *	This function replaces the library version of access. The appropriate
 *	function for the filesystem to which pathPtr belongs will be called.
 *
 * Results:
 *	See access documentation.
 *
 * Side effects:
 *	See access documentation.
 *
 *----------------------------------------------------------------------
 */

int
Tcl_FSAccess(
    Tcl_Obj *pathPtr,		/* Path of file to access (in current CP). */
    int mode)			/* Permission setting. */
{
    const Tcl_Filesystem *fsPtr;
#ifdef USE_OBSOLETE_FS_HOOKS
    int retVal = -1;

    /*
     * Call each of the "access" function in succession. A non-return value of
     * -1 indicates the particular function has succeeded.
     */

    Tcl_MutexLock(&obsoleteFsHookMutex);

    if (accessProcList != NULL) {
	AccessProc *accessProcPtr;
	char *path;
	Tcl_Obj *transPtr = Tcl_FSGetTranslatedPath(NULL, pathPtr);
	if (transPtr == NULL) {
	    path = NULL;
	} else {
	    path = Tcl_GetString(transPtr);
	}

	accessProcPtr = accessProcList;
	while ((retVal == -1) && (accessProcPtr != NULL)) {
	    retVal = (*accessProcPtr->proc)(path, mode);
	    accessProcPtr = accessProcPtr->nextPtr;
	}
	if (transPtr != NULL) {
	    Tcl_DecrRefCount(transPtr);
	}
    }

    Tcl_MutexUnlock(&obsoleteFsHookMutex);
    if (retVal != -1) {
	return retVal;
    }
#endif /* USE_OBSOLETE_FS_HOOKS */

    fsPtr = Tcl_FSGetFileSystemForPath(pathPtr);
    if (fsPtr != NULL) {
	Tcl_FSAccessProc *proc = fsPtr->accessProc;
	if (proc != NULL) {
	    return (*proc)(pathPtr, mode);
	}
    }

    Tcl_SetErrno(ENOENT);
    return -1;
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_FSOpenFileChannel --
 *
 *	The appropriate function for the filesystem to which pathPtr belongs
 *	will be called.
 *
 * Results:
 *	The new channel or NULL, if the named file could not be opened.
 *
 * Side effects:
 *	May open the channel and may cause creation of a file on the file
 *	system.
 *
 *----------------------------------------------------------------------
 */

Tcl_Channel
Tcl_FSOpenFileChannel(
    Tcl_Interp *interp,		/* Interpreter for error reporting; can be
				 * NULL. */
    Tcl_Obj *pathPtr,		/* Name of file to open. */
    const char *modeString,	/* A list of POSIX open modes or a string such
				 * as "rw". */
    int permissions)		/* If the open involves creating a file, with
				 * what modes to create it? */
{
    const Tcl_Filesystem *fsPtr;
    Tcl_Channel retVal = NULL;

#ifdef USE_OBSOLETE_FS_HOOKS
    /*
     * Call each of the "Tcl_OpenFileChannel" functions in succession. A
     * non-NULL return value indicates the particular function has succeeded.
     */

    Tcl_MutexLock(&obsoleteFsHookMutex);
    if (openFileChannelProcList != NULL) {
	OpenFileChannelProc *openFileChannelProcPtr;
	char *path;
	Tcl_Obj *transPtr = Tcl_FSGetTranslatedPath(interp, pathPtr);

	if (transPtr == NULL) {
	    path = NULL;
	} else {
	    path = Tcl_GetString(transPtr);
	}

	openFileChannelProcPtr = openFileChannelProcList;

	while ((retVal == NULL) && (openFileChannelProcPtr != NULL)) {
	    retVal = (*openFileChannelProcPtr->proc)(interp, path,
		    modeString, permissions);
	    openFileChannelProcPtr = openFileChannelProcPtr->nextPtr;
	}
	if (transPtr != NULL) {
	    Tcl_DecrRefCount(transPtr);
	}
    }
    Tcl_MutexUnlock(&obsoleteFsHookMutex);
    if (retVal != NULL) {
	return retVal;
    }
#endif /* USE_OBSOLETE_FS_HOOKS */

    /*
     * We need this just to ensure we return the correct error messages under
     * some circumstances.
     */

    if (Tcl_FSGetNormalizedPath(interp, pathPtr) == NULL) {
	return NULL;
    }

    fsPtr = Tcl_FSGetFileSystemForPath(pathPtr);
    if (fsPtr != NULL) {
	Tcl_FSOpenFileChannelProc *proc = fsPtr->openFileChannelProc;
	if (proc != NULL) {
	    int mode, seekFlag, binary;

	    /*
	     * Parse the mode, picking up whether we want to seek to start
	     * with and/or set the channel automatically into binary mode.
	     */

	    mode = TclGetOpenModeEx(interp, modeString, &seekFlag, &binary);
	    if (mode == -1) {
		return NULL;
	    }

	    /*
	     * Do the actual open() call.
	     */

	    retVal = (*proc)(interp, pathPtr, mode, permissions);
	    if (retVal == NULL) {
		return NULL;
	    }

	    /*
	     * Apply appropriate flags parsed out above.
	     */

	    if (seekFlag && Tcl_Seek(retVal, (Tcl_WideInt)0,
		    SEEK_END) < (Tcl_WideInt)0) {
		if (interp != NULL) {
		    Tcl_AppendResult(interp, "could not seek to end "
			    "of file while opening \"", Tcl_GetString(pathPtr),
			    "\": ", Tcl_PosixError(interp), NULL);
		}
		Tcl_Close(NULL, retVal);
		return NULL;
	    }
	    if (binary) {
		Tcl_SetChannelOption(interp, retVal, "-translation", "binary");
	    }
	    return retVal;
	}
    }

    /*
     * File doesn't belong to any filesystem that can open it.
     */

    Tcl_SetErrno(ENOENT);
    if (interp != NULL) {
	Tcl_AppendResult(interp, "couldn't open \"", Tcl_GetString(pathPtr),
		"\": ", Tcl_PosixError(interp), NULL);
    }
    return NULL;
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_FSUtime --
 *
 *	This function replaces the library version of utime. The appropriate
 *	function for the filesystem to which pathPtr belongs will be called.
 *
 * Results:
 *	See utime documentation.
 *
 * Side effects:
 *	See utime documentation.
 *
 *----------------------------------------------------------------------
 */

int
Tcl_FSUtime(
    Tcl_Obj *pathPtr,		/* File to change access/modification times */
    struct utimbuf *tval)	/* Structure containing access/modification
				 * times to use. Should not be modified. */
{
    const Tcl_Filesystem *fsPtr = Tcl_FSGetFileSystemForPath(pathPtr);
    if (fsPtr != NULL) {
	Tcl_FSUtimeProc *proc = fsPtr->utimeProc;
	if (proc != NULL) {
	    return (*proc)(pathPtr, tval);
	}
    }
    return -1;
}

/*
 *----------------------------------------------------------------------
 *
 * NativeFileAttrStrings --
 *
 *	This function implements the platform dependent 'file attributes'
 *	subcommand, for the native filesystem, for listing the set of possible
 *	attribute strings. This function is part of Tcl's native filesystem
 *	support, and is placed here because it is shared by Unix and Windows
 *	code.
 *
 * Results:
 *	An array of strings
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */

static const char **
NativeFileAttrStrings(
    Tcl_Obj *pathPtr,
    Tcl_Obj **objPtrRef)
{
    return tclpFileAttrStrings;
}

/*
 *----------------------------------------------------------------------
 *
 * NativeFileAttrsGet --
 *
 *	This function implements the platform dependent 'file attributes'
 *	subcommand, for the native filesystem, for 'get' operations. This
 *	function is part of Tcl's native filesystem support, and is placed
 *	here because it is shared by Unix and Windows code.
 *
 * Results:
 *	Standard Tcl return code. The object placed in objPtrRef (if TCL_OK
 *	was returned) is likely to have a refCount of zero. Either way we must
 *	either store it somewhere (e.g. the Tcl result), or Incr/Decr its
 *	refCount to ensure it is properly freed.
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */

static int
NativeFileAttrsGet(
    Tcl_Interp *interp,		/* The interpreter for error reporting. */
    int index,			/* index of the attribute command. */
    Tcl_Obj *pathPtr,		/* path of file we are operating on. */
    Tcl_Obj **objPtrRef)	/* for output. */
{
    return (*tclpFileAttrProcs[index].getProc)(interp, index, pathPtr,
	    objPtrRef);
}

/*
 *----------------------------------------------------------------------
 *
 * NativeFileAttrsSet --
 *
 *	This function implements the platform dependent 'file attributes'
 *	subcommand, for the native filesystem, for 'set' operations. This
 *	function is part of Tcl's native filesystem support, and is placed
 *	here because it is shared by Unix and Windows code.
 *
 * Results:
 *	Standard Tcl return code.
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */

static int
NativeFileAttrsSet(
    Tcl_Interp *interp,		/* The interpreter for error reporting. */
    int index,			/* index of the attribute command. */
    Tcl_Obj *pathPtr,		/* path of file we are operating on. */
    Tcl_Obj *objPtr)		/* set to this value. */
{
    return (*tclpFileAttrProcs[index].setProc)(interp, index, pathPtr, objPtr);
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_FSFileAttrStrings --
 *
 *	This function implements part of the hookable 'file attributes'
 *	subcommand. The appropriate function for the filesystem to which
 *	pathPtr belongs will be called.
 *
 * Results:
 *	The called function may either return an array of strings, or may
 *	instead return NULL and place a Tcl list into the given objPtrRef.
 *	Tcl will take that list and first increment its refCount before using
 *	it. On completion of that use, Tcl will decrement its refCount. Hence
 *	if the list should be disposed of by Tcl when done, it should have a
 *	refCount of zero, and if the list should not be disposed of, the
 *	filesystem should ensure it retains a refCount on the object.
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */

const char **
Tcl_FSFileAttrStrings(
    Tcl_Obj *pathPtr,
    Tcl_Obj **objPtrRef)
{
    const Tcl_Filesystem *fsPtr = Tcl_FSGetFileSystemForPath(pathPtr);

    if (fsPtr != NULL) {
	Tcl_FSFileAttrStringsProc *proc = fsPtr->fileAttrStringsProc;
	if (proc != NULL) {
	    return (*proc)(pathPtr, objPtrRef);
	}
    }
    Tcl_SetErrno(ENOENT);
    return NULL;
}

/*
 *----------------------------------------------------------------------
 *
 * TclFSFileAttrIndex --
 *
 *	Helper function for converting an attribute name to an index into the
 *	attribute table.
 *
 * Results:
 *	Tcl result code, index written to *indexPtr on result==TCL_OK
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */

int
TclFSFileAttrIndex(
    Tcl_Obj *pathPtr,		/* File whose attributes are to be indexed
				 * into. */
    const char *attributeName,	/* The attribute being looked for. */
    int *indexPtr)		/* Where to write the found index. */
{
    Tcl_Obj *listObj = NULL;
    const char **attrTable;

    /*
     * Get the attribute table for the file.
     */

    attrTable = Tcl_FSFileAttrStrings(pathPtr, &listObj);
    if (listObj != NULL) {
	Tcl_IncrRefCount(listObj);
    }

    if (attrTable != NULL) {
	/*
	 * It's a constant attribute table, so use T_GIFO.
	 */

	Tcl_Obj *tmpObj = Tcl_NewStringObj(attributeName, -1);
	int result;

	result = Tcl_GetIndexFromObj(NULL, tmpObj, attrTable, NULL, TCL_EXACT,
		indexPtr);
	TclDecrRefCount(tmpObj);
	if (listObj != NULL) {
	    TclDecrRefCount(listObj);
	}
	return result;
    } else if (listObj != NULL) {
	/*
	 * It's a non-constant attribute list, so do a literal search.
	 */

	int i, objc;
	Tcl_Obj **objv;

	if (Tcl_ListObjGetElements(NULL, listObj, &objc, &objv) != TCL_OK) {
	    TclDecrRefCount(listObj);
	    return TCL_ERROR;
	}
	for (i=0 ; i<objc ; i++) {
	    if (!strcmp(attributeName, TclGetString(objv[i]))) {
		TclDecrRefCount(listObj);
		*indexPtr = i;
		return TCL_OK;
	    }
	}
	TclDecrRefCount(listObj);
	return TCL_ERROR;
    } else {
	return TCL_ERROR;
    }
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_FSFileAttrsGet --
 *
 *	This function implements read access for the hookable 'file
 *	attributes' subcommand. The appropriate function for the filesystem to
 *	which pathPtr belongs will be called.
 *
 * Results:
 *	Standard Tcl return code. The object placed in objPtrRef (if TCL_OK
 *	was returned) is likely to have a refCount of zero. Either way we must
 *	either store it somewhere (e.g. the Tcl result), or Incr/Decr its
 *	refCount to ensure it is properly freed.
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */

int
Tcl_FSFileAttrsGet(
    Tcl_Interp *interp,		/* The interpreter for error reporting. */
    int index,			/* index of the attribute command. */
    Tcl_Obj *pathPtr,		/* filename we are operating on. */
    Tcl_Obj **objPtrRef)	/* for output. */
{
    const Tcl_Filesystem *fsPtr = Tcl_FSGetFileSystemForPath(pathPtr);

    if (fsPtr != NULL) {
	Tcl_FSFileAttrsGetProc *proc = fsPtr->fileAttrsGetProc;
	if (proc != NULL) {
	    return (*proc)(interp, index, pathPtr, objPtrRef);
	}
    }
    Tcl_SetErrno(ENOENT);
    return -1;
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_FSFileAttrsSet --
 *
 *	This function implements write access for the hookable 'file
 *	attributes' subcommand. The appropriate function for the filesystem to
 *	which pathPtr belongs will be called.
 *
 * Results:
 *	Standard Tcl return code.
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */

int
Tcl_FSFileAttrsSet(
    Tcl_Interp *interp,		/* The interpreter for error reporting. */
    int index,			/* index of the attribute command. */
    Tcl_Obj *pathPtr,		/* filename we are operating on. */
    Tcl_Obj *objPtr)		/* Input value. */
{
    const Tcl_Filesystem *fsPtr = Tcl_FSGetFileSystemForPath(pathPtr);

    if (fsPtr != NULL) {
	Tcl_FSFileAttrsSetProc *proc = fsPtr->fileAttrsSetProc;
	if (proc != NULL) {
	    return (*proc)(interp, index, pathPtr, objPtr);
	}
    }
    Tcl_SetErrno(ENOENT);
    return -1;
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_FSGetCwd --
 *
 *	This function replaces the library version of getcwd().
 *
 *	Most VFS's will *not* implement a 'cwdProc'. Tcl now maintains its own
 *	record (in a Tcl_Obj) of the cwd, and an attempt is made to synch this
 *	with the cwd's containing filesystem, if that filesystem provides a
 *	cwdProc (e.g. the native filesystem).
 *
 *	Note that if Tcl's cwd is not in the native filesystem, then of course
 *	Tcl's cwd and the native cwd are different: extensions should
 *	therefore ensure they only access the cwd through this function to
 *	avoid confusion.
 *
 *	If a global cwdPathPtr already exists, it is cached in the thread's
 *	private data structures and reference to the cached copy is returned,
 *	subject to a synchronisation attempt in that cwdPathPtr's fs.
 *
 *	Otherwise, the chain of functions that have been "inserted" into the
 *	filesystem will be called in succession until either a value other
 *	than NULL is returned, or the entire list is visited.
 *
 * Results:
 *	The result is a pointer to a Tcl_Obj specifying the current directory,
 *	or NULL if the current directory could not be determined. If NULL is
 *	returned, an error message is left in the interp's result.
 *
 *	The result already has its refCount incremented for the caller. When
 *	it is no longer needed, that refCount should be decremented.
 *
 * Side effects:
 *	Various objects may be freed and allocated.
 *
 *----------------------------------------------------------------------
 */

Tcl_Obj *
Tcl_FSGetCwd(
    Tcl_Interp *interp)
{
    ThreadSpecificData *tsdPtr = TCL_TSD_INIT(&tclFsDataKey);

    if (TclFSCwdPointerEquals(NULL)) {
	FilesystemRecord *fsRecPtr;
	Tcl_Obj *retVal = NULL;

	/*
	 * We've never been called before, try to find a cwd. Call each of the
	 * "Tcl_GetCwd" function in succession. A non-NULL return value
	 * indicates the particular function has succeeded.
	 */

	fsRecPtr = FsGetFirstFilesystem();
	while ((retVal == NULL) && (fsRecPtr != NULL)) {
	    Tcl_FSGetCwdProc *proc = fsRecPtr->fsPtr->getCwdProc;
	    if (proc != NULL) {
		if (fsRecPtr->fsPtr->version != TCL_FILESYSTEM_VERSION_1) {
		    ClientData retCd;
		    TclFSGetCwdProc2 *proc2 = (TclFSGetCwdProc2*)proc;

		    retCd = (*proc2)(NULL);
		    if (retCd != NULL) {
			Tcl_Obj *norm;
			/* Looks like a new current directory */
			retVal = (*fsRecPtr->fsPtr->internalToNormalizedProc)(
				retCd);
			Tcl_IncrRefCount(retVal);
			norm = TclFSNormalizeAbsolutePath(interp,retVal,NULL);
			if (norm != NULL) {
			    /*
			     * We found a cwd, which is now in our global
			     * storage. We must make a copy. Norm already has
			     * a refCount of 1.
			     *
			     * Threading issue: note that multiple threads at
			     * system startup could in principle call this
			     * function simultaneously. They will therefore
			     * each set the cwdPathPtr independently. That
			     * behaviour is a bit peculiar, but should be
			     * fine. Once we have a cwd, we'll always be in
			     * the 'else' branch below which is simpler.
			     */

			    FsUpdateCwd(norm, retCd);
			    Tcl_DecrRefCount(norm);
			} else {
			    (*fsRecPtr->fsPtr->freeInternalRepProc)(retCd);
			}
			Tcl_DecrRefCount(retVal);
			retVal = NULL;
			goto cdDidNotChange;
		    } else if (interp != NULL) {
			Tcl_AppendResult(interp,
				"error getting working directory name: ",
				Tcl_PosixError(interp), NULL);
		    }
		} else {
		    retVal = (*proc)(interp);
		}
	    }
	    fsRecPtr = fsRecPtr->nextPtr;
	}

	/*
	 * Now the 'cwd' may NOT be normalized, at least on some platforms.
	 * For the sake of efficiency, we want a completely normalized cwd at
	 * all times.
	 *
	 * Finally, if retVal is NULL, we do not have a cwd, which could be
	 * problematic.
	 */

	if (retVal != NULL) {
	    Tcl_Obj *norm = TclFSNormalizeAbsolutePath(interp, retVal, NULL);
	    if (norm != NULL) {
		/*
		 * We found a cwd, which is now in our global storage. We must
		 * make a copy. Norm already has a refCount of 1.
		 *
		 * Threading issue: note that multiple threads at system
		 * startup could in principle call this function
		 * simultaneously. They will therefore each set the cwdPathPtr
		 * independently. That behaviour is a bit peculiar, but should
		 * be fine. Once we have a cwd, we'll always be in the 'else'
		 * branch below which is simpler.
		 */

		ClientData cd = (ClientData) Tcl_FSGetNativePath(norm);
		FsUpdateCwd(norm, TclNativeDupInternalRep(cd));
		Tcl_DecrRefCount(norm);
	    }
	    Tcl_DecrRefCount(retVal);
	}
    } else {
	/*
	 * We already have a cwd cached, but we want to give the filesystem it
	 * is in a chance to check whether that cwd has changed, or is perhaps
	 * no longer accessible. This allows an error to be thrown if, say,
	 * the permissions on that directory have changed.
	 */

	const Tcl_Filesystem *fsPtr = Tcl_FSGetFileSystemForPath(tsdPtr->cwdPathPtr);

	/*
	 * If the filesystem couldn't be found, or if no cwd function exists
	 * for this filesystem, then we simply assume the cached cwd is ok.
	 * If we do call a cwd, we must watch for errors (if the cwd returns
	 * NULL). This ensures that, say, on Unix if the permissions of the
	 * cwd change, 'pwd' does actually throw the correct error in Tcl.
	 * (This is tested for in the test suite on unix).
	 */

	if (fsPtr != NULL) {
	    Tcl_FSGetCwdProc *proc = fsPtr->getCwdProc;
	    ClientData retCd = NULL;
	    if (proc != NULL) {
		Tcl_Obj *retVal;
		if (fsPtr->version != TCL_FILESYSTEM_VERSION_1) {
		    TclFSGetCwdProc2 *proc2 = (TclFSGetCwdProc2*)proc;

		    retCd = (*proc2)(tsdPtr->cwdClientData);
		    if (retCd == NULL && interp != NULL) {
			Tcl_AppendResult(interp,
				"error getting working directory name: ",
				Tcl_PosixError(interp), NULL);
		    }

		    if (retCd == tsdPtr->cwdClientData) {
			goto cdDidNotChange;
		    }

		    /*
		     * Looks like a new current directory.
		     */

		    retVal = (*fsPtr->internalToNormalizedProc)(retCd);
		    Tcl_IncrRefCount(retVal);
		} else {
		    retVal = (*proc)(interp);
		}
		if (retVal != NULL) {
		    Tcl_Obj *norm = TclFSNormalizeAbsolutePath(interp,
			    retVal, NULL);

		    /*
		     * Check whether cwd has changed from the value previously
		     * stored in cwdPathPtr. Really 'norm' shouldn't be NULL,
		     * but we are careful.
		     */

		    if (norm == NULL) {
			/* Do nothing */
			if (retCd != NULL) {
			    (*fsPtr->freeInternalRepProc)(retCd);
			}
		    } else if (norm == tsdPtr->cwdPathPtr) {
			goto cdEqual;
		    } else {
			/*
			 * Note that both 'norm' and 'tsdPtr->cwdPathPtr' are
			 * normalized paths. Therefore we can be more
			 * efficient than calling 'Tcl_FSEqualPaths', and in
			 * addition avoid a nasty infinite loop bug when
			 * trying to normalize tsdPtr->cwdPathPtr.
			 */

			int len1, len2;
			char *str1, *str2;

			str1 = Tcl_GetStringFromObj(tsdPtr->cwdPathPtr, &len1);
			str2 = Tcl_GetStringFromObj(norm, &len2);
			if ((len1 == len2) && (strcmp(str1, str2) == 0)) {
			    /*
			     * If the paths were equal, we can be more
			     * efficient and retain the old path object which
			     * will probably already be shared. In this case
			     * we can simply free the normalized path we just
			     * calculated.
			     */

			cdEqual:
			    Tcl_DecrRefCount(norm);
			    if (retCd != NULL) {
				(*fsPtr->freeInternalRepProc)(retCd);
			    }
			} else {
			    FsUpdateCwd(norm, retCd);
			    Tcl_DecrRefCount(norm);
			}
		    }
		    Tcl_DecrRefCount(retVal);
		} else {
		    /*
		     * The 'cwd' function returned an error; reset the cwd.
		     */

		    FsUpdateCwd(NULL, NULL);
		}
	    }
	}
    }

  cdDidNotChange:
    if (tsdPtr->cwdPathPtr != NULL) {
	Tcl_IncrRefCount(tsdPtr->cwdPathPtr);
    }

    return tsdPtr->cwdPathPtr;
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_FSChdir --
 *
 *	This function replaces the library version of chdir().
 *
 *	The path is normalized and then passed to the filesystem which claims
 *	it.
 *
 * Results:
 *	See chdir() documentation. If successful, we keep a record of the
 *	successful path in cwdPathPtr for subsequent calls to getcwd.
 *
 * Side effects:
 *	See chdir() documentation. The global cwdPathPtr may change value.
 *
 *----------------------------------------------------------------------
 */

int
Tcl_FSChdir(
    Tcl_Obj *pathPtr)
{
    const Tcl_Filesystem *fsPtr;
    int retVal = -1;

    if (Tcl_FSGetNormalizedPath(NULL, pathPtr) == NULL) {
	Tcl_SetErrno(ENOENT);
	return retVal;
    }

    fsPtr = Tcl_FSGetFileSystemForPath(pathPtr);
    if (fsPtr != NULL) {
	Tcl_FSChdirProc *proc = fsPtr->chdirProc;
	if (proc != NULL) {
	    /*
	     * If this fails, an appropriate errno will have been stored using
	     * 'Tcl_SetErrno()'.
	     */

	    retVal = (*proc)(pathPtr);
	} else {
	    /*
	     * Fallback on stat-based implementation.
	     */

	    Tcl_StatBuf buf;

	    /*
	     * If the file can be stat'ed and is a directory and is readable,
	     * then we can chdir. If any of these actions fail, then
	     * 'Tcl_SetErrno()' should automatically have been called to set
	     * an appropriate error code
	     */

	    if ((Tcl_FSStat(pathPtr, &buf) == 0) && (S_ISDIR(buf.st_mode))
		    && (Tcl_FSAccess(pathPtr, R_OK) == 0)) {
		/*
		 * We allow the chdir.
		 */

		retVal = 0;
	    }
	}
    } else {
	Tcl_SetErrno(ENOENT);
    }

    /*
     * The cwd changed, or an error was thrown. If an error was thrown, we can
     * just continue (and that will report the error to the user). If there
     * was no error we must assume that the cwd was actually changed to the
     * normalized value we calculated above, and we must therefore cache that
     * information.
     */

    /*
     * If the filesystem in question has a getCwdProc, then the correct logic
     * which performs the part below is already part of the Tcl_FSGetCwd()
     * call, so no need to replicate it again. This will have a side effect
     * though. The private authoritative representation of the current working
     * directory stored in cwdPathPtr in static memory will be out-of-sync
     * with the real OS-maintained value. The first call to Tcl_FSGetCwd will
     * however recalculate the private copy to match the OS-value so
     * everything will work right.
     *
     * However, if there is no getCwdProc, then we _must_ update our private
     * storage of the cwd, since this is the only opportunity to do that!
     *
     * Note: We currently call this block of code irrespective of whether
     * there was a getCwdProc or not, but the code should all in principle
     * work if we only call this block if fsPtr->getCwdProc == NULL.
     */

    if (retVal == 0) {
	/*
	 * Note that this normalized path may be different to what we found
	 * above (or at least a different object), if the filesystem epoch
	 * changed recently. This can actually happen with scripted documents
	 * very easily. Therefore we ask for the normalized path again (the
	 * correct value will have been cached as a result of the
	 * Tcl_FSGetFileSystemForPath call above anyway).
	 */

	Tcl_Obj *normDirName = Tcl_FSGetNormalizedPath(NULL, pathPtr);

	if (normDirName == NULL) {
	    /* Not really true, but what else to do? */
	    Tcl_SetErrno(ENOENT);
	    return -1;
	}

	if (fsPtr == &tclNativeFilesystem) {
	    /*
	     * For the native filesystem, we keep a cache of the native
	     * representation of the cwd. But, we want to do that for the
	     * exact format that is returned by 'getcwd' (so that we can later
	     * compare the two representations for equality), which might not
	     * be exactly the same char-string as the native representation of
	     * the fully normalized path (e.g. on Windows there's a
	     * forward-slash vs backslash difference). Hence we ask for this
	     * again here. On Unix it might actually be true that we always
	     * have the correct form in the native rep in which case we could
	     * simply use:
	     *		cd = Tcl_FSGetNativePath(pathPtr);
	     * instead. This should be examined by someone on Unix.
	     */

	    ThreadSpecificData *tsdPtr = TCL_TSD_INIT(&tclFsDataKey);
	    ClientData cd;
	    ClientData oldcd = tsdPtr->cwdClientData;

	    /*
	     * Assumption we are using a filesystem version 2.
	     */

	    TclFSGetCwdProc2 *proc2 = (TclFSGetCwdProc2*)fsPtr->getCwdProc;
	    cd = (*proc2)(oldcd);
	    if (cd != oldcd) {
		FsUpdateCwd(normDirName, cd);
	    }
	} else {
	    FsUpdateCwd(normDirName, NULL);
	}
    }

    return retVal;
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_FSLoadFile --
 *
 *	Dynamically loads a binary code file into memory and returns the
 *	addresses of two functions within that file, if they are defined. The
 *	appropriate function for the filesystem to which pathPtr belongs will
 *	be called.
 *
 *	Note that the native filesystem doesn't actually assume 'pathPtr' is a
 *	path. Rather it assumes pathPtr is either a path or just the name
 *	(tail) of a file which can be found somewhere in the environment's
 *	loadable path. This behaviour is not very compatible with virtual
 *	filesystems (and has other problems documented in the load man-page),
 *	so it is advised that full paths are always used.
 *
 * Results:
 *	A standard Tcl completion code. If an error occurs, an error message
 *	is left in the interp's result.
 *
 * Side effects:
 *	New code suddenly appears in memory. This may later be unloaded by
 *	passing the clientData to the unloadProc.
 *
 *----------------------------------------------------------------------
 */

int
Tcl_FSLoadFile(
    Tcl_Interp *interp,		/* Used for error reporting. */
    Tcl_Obj *pathPtr,		/* Name of the file containing the desired
				 * code. */
    const char *sym1, const char *sym2,
				/* Names of two functions to look up in the
				 * file's symbol table. */
    Tcl_PackageInitProc **proc1Ptr, Tcl_PackageInitProc **proc2Ptr,
				/* Where to return the addresses corresponding
				 * to sym1 and sym2. */
    Tcl_LoadHandle *handlePtr,	/* Filled with token for dynamically loaded
				 * file which will be passed back to
				 * (*unloadProcPtr)() to unload the file. */
    Tcl_FSUnloadFileProc **unloadProcPtr)
				/* Filled with address of Tcl_FSUnloadFileProc
				 * function which should be used for this
				 * file. */
{
    const char *symbols[2];
    Tcl_PackageInitProc **procPtrs[2];
    ClientData clientData;
    int res;

    /*
     * Initialize the arrays.
     */

    symbols[0] = sym1;
    symbols[1] = sym2;
    procPtrs[0] = proc1Ptr;
    procPtrs[1] = proc2Ptr;

    /*
     * Perform the load.
     */

    res = TclLoadFile(interp, pathPtr, 2, symbols, procPtrs, handlePtr,
	    &clientData, unloadProcPtr);

    /*
     * Due to an unfortunate mis-design in Tcl 8.4 fs, when loading a shared
     * library, we don't keep the loadHandle (for TclpFindSymbol) and the
     * clientData (for the unloadProc) separately. In fact we effectively
     * throw away the loadHandle and only use the clientData. It just so
     * happens, for the native filesystem only, that these two are identical.
     *
     * This also means that the signatures Tcl_FSUnloadFileProc and
     * Tcl_FSLoadFileProc are both misleading.
     */

    *handlePtr = (Tcl_LoadHandle) clientData;
    return res;
}

/*
 *----------------------------------------------------------------------
 *
 * TclLoadFile --
 *
 *	Dynamically loads a binary code file into memory and returns the
 *	addresses of a number of given functions within that file, if they are
 *	defined. The appropriate function for the filesystem to which pathPtr
 *	belongs will be called.
 *
 *	Note that the native filesystem doesn't actually assume 'pathPtr' is a
 *	path. Rather it assumes pathPtr is either a path or just the name
 *	(tail) of a file which can be found somewhere in the environment's
 *	loadable path. This behaviour is not very compatible with virtual
 *	filesystems (and has other problems documented in the load man-page),
 *	so it is advised that full paths are always used.
 *
 *	This function is currently private to Tcl. It may be exported in the
 *	future and its interface fixed (but we should clean up the
 *	loadHandle/clientData confusion at that time -- see the above comments
 *	in Tcl_FSLoadFile for details). For a public function, see
 *	Tcl_FSLoadFile.
 *
 * Results:
 *	A standard Tcl completion code. If an error occurs, an error message
 *	is left in the interp's result.
 *
 * Side effects:
 *	New code suddenly appears in memory. This may later be unloaded by
 *	passing the clientData to the unloadProc.
 *
 *----------------------------------------------------------------------
 */

int
TclLoadFile(
    Tcl_Interp *interp,		/* Used for error reporting. */
    Tcl_Obj *pathPtr,		/* Name of the file containing the desired
				 * code. */
    int symc,			/* Number of symbols/procPtrs in the next two
				 * arrays. */
    const char *symbols[],	/* Names of functions to look up in the file's
				 * symbol table. */
    Tcl_PackageInitProc **procPtrs[],
				/* Where to return the addresses corresponding
				 * to symbols[]. */
    Tcl_LoadHandle *handlePtr,	/* Filled with token for shared library
				 * information which can be used in
				 * TclpFindSymbol. */
    ClientData *clientDataPtr,	/* Filled with token for dynamically loaded
				 * file which will be passed back to
				 * (*unloadProcPtr)() to unload the file. */
    Tcl_FSUnloadFileProc **unloadProcPtr)
				/* Filled with address of Tcl_FSUnloadFileProc
				 * function which should be used for this
				 * file. */
{
    const Tcl_Filesystem *fsPtr = Tcl_FSGetFileSystemForPath(pathPtr);
    Tcl_FSLoadFileProc *proc;
    Tcl_Filesystem *copyFsPtr;
    Tcl_Obj *copyToPtr;
    Tcl_LoadHandle newLoadHandle = NULL;
    ClientData newClientData = NULL;
    Tcl_FSUnloadFileProc *newUnloadProcPtr = NULL;
    FsDivertLoad *tvdlPtr;
    int retVal;

    if (fsPtr == NULL) {
	Tcl_SetErrno(ENOENT);
	return TCL_ERROR;
    }

    proc = fsPtr->loadFileProc;
    if (proc != NULL) {
	int retVal = (*proc)(interp, pathPtr, handlePtr, unloadProcPtr);
	if (retVal == TCL_OK) {
	    if (*handlePtr == NULL) {
		return TCL_ERROR;
	    }

	    /*
	     * Copy this across, since both are equal for the native fs.
	     */

	    *clientDataPtr = (ClientData)*handlePtr;
	    Tcl_ResetResult(interp);
	    goto resolveSymbols;
	}
	if (Tcl_GetErrno() != EXDEV) {
	    return retVal;
	}
    }

    /*
     * The filesystem doesn't support 'load', so we fall back on the following
     * technique:
     *
     * First check if it is readable -- and exists!
     */

    if (Tcl_FSAccess(pathPtr, R_OK) != 0) {
	Tcl_AppendResult(interp, "couldn't load library \"",
		Tcl_GetString(pathPtr), "\": ", Tcl_PosixError(interp), NULL);
	return TCL_ERROR;
    }

#ifdef TCL_LOAD_FROM_MEMORY
    /*
     * The platform supports loading code from memory, so ask for a buffer of
     * the appropriate size, read the file into it and load the code from the
     * buffer:
     */

    {
	int ret, size;
	void *buffer;
	Tcl_StatBuf statBuf;
	Tcl_Channel data;

	ret = Tcl_FSStat(pathPtr, &statBuf);
	if (ret < 0) {
	    goto mustCopyToTempAnyway;
	}
	size = (int) statBuf.st_size;

	/*
	 * Tcl_Read takes an int: check that file size isn't wide.
	 */

	if (size != (Tcl_WideInt) statBuf.st_size) {
	    goto mustCopyToTempAnyway;
	}
	data = Tcl_FSOpenFileChannel(interp, pathPtr, "rb", 0666);
	if (!data) {
	    goto mustCopyToTempAnyway;
	}
	buffer = TclpLoadMemoryGetBuffer(interp, size);
	if (!buffer) {
	    Tcl_Close(interp, data);
	    goto mustCopyToTempAnyway;
	}
	ret = Tcl_Read(data, buffer, size);
	Tcl_Close(interp, data);
	ret = TclpLoadMemory(interp, buffer, size, ret, handlePtr,
		unloadProcPtr);
	if (ret == TCL_OK && *handlePtr != NULL) {
	    *clientDataPtr = (ClientData) *handlePtr;
	    goto resolveSymbols;
	}
    }

  mustCopyToTempAnyway:
    Tcl_ResetResult(interp);
#endif

    /*
     * Get a temporary filename to use, first to copy the file into, and then
     * to load.
     */

    copyToPtr = TclpTempFileName();
    if (copyToPtr == NULL) {
	Tcl_AppendResult(interp, "couldn't create temporary file: ",
		Tcl_PosixError(interp), NULL);
	return TCL_ERROR;
    }
    Tcl_IncrRefCount(copyToPtr);

    copyFsPtr = Tcl_FSGetFileSystemForPath(copyToPtr);
    if ((copyFsPtr == NULL) || (copyFsPtr == fsPtr)) {
	/*
	 * We already know we can't use Tcl_FSLoadFile from this filesystem,
	 * and we must avoid a possible infinite loop. Try to delete the file
	 * we probably created, and then exit.
	 */

	Tcl_FSDeleteFile(copyToPtr);
	Tcl_DecrRefCount(copyToPtr);
	Tcl_AppendResult(interp, "couldn't load from current filesystem",NULL);
	return TCL_ERROR;
    }

    if (TclCrossFilesystemCopy(interp, pathPtr, copyToPtr) != TCL_OK) {
	/*
	 * Cross-platform copy failed.
	 */

	Tcl_FSDeleteFile(copyToPtr);
	Tcl_DecrRefCount(copyToPtr);
	return TCL_ERROR;
    }

#if !defined(__WIN32__)
    /*
     * Do we need to set appropriate permissions on the file? This may be
     * required on some systems. On Unix we could loop over the file
     * attributes, and set any that are called "-permissions" to 0700. However
     * we just do this directly, like this:
     */

    {
	int index;
	Tcl_Obj *perm;

	TclNewLiteralStringObj(perm, "0700");
	Tcl_IncrRefCount(perm);
	if (TclFSFileAttrIndex(copyToPtr, "-permissions", &index) == TCL_OK) {
	    Tcl_FSFileAttrsSet(NULL, index, copyToPtr, perm);
	}
	Tcl_DecrRefCount(perm);
    }
#endif

    /*
     * We need to reset the result now, because the cross-filesystem copy may
     * have stored the number of bytes in the result.
     */

    Tcl_ResetResult(interp);

    retVal = TclLoadFile(interp, copyToPtr, symc, symbols, procPtrs,
	    &newLoadHandle, &newClientData, &newUnloadProcPtr);
    if (retVal != TCL_OK) {
	/*
	 * The file didn't load successfully.
	 */

	Tcl_FSDeleteFile(copyToPtr);
	Tcl_DecrRefCount(copyToPtr);
	return retVal;
    }

    /*
     * Try to delete the file immediately - this is possible in some OSes, and
     * avoids any worries about leaving the copy laying around on exit.
     */

    if (Tcl_FSDeleteFile(copyToPtr) == TCL_OK) {
	Tcl_DecrRefCount(copyToPtr);

	/*
	 * We tell our caller about the real shared library which was loaded.
	 * Note that this does mean that the package list maintained by 'load'
	 * will store the original (vfs) path alongside the temporary load
	 * handle and unload proc ptr.
	 */

	(*handlePtr) = newLoadHandle;
	(*clientDataPtr) = newClientData;
	(*unloadProcPtr) = newUnloadProcPtr;
	Tcl_ResetResult(interp);
	return TCL_OK;
    }

    /*
     * When we unload this file, we need to divert the unloading so we can
     * unload and cleanup the temporary file correctly.
     */

    tvdlPtr = (FsDivertLoad *) ckalloc(sizeof(FsDivertLoad));

    /*
     * Remember three pieces of information. This allows us to cleanup the
     * diverted load completely, on platforms which allow proper unloading of
     * code.
     */

    tvdlPtr->loadHandle = newLoadHandle;
    tvdlPtr->unloadProcPtr = newUnloadProcPtr;

    if (copyFsPtr != &tclNativeFilesystem) {
	/*
	 * copyToPtr is already incremented for this reference.
	 */

	tvdlPtr->divertedFile = copyToPtr;

	/*
	 * This is the filesystem we loaded it into. Since we have a reference
	 * to 'copyToPtr', we already have a refCount on this filesystem, so
	 * we don't need to worry about it disappearing on us.
	 */

	tvdlPtr->divertedFilesystem = copyFsPtr;
	tvdlPtr->divertedFileNativeRep = NULL;
    } else {
	/*
	 * We need the native rep.
	 */

	tvdlPtr->divertedFileNativeRep = TclNativeDupInternalRep(
		Tcl_FSGetInternalRep(copyToPtr, copyFsPtr));

	/*
	 * We don't need or want references to the copied Tcl_Obj or the
	 * filesystem if it is the native one.
	 */

	tvdlPtr->divertedFile = NULL;
	tvdlPtr->divertedFilesystem = NULL;
	Tcl_DecrRefCount(copyToPtr);
    }

    copyToPtr = NULL;
    (*handlePtr) = newLoadHandle;
    (*clientDataPtr) = (ClientData) tvdlPtr;
    (*unloadProcPtr) = &FSUnloadTempFile;

    Tcl_ResetResult(interp);
    return retVal;

  resolveSymbols:
    {
	int i;

	for (i=0 ; i<symc ; i++) {
	    if (symbols[i] != NULL) {
		*procPtrs[i] = TclpFindSymbol(interp, *handlePtr, symbols[i]);
	    }
	}
    }
    return TCL_OK;
}
/*
 * This function used to be in the platform specific directories, but it has
 * now been made to work cross-platform
 */

int
TclpLoadFile(
    Tcl_Interp *interp,		/* Used for error reporting. */
    Tcl_Obj *pathPtr,		/* Name of the file containing the desired
				 * code (UTF-8). */
    const char *sym1, CONST char *sym2,
				/* Names of two functions to look up in the
				 * file's symbol table. */
    Tcl_PackageInitProc **proc1Ptr, Tcl_PackageInitProc **proc2Ptr,
				/* Where to return the addresses corresponding
				 * to sym1 and sym2. */
    ClientData *clientDataPtr,	/* Filled with token for dynamically loaded
				 * file which will be passed back to
				 * (*unloadProcPtr)() to unload the file. */
    Tcl_FSUnloadFileProc **unloadProcPtr)
				/* Filled with address of Tcl_FSUnloadFileProc
				 * function which should be used for this
				 * file. */
{
    Tcl_LoadHandle handle = NULL;
    int res;

    res = TclpDlopen(interp, pathPtr, &handle, unloadProcPtr);

    if (res != TCL_OK) {
	return res;
    }

    if (handle == NULL) {
	return TCL_ERROR;
    }

    *clientDataPtr = (ClientData) handle;

    *proc1Ptr = TclpFindSymbol(interp, handle, sym1);
    *proc2Ptr = TclpFindSymbol(interp, handle, sym2);
    return TCL_OK;
}

/*
 *---------------------------------------------------------------------------
 *
 * FSUnloadTempFile --
 *
 *	This function is called when we loaded a library of code via an
 *	intermediate temporary file. This function ensures the library is
 *	correctly unloaded and the temporary file is correctly deleted.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	The effects of the 'unload' function called, and of course the
 *	temporary file will be deleted.
 *
 *---------------------------------------------------------------------------
 */

static void
FSUnloadTempFile(
    Tcl_LoadHandle loadHandle)	/* loadHandle returned by a previous call to
				 * Tcl_FSLoadFile(). The loadHandle is a token
				 * that represents the loaded file. */
{
    FsDivertLoad *tvdlPtr = (FsDivertLoad *) loadHandle;

    /*
     * This test should never trigger, since we give the client data in the
     * function above.
     */

    if (tvdlPtr == NULL) {
	return;
    }

    /*
     * Call the real 'unloadfile' proc we actually used. It is very important
     * that we call this first, so that the shared library is actually
     * unloaded by the OS. Otherwise, the following 'delete' may well fail
     * because the shared library is still in use.
     */

    if (tvdlPtr->unloadProcPtr != NULL) {
	(*tvdlPtr->unloadProcPtr)(tvdlPtr->loadHandle);
    }

    if (tvdlPtr->divertedFilesystem == NULL) {
	/*
	 * It was the native filesystem, and we have a special function
	 * available just for this purpose, which we know works even at this
	 * late stage.
	 */

	TclpDeleteFile(tvdlPtr->divertedFileNativeRep);
	NativeFreeInternalRep(tvdlPtr->divertedFileNativeRep);

    } else {
	/*
	 * Remove the temporary file we created. Note, we may crash here
	 * because encodings have been taken down already.
	 */

	if (tvdlPtr->divertedFilesystem->deleteFileProc(tvdlPtr->divertedFile)
		!= TCL_OK) {
	    /*
	     * The above may have failed because the filesystem, or something
	     * it depends upon (e.g. encodings) have been taken down because
	     * Tcl is exiting.
	     *
	     * We may need to work out how to delete this file more robustly
	     * (or give the filesystem the information it needs to delete the
	     * file more robustly).
	     *
	     * In particular, one problem might be that the filesystem cannot
	     * extract the information it needs from the above path object
	     * because Tcl's entire filesystem apparatus (the code in this
	     * file) has been finalized, and it refuses to pass the internal
	     * representation to the filesystem.
	     */
	}

	/*
	 * And free up the allocations. This will also of course remove a
	 * refCount from the Tcl_Filesystem to which this file belongs, which
	 * could then free up the filesystem if we are exiting.
	 */

	Tcl_DecrRefCount(tvdlPtr->divertedFile);
    }

    ckfree((char*)tvdlPtr);
}

/*
 *---------------------------------------------------------------------------
 *
 * Tcl_FSLink --
 *
 *	This function replaces the library version of readlink() and can also
 *	be used to make links. The appropriate function for the filesystem to
 *	which pathPtr belongs will be called.
 *
 * Results:
 *	If toPtr is NULL, then the result is a Tcl_Obj specifying the contents
 *	of the symbolic link given by 'pathPtr', or NULL if the symbolic link
 *	could not be read. The result is owned by the caller, which should
 *	call Tcl_DecrRefCount when the result is no longer needed.
 *
 *	If toPtr is non-NULL, then the result is toPtr if the link action was
 *	successful, or NULL if not. In this case the result has no additional
 *	reference count, and need not be freed. The actual action to perform
 *	is given by the 'linkAction' flags, which is an or'd combination of:
 *
 *		TCL_CREATE_SYMBOLIC_LINK
 *		TCL_CREATE_HARD_LINK
 *
 *	Note that most filesystems will not support linking across to
 *	different filesystems, so this function will usually fail unless toPtr
 *	is in the same FS as pathPtr.
 *
 * Side effects:
 *	See readlink() documentation. A new filesystem link object may appear.
 *
 *---------------------------------------------------------------------------
 */

Tcl_Obj *
Tcl_FSLink(
    Tcl_Obj *pathPtr,		/* Path of file to readlink or link */
    Tcl_Obj *toPtr,		/* NULL or path to be linked to */
    int linkAction)		/* Action to perform */
{
    const Tcl_Filesystem *fsPtr = Tcl_FSGetFileSystemForPath(pathPtr);

    if (fsPtr != NULL) {
	Tcl_FSLinkProc *proc = fsPtr->linkProc;

	if (proc != NULL) {
	    return (*proc)(pathPtr, toPtr, linkAction);
	}
    }

    /*
     * If S_IFLNK isn't defined it means that the machine doesn't support
     * symbolic links, so the file can't possibly be a symbolic link. Generate
     * an EINVAL error, which is what happens on machines that do support
     * symbolic links when you invoke readlink on a file that isn't a symbolic
     * link.
     */

#ifndef S_IFLNK
    errno = EINVAL;
#else
    Tcl_SetErrno(ENOENT);
#endif /* S_IFLNK */
    return NULL;
}

/*
 *---------------------------------------------------------------------------
 *
 * Tcl_FSListVolumes --
 *
 *	Lists the currently mounted volumes. The chain of functions that have
 *	been "inserted" into the filesystem will be called in succession; each
 *	may return a list of volumes, all of which are added to the result
 *	until all mounted file systems are listed.
 *
 *	Notice that we assume the lists returned by each filesystem (if non
 *	NULL) have been given a refCount for us already. However, we are NOT
 *	allowed to hang on to the list itself (it belongs to the filesystem we
 *	called). Therefore we quite naturally add its contents to the result
 *	we are building, and then decrement the refCount.
 *
 * Results:
 *	The list of volumes, in an object which has refCount 0.
 *
 * Side effects:
 *	None
 *
 *---------------------------------------------------------------------------
 */

Tcl_Obj*
Tcl_FSListVolumes(void)
{
    FilesystemRecord *fsRecPtr;
    Tcl_Obj *resultPtr = Tcl_NewObj();

    /*
     * Call each of the "listVolumes" function in succession. A non-NULL
     * return value indicates the particular function has succeeded. We call
     * all the functions registered, since we want a list of all drives from
     * all filesystems.
     */

    fsRecPtr = FsGetFirstFilesystem();
    while (fsRecPtr != NULL) {
	Tcl_FSListVolumesProc *proc = fsRecPtr->fsPtr->listVolumesProc;
	if (proc != NULL) {
	    Tcl_Obj *thisFsVolumes = (*proc)();
	    if (thisFsVolumes != NULL) {
		Tcl_ListObjAppendList(NULL, resultPtr, thisFsVolumes);
		Tcl_DecrRefCount(thisFsVolumes);
	    }
	}
	fsRecPtr = fsRecPtr->nextPtr;
    }

    return resultPtr;
}

/*
 *---------------------------------------------------------------------------
 *
 * FsListMounts --
 *
 *	List all mounts within the given directory, which match the given
 *	pattern.
 *
 * Results:
 *	The list of mounts, in a list object which has refCount 0, or NULL if
 *	we didn't even find any filesystems to try to list mounts.
 *
 * Side effects:
 *	None
 *
 *---------------------------------------------------------------------------
 */

static Tcl_Obj *
FsListMounts(
    Tcl_Obj *pathPtr,		/* Contains path to directory to search. */
    const char *pattern)	/* Pattern to match against. */
{
    FilesystemRecord *fsRecPtr;
    Tcl_GlobTypeData mountsOnly = { TCL_GLOB_TYPE_MOUNT, 0, NULL, NULL };
    Tcl_Obj *resultPtr = NULL;

    /*
     * Call each of the "matchInDirectory" functions in succession, with the
     * specific type information 'mountsOnly'. A non-NULL return value
     * indicates the particular function has succeeded. We call all the
     * functions registered, since we want a list from each filesystems.
     */

    fsRecPtr = FsGetFirstFilesystem();
    while (fsRecPtr != NULL) {
	if (fsRecPtr->fsPtr != &tclNativeFilesystem) {
	    Tcl_FSMatchInDirectoryProc *proc =
		    fsRecPtr->fsPtr->matchInDirectoryProc;
	    if (proc != NULL) {
		if (resultPtr == NULL) {
		    resultPtr = Tcl_NewObj();
		}
		(*proc)(NULL, resultPtr, pathPtr, pattern, &mountsOnly);
	    }
	}
	fsRecPtr = fsRecPtr->nextPtr;
    }

    return resultPtr;
}

/*
 *---------------------------------------------------------------------------
 *
 * Tcl_FSSplitPath --
 *
 *	This function takes the given Tcl_Obj, which should be a valid path,
 *	and returns a Tcl List object containing each segment of that path as
 *	an element.
 *
 * Results:
 *	Returns list object with refCount of zero. If the passed in lenPtr is
 *	non-NULL, we use it to return the number of elements in the returned
 *	list.
 *
 * Side effects:
 *	None.
 *
 *---------------------------------------------------------------------------
 */

Tcl_Obj *
Tcl_FSSplitPath(
    Tcl_Obj *pathPtr,		/* Path to split. */
    int *lenPtr)		/* int to store number of path elements. */
{
    Tcl_Obj *result = NULL;	/* Needed only to prevent gcc warnings. */
    Tcl_Filesystem *fsPtr;
    char separator = '/';
    int driveNameLength;
    char *p;

    /*
     * Perform platform specific splitting.
     */

    if (TclFSGetPathType(pathPtr, &fsPtr,
	    &driveNameLength) == TCL_PATH_ABSOLUTE) {
	if (fsPtr == &tclNativeFilesystem) {
	    return TclpNativeSplitPath(pathPtr, lenPtr);
	}
    } else {
	return TclpNativeSplitPath(pathPtr, lenPtr);
    }

    /*
     * We assume separators are single characters.
     */

    if (fsPtr->filesystemSeparatorProc != NULL) {
	Tcl_Obj *sep = (*fsPtr->filesystemSeparatorProc)(pathPtr);
	if (sep != NULL) {
	    Tcl_IncrRefCount(sep);
	    separator = Tcl_GetString(sep)[0];
	    Tcl_DecrRefCount(sep);
	}
    }

    /*
     * Place the drive name as first element of the result list. The drive
     * name may contain strange characters, like colons and multiple forward
     * slashes (for example 'ftp://' is a valid vfs drive name)
     */

    result = Tcl_NewObj();
    p = Tcl_GetString(pathPtr);
    Tcl_ListObjAppendElement(NULL, result,
	    Tcl_NewStringObj(p, driveNameLength));
    p += driveNameLength;

    /*
     * Add the remaining path elements to the list.
     */

    for (;;) {
	char *elementStart = p;
	int length;
	while ((*p != '\0') && (*p != separator)) {
	    p++;
	}
	length = p - elementStart;
	if (length > 0) {
	    Tcl_Obj *nextElt;
	    if (elementStart[0] == '~') {
		TclNewLiteralStringObj(nextElt, "./");
		Tcl_AppendToObj(nextElt, elementStart, length);
	    } else {
		nextElt = Tcl_NewStringObj(elementStart, length);
	    }
	    Tcl_ListObjAppendElement(NULL, result, nextElt);
	}
	if (*p++ == '\0') {
	    break;
	}
    }

    /*
     * Compute the number of elements in the result.
     */

    if (lenPtr != NULL) {
	TclListObjLength(NULL, result, lenPtr);
    }
    return result;
}

/* Simple helper function */
Tcl_Obj *
TclFSInternalToNormalized(
    Tcl_Filesystem *fromFilesystem,
    ClientData clientData,
    FilesystemRecord **fsRecPtrPtr)
{
    FilesystemRecord *fsRecPtr = FsGetFirstFilesystem();

    while (fsRecPtr != NULL) {
	if (fsRecPtr->fsPtr == fromFilesystem) {
	    *fsRecPtrPtr = fsRecPtr;
	    break;
	}
	fsRecPtr = fsRecPtr->nextPtr;
    }

    if ((fsRecPtr != NULL)
	    && (fromFilesystem->internalToNormalizedProc != NULL)) {
	return (*fromFilesystem->internalToNormalizedProc)(clientData);
    } else {
	return NULL;
    }
}

/*
 *----------------------------------------------------------------------
 *
 * TclGetPathType --
 *
 *	Helper function used by FSGetPathType.
 *
 * Results:
 *	Returns one of TCL_PATH_ABSOLUTE, TCL_PATH_RELATIVE, or
 *	TCL_PATH_VOLUME_RELATIVE. The filesystem reference will be set if and
 *	only if it is non-NULL and the function's return value is
 *	TCL_PATH_ABSOLUTE.
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */

Tcl_PathType
TclGetPathType(
    Tcl_Obj *pathPtr,		/* Path to determine type for */
    Tcl_Filesystem **filesystemPtrPtr,
				/* If absolute path and this is not NULL, then
				 * set to the filesystem which claims this
				 * path. */
    int *driveNameLengthPtr,	/* If the path is absolute, and this is
				 * non-NULL, then set to the length of the
				 * driveName. */
    Tcl_Obj **driveNameRef)	/* If the path is absolute, and this is
				 * non-NULL, then set to the name of the
				 * drive, network-volume which contains the
				 * path, already with a refCount for the
				 * caller. */
{
    int pathLen;
    char *path;
    Tcl_PathType type;

    path = Tcl_GetStringFromObj(pathPtr, &pathLen);

    type = TclFSNonnativePathType(path, pathLen, filesystemPtrPtr,
	    driveNameLengthPtr, driveNameRef);

    if (type != TCL_PATH_ABSOLUTE) {
	type = TclpGetNativePathType(pathPtr, driveNameLengthPtr,
		driveNameRef);
	if ((type == TCL_PATH_ABSOLUTE) && (filesystemPtrPtr != NULL)) {
	    *filesystemPtrPtr = &tclNativeFilesystem;
	}
    }
    return type;
}

/*
 *----------------------------------------------------------------------
 *
 * TclFSNonnativePathType --
 *
 *	Helper function used by TclGetPathType. Its purpose is to check
 *	whether the given path starts with a string which corresponds to a
 *	file volume in any registered filesystem except the native one. For
 *	speed and historical reasons the native filesystem has special
 *	hard-coded checks dotted here and there in the filesystem code.
 *
 * Results:
 *	Returns one of TCL_PATH_ABSOLUTE or TCL_PATH_RELATIVE. The filesystem
 *	reference will be set if and only if it is non-NULL and the function's
 *	return value is TCL_PATH_ABSOLUTE.
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */

Tcl_PathType
TclFSNonnativePathType(
    const char *path,		/* Path to determine type for */
    int pathLen,		/* Length of the path */
    Tcl_Filesystem **filesystemPtrPtr,
				/* If absolute path and this is not NULL, then
				 * set to the filesystem which claims this
				 * path. */
    int *driveNameLengthPtr,	/* If the path is absolute, and this is
				 * non-NULL, then set to the length of the
				 * driveName. */
    Tcl_Obj **driveNameRef)	/* If the path is absolute, and this is
				 * non-NULL, then set to the name of the
				 * drive, network-volume which contains the
				 * path, already with a refCount for the
				 * caller. */
{
    FilesystemRecord *fsRecPtr;
    Tcl_PathType type = TCL_PATH_RELATIVE;

    /*
     * Call each of the "listVolumes" function in succession, checking whether
     * the given path is an absolute path on any of the volumes returned (this
     * is done by checking whether the path's prefix matches).
     */

    fsRecPtr = FsGetFirstFilesystem();
    while (fsRecPtr != NULL) {
	Tcl_FSListVolumesProc *proc = fsRecPtr->fsPtr->listVolumesProc;

	/*
	 * We want to skip the native filesystem in this loop because
	 * otherwise we won't necessarily pass all the Tcl testsuite -- this
	 * is because some of the tests artificially change the current
	 * platform (between win, unix) but the list of volumes we get by
	 * calling (*proc) will reflect the current (real) platform only and
	 * this may cause some tests to fail. In particular, on unix '/' will
	 * match the beginning of certain absolute Windows paths starting '//'
	 * and those tests will go wrong.
	 *
	 * Besides these test-suite issues, there is one other reason to skip
	 * the native filesystem --- since the tclFilename.c code has nice
	 * fast 'absolute path' checkers, we don't want to waste time
	 * repeating that effort here, and this function is actually called
	 * quite often, so if we can save the overhead of the native
	 * filesystem returning us a list of volumes all the time, it is
	 * better.
	 */

	if ((fsRecPtr->fsPtr != &tclNativeFilesystem) && (proc != NULL)) {
	    int numVolumes;
	    Tcl_Obj *thisFsVolumes = (*proc)();

	    if (thisFsVolumes != NULL) {
		if (Tcl_ListObjLength(NULL, thisFsVolumes, &numVolumes)
			!= TCL_OK) {
		    /*
		     * This is VERY bad; the Tcl_FSListVolumesProc didn't
		     * return a valid list. Set numVolumes to -1 so that we
		     * skip the while loop below and just return with the
		     * current value of 'type'.
		     *
		     * It would be better if we could signal an error here
		     * (but Tcl_Panic seems a bit excessive).
		     */

		    numVolumes = -1;
		}
		while (numVolumes > 0) {
		    Tcl_Obj *vol;
		    int len;
		    char *strVol;

		    numVolumes--;
		    Tcl_ListObjIndex(NULL, thisFsVolumes, numVolumes, &vol);
		    strVol = Tcl_GetStringFromObj(vol,&len);
		    if (pathLen < len) {
			continue;
		    }
		    if (strncmp(strVol, path, (size_t) len) == 0) {
			type = TCL_PATH_ABSOLUTE;
			if (filesystemPtrPtr != NULL) {
			    *filesystemPtrPtr = fsRecPtr->fsPtr;
			}
			if (driveNameLengthPtr != NULL) {
			    *driveNameLengthPtr = len;
			}
			if (driveNameRef != NULL) {
			    *driveNameRef = vol;
			    Tcl_IncrRefCount(vol);
			}
			break;
		    }
		}
		Tcl_DecrRefCount(thisFsVolumes);
		if (type == TCL_PATH_ABSOLUTE) {
		    /*
		     * We don't need to examine any more filesystems.
		     */
		    break;
		}
	    }
	}
	fsRecPtr = fsRecPtr->nextPtr;
    }
    return type;
}

/*
 *---------------------------------------------------------------------------
 *
 * Tcl_FSRenameFile --
 *
 *	If the two paths given belong to the same filesystem, we call that
 *	filesystems rename function. Otherwise we simply return the POSIX
 *	error 'EXDEV', and -1.
 *
 * Results:
 *	Standard Tcl error code if a function was called.
 *
 * Side effects:
 *	A file may be renamed.
 *
 *---------------------------------------------------------------------------
 */

int
Tcl_FSRenameFile(
    Tcl_Obj* srcPathPtr,	/* Pathname of file or dir to be renamed
				 * (UTF-8). */
    Tcl_Obj *destPathPtr)	/* New pathname of file or directory
				 * (UTF-8). */
{
    int retVal = -1;
    const Tcl_Filesystem *fsPtr, *fsPtr2;
    fsPtr = Tcl_FSGetFileSystemForPath(srcPathPtr);
    fsPtr2 = Tcl_FSGetFileSystemForPath(destPathPtr);

    if ((fsPtr == fsPtr2) && (fsPtr != NULL)) {
	Tcl_FSRenameFileProc *proc = fsPtr->renameFileProc;
	if (proc != NULL) {
	    retVal = (*proc)(srcPathPtr, destPathPtr);
	}
    }
    if (retVal == -1) {
	Tcl_SetErrno(EXDEV);
    }
    return retVal;
}

/*
 *---------------------------------------------------------------------------
 *
 * Tcl_FSCopyFile --
 *
 *	If the two paths given belong to the same filesystem, we call that
 *	filesystem's copy function. Otherwise we simply return the POSIX error
 *	'EXDEV', and -1.
 *
 *	Note that in the native filesystems, 'copyFileProc' is defined to copy
 *	soft links (i.e. it copies the links themselves, not the things they
 *	point to).
 *
 * Results:
 *	Standard Tcl error code if a function was called.
 *
 * Side effects:
 *	A file may be copied.
 *
 *---------------------------------------------------------------------------
 */

int
Tcl_FSCopyFile(
    Tcl_Obj *srcPathPtr,	/* Pathname of file to be copied (UTF-8). */
    Tcl_Obj *destPathPtr)	/* Pathname of file to copy to (UTF-8). */
{
    int retVal = -1;
    const Tcl_Filesystem *fsPtr, *fsPtr2;
    fsPtr = Tcl_FSGetFileSystemForPath(srcPathPtr);
    fsPtr2 = Tcl_FSGetFileSystemForPath(destPathPtr);

    if (fsPtr == fsPtr2 && fsPtr != NULL) {
	Tcl_FSCopyFileProc *proc = fsPtr->copyFileProc;
	if (proc != NULL) {
	    retVal = (*proc)(srcPathPtr, destPathPtr);
	}
    }
    if (retVal == -1) {
	Tcl_SetErrno(EXDEV);
    }
    return retVal;
}

/*
 *---------------------------------------------------------------------------
 *
 * TclCrossFilesystemCopy --
 *
 *	Helper for above function, and for Tcl_FSLoadFile, to copy files from
 *	one filesystem to another. This function will overwrite the target
 *	file if it already exists.
 *
 * Results:
 *	Standard Tcl error code.
 *
 * Side effects:
 *	A file may be created.
 *
 *---------------------------------------------------------------------------
 */
int
TclCrossFilesystemCopy(
    Tcl_Interp *interp,		/* For error messages */
    Tcl_Obj *source,		/* Pathname of file to be copied (UTF-8). */
    Tcl_Obj *target)		/* Pathname of file to copy to (UTF-8). */
{
    int result = TCL_ERROR;
    int prot = 0666;
    Tcl_Channel in, out;
    Tcl_StatBuf sourceStatBuf;
    struct utimbuf tval;

    out = Tcl_FSOpenFileChannel(interp, target, "wb", prot);
    if (out == NULL) {
	/*
	 * It looks like we cannot copy it over. Bail out...
	 */
	goto done;
    }

    in = Tcl_FSOpenFileChannel(interp, source, "rb", prot);
    if (in == NULL) {
	/*
	 * This is very strange, caller should have checked this...
	 */

	Tcl_Close(interp, out);
	goto done;
    }

    /*
     * Copy it synchronously. We might wish to add an asynchronous option to
     * support vfs's which are slow (e.g. network sockets).
     */

    if (TclCopyChannel(interp, in, out, -1, NULL) == TCL_OK) {
	result = TCL_OK;
    }

    /*
     * If the copy failed, assume that copy channel left a good error message.
     */

    Tcl_Close(interp, in);
    Tcl_Close(interp, out);

    /*
     * Set modification date of copied file.
     */

    if (Tcl_FSLstat(source, &sourceStatBuf) == 0) {
	tval.actime = sourceStatBuf.st_atime;
	tval.modtime = sourceStatBuf.st_mtime;
	Tcl_FSUtime(target, &tval);
    }

  done:
    return result;
}

/*
 *---------------------------------------------------------------------------
 *
 * Tcl_FSDeleteFile --
 *
 *	The appropriate function for the filesystem to which pathPtr belongs
 *	will be called.
 *
 * Results:
 *	Standard Tcl error code.
 *
 * Side effects:
 *	A file may be deleted.
 *
 *---------------------------------------------------------------------------
 */

int
Tcl_FSDeleteFile(
    Tcl_Obj *pathPtr)		/* Pathname of file to be removed (UTF-8). */
{
    const Tcl_Filesystem *fsPtr = Tcl_FSGetFileSystemForPath(pathPtr);
    if (fsPtr != NULL) {
	Tcl_FSDeleteFileProc *proc = fsPtr->deleteFileProc;
	if (proc != NULL) {
	    return (*proc)(pathPtr);
	}
    }
    Tcl_SetErrno(ENOENT);
    return -1;
}

/*
 *---------------------------------------------------------------------------
 *
 * Tcl_FSCreateDirectory --
 *
 *	The appropriate function for the filesystem to which pathPtr belongs
 *	will be called.
 *
 * Results:
 *	Standard Tcl error code.
 *
 * Side effects:
 *	A directory may be created.
 *
 *---------------------------------------------------------------------------
 */

int
Tcl_FSCreateDirectory(
    Tcl_Obj *pathPtr)		/* Pathname of directory to create (UTF-8). */
{
    const Tcl_Filesystem *fsPtr = Tcl_FSGetFileSystemForPath(pathPtr);
    if (fsPtr != NULL) {
	Tcl_FSCreateDirectoryProc *proc = fsPtr->createDirectoryProc;
	if (proc != NULL) {
	    return (*proc)(pathPtr);
	}
    }
    Tcl_SetErrno(ENOENT);
    return -1;
}

/*
 *---------------------------------------------------------------------------
 *
 * Tcl_FSCopyDirectory --
 *
 *	If the two paths given belong to the same filesystem, we call that
 *	filesystems copy-directory function. Otherwise we simply return the
 *	POSIX error 'EXDEV', and -1.
 *
 * Results:
 *	Standard Tcl error code if a function was called.
 *
 * Side effects:
 *	A directory may be copied.
 *
 *---------------------------------------------------------------------------
 */

int
Tcl_FSCopyDirectory(
    Tcl_Obj* srcPathPtr,	/* Pathname of directory to be copied
				 * (UTF-8). */
    Tcl_Obj *destPathPtr,	/* Pathname of target directory (UTF-8). */
    Tcl_Obj **errorPtr)		/* If non-NULL, then will be set to a new
				 * object containing name of file causing
				 * error, with refCount 1. */
{
    int retVal = -1;
    const Tcl_Filesystem *fsPtr, *fsPtr2;
    fsPtr = Tcl_FSGetFileSystemForPath(srcPathPtr);
    fsPtr2 = Tcl_FSGetFileSystemForPath(destPathPtr);

    if (fsPtr == fsPtr2 && fsPtr != NULL) {
	Tcl_FSCopyDirectoryProc *proc = fsPtr->copyDirectoryProc;
	if (proc != NULL) {
	    retVal = (*proc)(srcPathPtr, destPathPtr, errorPtr);
	}
    }
    if (retVal == -1) {
	Tcl_SetErrno(EXDEV);
    }
    return retVal;
}

/*
 *---------------------------------------------------------------------------
 *
 * Tcl_FSRemoveDirectory --
 *
 *	The appropriate function for the filesystem to which pathPtr belongs
 *	will be called.
 *
 * Results:
 *	Standard Tcl error code.
 *
 * Side effects:
 *	A directory may be deleted.
 *
 *---------------------------------------------------------------------------
 */

int
Tcl_FSRemoveDirectory(
    Tcl_Obj *pathPtr,		/* Pathname of directory to be removed
				 * (UTF-8). */
    int recursive,		/* If non-zero, removes directories that are
				 * nonempty. Otherwise, will only remove empty
				 * directories. */
    Tcl_Obj **errorPtr)		/* If non-NULL, then will be set to a new
				 * object containing name of file causing
				 * error, with refCount 1. */
{
    const Tcl_Filesystem *fsPtr = Tcl_FSGetFileSystemForPath(pathPtr);
    if (fsPtr != NULL && fsPtr->removeDirectoryProc != NULL) {
	Tcl_FSRemoveDirectoryProc *proc = fsPtr->removeDirectoryProc;
	if (recursive) {
	    /*
	     * We check whether the cwd lies inside this directory and move it
	     * if it does.
	     */

	    Tcl_Obj *cwdPtr = Tcl_FSGetCwd(NULL);

	    if (cwdPtr != NULL) {
		char *cwdStr, *normPathStr;
		int cwdLen, normLen;
		Tcl_Obj *normPath = Tcl_FSGetNormalizedPath(NULL, pathPtr);

		if (normPath != NULL) {
		    normPathStr = Tcl_GetStringFromObj(normPath, &normLen);
		    cwdStr = Tcl_GetStringFromObj(cwdPtr, &cwdLen);
		    if ((cwdLen >= normLen) && (strncmp(normPathStr, cwdStr,
			    (size_t) normLen) == 0)) {
			/*
			 * The cwd is inside the directory, so we perform a
			 * 'cd [file dirname $path]'.
			 */

			Tcl_Obj *dirPtr = TclPathPart(NULL, pathPtr,
				TCL_PATH_DIRNAME);

			Tcl_FSChdir(dirPtr);
			Tcl_DecrRefCount(dirPtr);
		    }
		}
		Tcl_DecrRefCount(cwdPtr);
	    }
	}
	return (*proc)(pathPtr, recursive, errorPtr);
    }
    Tcl_SetErrno(ENOENT);
    return -1;
}

/*
 *---------------------------------------------------------------------------
 *
 * Tcl_FSGetFileSystemForPath --
 *
 *	This function determines which filesystem to use for a particular path
 *	object, and returns the filesystem which accepts this file. If no
 *	filesystem will accept this object as a valid file path, then NULL is
 *	returned.
 *
 * Results:
 *	NULL or a filesystem which will accept this path.
 *
 * Side effects:
 *	The object may be converted to a path type.
 *
 *---------------------------------------------------------------------------
 */

Tcl_Filesystem *
Tcl_FSGetFileSystemForPath(
    Tcl_Obj* pathPtr)
{
    FilesystemRecord *fsRecPtr;
    Tcl_Filesystem* retVal = NULL;

    if (pathPtr == NULL) {
	Tcl_Panic("Tcl_FSGetFileSystemForPath called with NULL object");
	return NULL;
    }

    /*
     * If the object has a refCount of zero, we reject it. This is to avoid
     * possible segfaults or nondeterministic memory leaks (i.e. the user
     * doesn't know if they should decrement the ref count on return or not).
     */

    if (pathPtr->refCount == 0) {
	Tcl_Panic("Tcl_FSGetFileSystemForPath called with object with refCount == 0");
	return NULL;
    }

    /*
     * Check if the filesystem has changed in some way since this object's
     * internal representation was calculated. Before doing that, assure we
     * have the most up-to-date copy of the master filesystem. This is
     * accomplished by the FsGetFirstFilesystem() call.
     */

    fsRecPtr = FsGetFirstFilesystem();

    if (TclFSEnsureEpochOk(pathPtr, &retVal) != TCL_OK) {
	return NULL;
    }

    /*
     * Call each of the "pathInFilesystem" functions in succession. A
     * non-return value of -1 indicates the particular function has succeeded.
     */

    while ((retVal == NULL) && (fsRecPtr != NULL)) {
	Tcl_FSPathInFilesystemProc *proc =
		fsRecPtr->fsPtr->pathInFilesystemProc;

	if (proc != NULL) {
	    ClientData clientData = NULL;
	    if ((*proc)(pathPtr, &clientData) != -1) {
		/*
		 * We assume the type of pathPtr hasn't been changed by the
		 * above call to the pathInFilesystemProc.
		 */

		TclFSSetPathDetails(pathPtr, fsRecPtr, clientData);
		retVal = fsRecPtr->fsPtr;
	    }
	}
	fsRecPtr = fsRecPtr->nextPtr;
    }

    return retVal;
}

/*
 *---------------------------------------------------------------------------
 *
 * Tcl_FSGetNativePath --
 *
 *	This function is for use by the Win/Unix native filesystems, so that
 *	they can easily retrieve the native (char* or TCHAR*) representation
 *	of a path. Other filesystems will probably want to implement similar
 *	functions. They basically act as a safety net around
 *	Tcl_FSGetInternalRep. Normally your file-system functions will always
 *	be called with path objects already converted to the correct
 *	filesystem, but if for some reason they are called directly (i.e. by
 *	functions not in this file), then one cannot necessarily guarantee
 *	that the path object pointer is from the correct filesystem.
 *
 *	Note: in the future it might be desireable to have separate versions
 *	of this function with different signatures, for example
 *	Tcl_FSGetNativeWinPath, Tcl_FSGetNativeUnixPath etc. Right now, since
 *	native paths are all string based, we use just one function.
 *
 * Results:
 *	NULL or a valid native path.
 *
 * Side effects:
 *	See Tcl_FSGetInternalRep.
 *
 *---------------------------------------------------------------------------
 */

const char *
Tcl_FSGetNativePath(
    Tcl_Obj *pathPtr)
{
    return (const char *) Tcl_FSGetInternalRep(pathPtr, &tclNativeFilesystem);
}

/*
 *---------------------------------------------------------------------------
 *
 * NativeFreeInternalRep --
 *
 *	Free a native internal representation, which will be non-NULL.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	Memory is released.
 *
 *---------------------------------------------------------------------------
 */

static void
NativeFreeInternalRep(
    ClientData clientData)
{
    ckfree((char *) clientData);
}

/*
 *---------------------------------------------------------------------------
 *
 * Tcl_FSFileSystemInfo --
 *
 *	This function returns a list of two elements. The first element is the
 *	name of the filesystem (e.g. "native" or "vfs"), and the second is the
 *	particular type of the given path within that filesystem.
 *
 * Results:
 *	A list of two elements.
 *
 * Side effects:
 *	The object may be converted to a path type.
 *
 *---------------------------------------------------------------------------
 */

Tcl_Obj *
Tcl_FSFileSystemInfo(
    Tcl_Obj *pathPtr)
{
    Tcl_Obj *resPtr;
    Tcl_FSFilesystemPathTypeProc *proc;
    const Tcl_Filesystem *fsPtr = Tcl_FSGetFileSystemForPath(pathPtr);

    if (fsPtr == NULL) {
	return NULL;
    }

    resPtr = Tcl_NewListObj(0, NULL);
    Tcl_ListObjAppendElement(NULL,resPtr,Tcl_NewStringObj(fsPtr->typeName,-1));

    proc = fsPtr->filesystemPathTypeProc;
    if (proc != NULL) {
	Tcl_Obj *typePtr = (*proc)(pathPtr);
	if (typePtr != NULL) {
	    Tcl_ListObjAppendElement(NULL, resPtr, typePtr);
	}
    }

    return resPtr;
}

/*
 *---------------------------------------------------------------------------
 *
 * Tcl_FSPathSeparator --
 *
 *	This function returns the separator to be used for a given path. The
 *	object returned should have a refCount of zero
 *
 * Results:
 *	A Tcl object, with a refCount of zero. If the caller needs to retain a
 *	reference to the object, it should call Tcl_IncrRefCount, and should
 *	otherwise free the object.
 *
 * Side effects:
 *	The path object may be converted to a path type.
 *
 *---------------------------------------------------------------------------
 */

Tcl_Obj *
Tcl_FSPathSeparator(
    Tcl_Obj *pathPtr)
{
    const Tcl_Filesystem *fsPtr = Tcl_FSGetFileSystemForPath(pathPtr);

    if (fsPtr == NULL) {
	return NULL;
    }
    if (fsPtr->filesystemSeparatorProc != NULL) {
	return (*fsPtr->filesystemSeparatorProc)(pathPtr);
    } else {
	Tcl_Obj *resultObj;

	/*
	 * Allow filesystems not to provide a filesystemSeparatorProc if they
	 * wish to use the standard forward slash.
	 */

	TclNewLiteralStringObj(resultObj, "/");
	return resultObj;
    }
}

/*
 *---------------------------------------------------------------------------
 *
 * NativeFilesystemSeparator --
 *
 *	This function is part of the native filesystem support, and returns
 *	the separator for the given path.
 *
 * Results:
 *	String object containing the separator character.
 *
 * Side effects:
 *	None.
 *
 *---------------------------------------------------------------------------
 */

static Tcl_Obj *
NativeFilesystemSeparator(
    Tcl_Obj *pathPtr)
{
    const char *separator = NULL; /* lint */
    switch (tclPlatform) {
    case TCL_PLATFORM_UNIX:
	separator = "/";
	break;
    case TCL_PLATFORM_WINDOWS:
	separator = "\\";
	break;
    }
    return Tcl_NewStringObj(separator,1);
}

/* Everything from here on is contained in this obsolete ifdef */
#ifdef USE_OBSOLETE_FS_HOOKS

/*
 *----------------------------------------------------------------------
 *
 * TclStatInsertProc --
 *
 *	Insert the passed function pointer at the head of the list of
 *	functions which are used during a call to 'TclStat(...)'. The passed
 *	function should behave exactly like 'TclStat' when called during that
 *	time (see 'TclStat(...)' for more information). The function will be
 *	added even if it already in the list.
 *
 * Results:
 *	Normally TCL_OK; TCL_ERROR if memory for a new node in the list could
 *	not be allocated.
 *
 * Side effects:
 *	Memory allocated and modifies the link list for 'TclStat' functions.
 *
 *----------------------------------------------------------------------
 */

int
TclStatInsertProc(
    TclStatProc_ *proc)
{
    int retVal = TCL_ERROR;

    if (proc != NULL) {
	StatProc *newStatProcPtr;

	newStatProcPtr = (StatProc *)ckalloc(sizeof(StatProc));

	if (newStatProcPtr != NULL) {
	    newStatProcPtr->proc = proc;
	    Tcl_MutexLock(&obsoleteFsHookMutex);
	    newStatProcPtr->nextPtr = statProcList;
	    statProcList = newStatProcPtr;
	    Tcl_MutexUnlock(&obsoleteFsHookMutex);

	    retVal = TCL_OK;
	}
    }

    return retVal;
}

/*
 *----------------------------------------------------------------------
 *
 * TclStatDeleteProc --
 *
 *	Removed the passed function pointer from the list of 'TclStat'
 *	functions. Ensures that the built-in stat function is not removable.
 *
 * Results:
 *	TCL_OK if the function pointer was successfully removed, TCL_ERROR
 *	otherwise.
 *
 * Side effects:
 *	Memory is deallocated and the respective list updated.
 *
 *----------------------------------------------------------------------
 */

int
TclStatDeleteProc(
    TclStatProc_ *proc)
{
    int retVal = TCL_ERROR;
    StatProc *tmpStatProcPtr;
    StatProc *prevStatProcPtr = NULL;

    Tcl_MutexLock(&obsoleteFsHookMutex);
    tmpStatProcPtr = statProcList;

    /*
     * Traverse the 'statProcList' looking for the particular node whose
     * 'proc' member matches 'proc' and remove that one from the list. Ensure
     * that the "default" node cannot be removed.
     */

    while ((retVal == TCL_ERROR) && (tmpStatProcPtr != NULL)) {
	if (tmpStatProcPtr->proc == proc) {
	    if (prevStatProcPtr == NULL) {
		statProcList = tmpStatProcPtr->nextPtr;
	    } else {
		prevStatProcPtr->nextPtr = tmpStatProcPtr->nextPtr;
	    }

	    ckfree((char *)tmpStatProcPtr);

	    retVal = TCL_OK;
	} else {
	    prevStatProcPtr = tmpStatProcPtr;
	    tmpStatProcPtr = tmpStatProcPtr->nextPtr;
	}
    }

    Tcl_MutexUnlock(&obsoleteFsHookMutex);

    return retVal;
}

/*
 *----------------------------------------------------------------------
 *
 * TclAccessInsertProc --
 *
 *	Insert the passed function pointer at the head of the list of
 *	functions which are used during a call to 'TclAccess(...)'. The passed
 *	function should behave exactly like 'TclAccess' when called during
 *	that time (see 'TclAccess(...)' for more information). The function
 *	will be added even if it already in the list.
 *
 * Results:
 *	Normally TCL_OK; TCL_ERROR if memory for a new node in the list could
 *	not be allocated.
 *
 * Side effects:
 *	Memory allocated and modifies the link list for 'TclAccess' functions.
 *
 *----------------------------------------------------------------------
 */

int
TclAccessInsertProc(
    TclAccessProc_ *proc)
{
    int retVal = TCL_ERROR;

    if (proc != NULL) {
	AccessProc *newAccessProcPtr;

	newAccessProcPtr = (AccessProc *)ckalloc(sizeof(AccessProc));

	if (newAccessProcPtr != NULL) {
	    newAccessProcPtr->proc = proc;
	    Tcl_MutexLock(&obsoleteFsHookMutex);
	    newAccessProcPtr->nextPtr = accessProcList;
	    accessProcList = newAccessProcPtr;
	    Tcl_MutexUnlock(&obsoleteFsHookMutex);

	    retVal = TCL_OK;
	}
    }

    return retVal;
}

/*
 *----------------------------------------------------------------------
 *
 * TclAccessDeleteProc --
 *
 *	Removed the passed function pointer from the list of 'TclAccess'
 *	functions. Ensures that the built-in access function is not removable.
 *
 * Results:
 *	TCL_OK if the function pointer was successfully removed, TCL_ERROR
 *	otherwise.
 *
 * Side effects:
 *	Memory is deallocated and the respective list updated.
 *
 *----------------------------------------------------------------------
 */

int
TclAccessDeleteProc(
    TclAccessProc_ *proc)
{
    int retVal = TCL_ERROR;
    AccessProc *tmpAccessProcPtr;
    AccessProc *prevAccessProcPtr = NULL;

    /*
     * Traverse the 'accessProcList' looking for the particular node whose
     * 'proc' member matches 'proc' and remove that one from the list. Ensure
     * that the "default" node cannot be removed.
     */

    Tcl_MutexLock(&obsoleteFsHookMutex);
    tmpAccessProcPtr = accessProcList;
    while ((retVal == TCL_ERROR) && (tmpAccessProcPtr != NULL)) {
	if (tmpAccessProcPtr->proc == proc) {
	    if (prevAccessProcPtr == NULL) {
		accessProcList = tmpAccessProcPtr->nextPtr;
	    } else {
		prevAccessProcPtr->nextPtr = tmpAccessProcPtr->nextPtr;
	    }

	    ckfree((char *)tmpAccessProcPtr);

	    retVal = TCL_OK;
	} else {
	    prevAccessProcPtr = tmpAccessProcPtr;
	    tmpAccessProcPtr = tmpAccessProcPtr->nextPtr;
	}
    }
    Tcl_MutexUnlock(&obsoleteFsHookMutex);

    return retVal;
}

/*
 *----------------------------------------------------------------------
 *
 * TclOpenFileChannelInsertProc --
 *
 *	Insert the passed function pointer at the head of the list of
 *	functions which are used during a call to 'Tcl_OpenFileChannel(...)'.
 *	The passed function should behave exactly like 'Tcl_OpenFileChannel'
 *	when called during that time (see 'Tcl_OpenFileChannel(...)' for more
 *	information). The function will be added even if it already in the
 *	list.
 *
 * Results:
 *	Normally TCL_OK; TCL_ERROR if memory for a new node in the list could
 *	not be allocated.
 *
 * Side effects:
 *	Memory allocated and modifies the link list for 'Tcl_OpenFileChannel'
 *	functions.
 *
 *----------------------------------------------------------------------
 */

int
TclOpenFileChannelInsertProc(
    TclOpenFileChannelProc_ *proc)
{
    int retVal = TCL_ERROR;

    if (proc != NULL) {
	OpenFileChannelProc *newOpenFileChannelProcPtr;

	newOpenFileChannelProcPtr = (OpenFileChannelProc *)
		ckalloc(sizeof(OpenFileChannelProc));

	newOpenFileChannelProcPtr->proc = proc;
	Tcl_MutexLock(&obsoleteFsHookMutex);
	newOpenFileChannelProcPtr->nextPtr = openFileChannelProcList;
	openFileChannelProcList = newOpenFileChannelProcPtr;
	Tcl_MutexUnlock(&obsoleteFsHookMutex);

	retVal = TCL_OK;
    }

    return retVal;
}

/*
 *----------------------------------------------------------------------
 *
 * TclOpenFileChannelDeleteProc --
 *
 *	Removed the passed function pointer from the list of
 *	'Tcl_OpenFileChannel' functions. Ensures that the built-in open file
 *	channel function is not removable.
 *
 * Results:
 *	TCL_OK if the function pointer was successfully removed, TCL_ERROR
 *	otherwise.
 *
 * Side effects:
 *	Memory is deallocated and the respective list updated.
 *
 *----------------------------------------------------------------------
 */

int
TclOpenFileChannelDeleteProc(
    TclOpenFileChannelProc_ *proc)
{
    int retVal = TCL_ERROR;
    OpenFileChannelProc *tmpOpenFileChannelProcPtr = openFileChannelProcList;
    OpenFileChannelProc *prevOpenFileChannelProcPtr = NULL;

    /*
     * Traverse the 'openFileChannelProcList' looking for the particular node
     * whose 'proc' member matches 'proc' and remove that one from the list.
     */

    Tcl_MutexLock(&obsoleteFsHookMutex);
    tmpOpenFileChannelProcPtr = openFileChannelProcList;
    while ((retVal == TCL_ERROR) &&
	    (tmpOpenFileChannelProcPtr != NULL)) {
	if (tmpOpenFileChannelProcPtr->proc == proc) {
	    if (prevOpenFileChannelProcPtr == NULL) {
		openFileChannelProcList = tmpOpenFileChannelProcPtr->nextPtr;
	    } else {
		prevOpenFileChannelProcPtr->nextPtr =
			tmpOpenFileChannelProcPtr->nextPtr;
	    }

	    ckfree((char *) tmpOpenFileChannelProcPtr);

	    retVal = TCL_OK;
	} else {
	    prevOpenFileChannelProcPtr = tmpOpenFileChannelProcPtr;
	    tmpOpenFileChannelProcPtr = tmpOpenFileChannelProcPtr->nextPtr;
	}
    }
    Tcl_MutexUnlock(&obsoleteFsHookMutex);

    return retVal;
}
#endif /* USE_OBSOLETE_FS_HOOKS */

/*
 * Local Variables:
 * mode: c
 * c-basic-offset: 4
 * fill-column: 78
 * End:
 */
