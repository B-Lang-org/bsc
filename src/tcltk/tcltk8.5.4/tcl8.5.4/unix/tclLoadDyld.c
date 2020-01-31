/*
 * tclLoadDyld.c --
 *
 *	This procedure provides a version of the TclLoadFile that works with
 *	Apple's dyld dynamic loading.
 *	Original version of his file (superseded long ago) provided by
 *	Wilfredo Sanchez (wsanchez@apple.com).
 *
 * Copyright (c) 1995 Apple Computer, Inc.
 * Copyright (c) 2001-2007 Daniel A. Steffen <das@users.sourceforge.net>
 *
 * See the file "license.terms" for information on usage and redistribution of
 * this file, and for a DISCLAIMER OF ALL WARRANTIES.
 *
 * RCS: @(#) $Id: tclLoadDyld.c,v 1.29 2007/12/13 15:28:42 dgp Exp $
 */

#include "tclInt.h"

#ifndef MODULE_SCOPE
#define MODULE_SCOPE extern
#endif

#ifndef TCL_DYLD_USE_DLFCN
/*
 * Use preferred dlfcn API on 10.4 and later
 */
#   if !defined(NO_DLFCN_H) && MAC_OS_X_VERSION_MAX_ALLOWED >= 1040
#	define TCL_DYLD_USE_DLFCN 1
#   else
#	define TCL_DYLD_USE_DLFCN 0
#   endif
#endif
#ifndef TCL_DYLD_USE_NSMODULE
/*
 * Use deprecated NSModule API only to support 10.3 and earlier:
 */
#   if MAC_OS_X_VERSION_MIN_REQUIRED < 1040
#	define TCL_DYLD_USE_NSMODULE 1
#   else
#	define TCL_DYLD_USE_NSMODULE 0
#   endif
#endif

#if TCL_DYLD_USE_DLFCN
#include <dlfcn.h>
#if defined(HAVE_WEAK_IMPORT) && MAC_OS_X_VERSION_MIN_REQUIRED < 1040
/*
 * Support for weakly importing dlfcn API.
 */
extern void *dlopen(const char *path, int mode) WEAK_IMPORT_ATTRIBUTE;
extern void *dlsym(void *handle, const char *symbol) WEAK_IMPORT_ATTRIBUTE;
extern int dlclose(void *handle) WEAK_IMPORT_ATTRIBUTE;
extern char *dlerror(void) WEAK_IMPORT_ATTRIBUTE;
#endif
#endif

#if TCL_DYLD_USE_NSMODULE || defined(TCL_LOAD_FROM_MEMORY)
#include <mach-o/dyld.h>
#include <mach-o/fat.h>
#include <mach-o/swap.h>
#include <mach-o/arch.h>
#include <libkern/OSByteOrder.h>
#include <mach/mach.h>
#include <stdbool.h>

typedef struct Tcl_DyldModuleHandle {
    struct Tcl_DyldModuleHandle *nextPtr;
    NSModule module;
} Tcl_DyldModuleHandle;
#endif /* TCL_DYLD_USE_NSMODULE */

typedef struct Tcl_DyldLoadHandle {
#if TCL_DYLD_USE_DLFCN
    void *dlHandle;
#endif
#if TCL_DYLD_USE_NSMODULE || defined(TCL_LOAD_FROM_MEMORY)
    const struct mach_header *dyldLibHeader;
    Tcl_DyldModuleHandle *modulePtr;
#endif
} Tcl_DyldLoadHandle;

#if (TCL_DYLD_USE_DLFCN && MAC_OS_X_VERSION_MIN_REQUIRED < 1040) || \
	defined(TCL_LOAD_FROM_MEMORY)
MODULE_SCOPE long tclMacOSXDarwinRelease;
#endif

#ifdef TCL_DEBUG_LOAD
#define TclLoadDbgMsg(m, ...) do { \
	    fprintf(stderr, "%s:%d: %s(): " m ".\n", \
	    strrchr(__FILE__, '/')+1, __LINE__, __func__, ##__VA_ARGS__); \
	} while (0)
#else
#define TclLoadDbgMsg(m, ...)
#endif

#if TCL_DYLD_USE_NSMODULE || defined(TCL_LOAD_FROM_MEMORY)
/*
 *----------------------------------------------------------------------
 *
 * DyldOFIErrorMsg --
 *
 *	Converts a numerical NSObjectFileImage error into an error message
 *	string.
 *
 * Results:
 *	Error message string.
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */

static CONST char*
DyldOFIErrorMsg(
    int err)
{
    switch(err) {
    case NSObjectFileImageSuccess:
	return NULL;
    case NSObjectFileImageFailure:
	return "object file setup failure";
    case NSObjectFileImageInappropriateFile:
	return "not a Mach-O MH_BUNDLE file";
    case NSObjectFileImageArch:
	return "no object for this architecture";
    case NSObjectFileImageFormat:
	return "bad object file format";
    case NSObjectFileImageAccess:
	return "can't read object file";
    default:
	return "unknown error";
    }
}
#endif /* TCL_DYLD_USE_NSMODULE */

/*
 *----------------------------------------------------------------------
 *
 * TclpDlopen --
 *
 *	Dynamically loads a binary code file into memory and returns a handle
 *	to the new code.
 *
 * Results:
 *	A standard Tcl completion code. If an error occurs, an error message
 *	is left in the interpreter's result.
 *
 * Side effects:
 *	New code suddenly appears in memory.
 *
 *----------------------------------------------------------------------
 */

MODULE_SCOPE int
TclpDlopen(
    Tcl_Interp *interp,		/* Used for error reporting. */
    Tcl_Obj *pathPtr,		/* Name of the file containing the desired
				 * code (UTF-8). */
    Tcl_LoadHandle *loadHandle, /* Filled with token for dynamically loaded
				 * file which will be passed back to
				 * (*unloadProcPtr)() to unload the file. */
    Tcl_FSUnloadFileProc **unloadProcPtr)
				/* Filled with address of Tcl_FSUnloadFileProc
				 * function which should be used for this
				 * file. */
{
    Tcl_DyldLoadHandle *dyldLoadHandle;
#if TCL_DYLD_USE_DLFCN
    void *dlHandle = NULL;
#endif
#if TCL_DYLD_USE_NSMODULE || defined(TCL_LOAD_FROM_MEMORY)
    const struct mach_header *dyldLibHeader = NULL;
    Tcl_DyldModuleHandle *modulePtr = NULL;
#endif
#if TCL_DYLD_USE_NSMODULE
    NSLinkEditErrors editError;
    int errorNumber;
    const char *errorName, *objFileImageErrMsg = NULL;
#endif
    const char *errMsg = NULL;
    int result;
    Tcl_DString ds;
    char *fileName = NULL;
    const char *nativePath, *nativeFileName = NULL;

    /*
     * First try the full path the user gave us. This is particularly
     * important if the cwd is inside a vfs, and we are trying to load using a
     * relative path.
     */

    nativePath = Tcl_FSGetNativePath(pathPtr);

#if TCL_DYLD_USE_DLFCN
#if MAC_OS_X_VERSION_MIN_REQUIRED < 1040
    if (tclMacOSXDarwinRelease >= 8)
#endif
    {
	dlHandle = dlopen(nativePath, RTLD_NOW | RTLD_LOCAL);
	if (!dlHandle) {
	    /*
	     * Let the OS loader examine the binary search path for whatever
	     * string the user gave us which hopefully refers to a file on the
	     * binary path.
	     */

	    fileName = Tcl_GetString(pathPtr);
	    nativeFileName = Tcl_UtfToExternalDString(NULL, fileName, -1, &ds);
	    dlHandle = dlopen(nativeFileName, RTLD_NOW | RTLD_LOCAL);
	}
	if (dlHandle) {
	    TclLoadDbgMsg("dlopen() successful");
	} else {
	    errMsg = dlerror();
	    TclLoadDbgMsg("dlopen() failed: %s", errMsg);
	}
    }
    if (!dlHandle)
#endif /* TCL_DYLD_USE_DLFCN */
    {
#if TCL_DYLD_USE_NSMODULE
	dyldLibHeader = NSAddImage(nativePath,
		NSADDIMAGE_OPTION_RETURN_ON_ERROR);
	if (dyldLibHeader) {
	    TclLoadDbgMsg("NSAddImage() successful");
	} else {
	    NSLinkEditError(&editError, &errorNumber, &errorName, &errMsg);
	    if (editError == NSLinkEditFileAccessError) {
		/*
		 * The requested file was not found. Let the OS loader examine
		 * the binary search path for whatever string the user gave us
		 * which hopefully refers to a file on the binary path.
		 */

		if (!fileName) {
		    fileName = Tcl_GetString(pathPtr);
		    nativeFileName = Tcl_UtfToExternalDString(NULL, fileName,
			    -1, &ds);
		}
		dyldLibHeader = NSAddImage(nativeFileName,
			NSADDIMAGE_OPTION_WITH_SEARCHING |
			NSADDIMAGE_OPTION_RETURN_ON_ERROR);
		if (dyldLibHeader) {
		    TclLoadDbgMsg("NSAddImage() successful");
		} else {
		    NSLinkEditError(&editError, &errorNumber, &errorName,
			    &errMsg);
		    TclLoadDbgMsg("NSAddImage() failed: %s", errMsg);
		}
	    } else if ((editError == NSLinkEditFileFormatError
		    && errorNumber == EBADMACHO)
		    || editError == NSLinkEditOtherError){
		NSObjectFileImageReturnCode err;
		NSObjectFileImage dyldObjFileImage;
		NSModule module;

		/*
		 * The requested file was found but was not of type MH_DYLIB,
		 * attempt to load it as a MH_BUNDLE.
		 */

		err = NSCreateObjectFileImageFromFile(nativePath,
			&dyldObjFileImage);
		if (err == NSObjectFileImageSuccess && dyldObjFileImage) {
		    TclLoadDbgMsg("NSCreateObjectFileImageFromFile() "
			    "successful");
		    module = NSLinkModule(dyldObjFileImage, nativePath,
			    NSLINKMODULE_OPTION_BINDNOW
			    | NSLINKMODULE_OPTION_RETURN_ON_ERROR);
		    NSDestroyObjectFileImage(dyldObjFileImage);
		    if (module) {
			modulePtr = (Tcl_DyldModuleHandle *)
				ckalloc(sizeof(Tcl_DyldModuleHandle));
			modulePtr->module = module;
			modulePtr->nextPtr = NULL;
			TclLoadDbgMsg("NSLinkModule() successful");
		    } else {
			NSLinkEditError(&editError, &errorNumber, &errorName,
				&errMsg);
			TclLoadDbgMsg("NSLinkModule() failed: %s", errMsg);
		    }
		} else {
		    objFileImageErrMsg = DyldOFIErrorMsg(err);
		    TclLoadDbgMsg("NSCreateObjectFileImageFromFile() failed: "
			    "%s", objFileImageErrMsg);
		}
	    }
	}
#endif /* TCL_DYLD_USE_NSMODULE */
    }
    if (0
#if TCL_DYLD_USE_DLFCN
	    || dlHandle
#endif
#if TCL_DYLD_USE_NSMODULE
	    || dyldLibHeader || modulePtr
#endif
    ) {
	dyldLoadHandle = (Tcl_DyldLoadHandle *)
		ckalloc(sizeof(Tcl_DyldLoadHandle));
#if TCL_DYLD_USE_DLFCN
	dyldLoadHandle->dlHandle = dlHandle;
#endif
#if TCL_DYLD_USE_NSMODULE || defined(TCL_LOAD_FROM_MEMORY)
	dyldLoadHandle->dyldLibHeader = dyldLibHeader;
	dyldLoadHandle->modulePtr = modulePtr;
#endif
	*loadHandle = (Tcl_LoadHandle) dyldLoadHandle;
	*unloadProcPtr = &TclpUnloadFile;
	result = TCL_OK;
    } else {
	Tcl_AppendResult(interp, errMsg, NULL);
#if TCL_DYLD_USE_NSMODULE
	if (objFileImageErrMsg) {
	    Tcl_AppendResult(interp, "\nNSCreateObjectFileImageFromFile() "
		    "error: ", objFileImageErrMsg, NULL);
	}
#endif
	result = TCL_ERROR;
    }
    if(fileName) {
	Tcl_DStringFree(&ds);
    }
    return result;
}

/*
 *----------------------------------------------------------------------
 *
 * TclpFindSymbol --
 *
 *	Looks up a symbol, by name, through a handle associated with a
 *	previously loaded piece of code (shared library).
 *
 * Results:
 *	Returns a pointer to the function associated with 'symbol' if it is
 *	found. Otherwise returns NULL and may leave an error message in the
 *	interp's result.
 *
 *----------------------------------------------------------------------
 */

MODULE_SCOPE Tcl_PackageInitProc *
TclpFindSymbol(
    Tcl_Interp *interp,		/* For error reporting. */
    Tcl_LoadHandle loadHandle,	/* Handle from TclpDlopen. */
    CONST char *symbol)		/* Symbol name to look up. */
{
    Tcl_DyldLoadHandle *dyldLoadHandle = (Tcl_DyldLoadHandle *) loadHandle;
    Tcl_PackageInitProc *proc = NULL;
    const char *errMsg = NULL;
    Tcl_DString ds;
    const char *native;

    native = Tcl_UtfToExternalDString(NULL, symbol, -1, &ds);
#if TCL_DYLD_USE_DLFCN
    if (dyldLoadHandle->dlHandle) {
	proc = dlsym(dyldLoadHandle->dlHandle, native);
	if (proc) {
	    TclLoadDbgMsg("dlsym() successful");
	} else {
	    errMsg = dlerror();
	    TclLoadDbgMsg("dlsym() failed: %s", errMsg);
	}
    } else
#endif /* TCL_DYLD_USE_DLFCN */
    {
#if TCL_DYLD_USE_NSMODULE || defined(TCL_LOAD_FROM_MEMORY)
	NSSymbol nsSymbol = NULL;
	Tcl_DString newName;

	/*
	 * dyld adds an underscore to the beginning of symbol names.
	 */

	Tcl_DStringInit(&newName);
	Tcl_DStringAppend(&newName, "_", 1);
	native = Tcl_DStringAppend(&newName, native, -1);
	if (dyldLoadHandle->dyldLibHeader) {
	    nsSymbol = NSLookupSymbolInImage(dyldLoadHandle->dyldLibHeader,
		    native, NSLOOKUPSYMBOLINIMAGE_OPTION_BIND_NOW |
		    NSLOOKUPSYMBOLINIMAGE_OPTION_RETURN_ON_ERROR);
	    if (nsSymbol) {
		TclLoadDbgMsg("NSLookupSymbolInImage() successful");
#ifdef DYLD_SUPPORTS_DYLIB_UNLOADING
		/*
		 * Until dyld supports unloading of MY_DYLIB binaries, the
		 * following is not needed.
		 */

		NSModule module = NSModuleForSymbol(nsSymbol);
		Tcl_DyldModuleHandle *modulePtr = dyldLoadHandle->modulePtr;

		while (modulePtr != NULL) {
		    if (module == modulePtr->module) {
			break;
		    }
		    modulePtr = modulePtr->nextPtr;
		}
		if (modulePtr == NULL) {
		    modulePtr = (Tcl_DyldModuleHandle *)
			    ckalloc(sizeof(Tcl_DyldModuleHandle));
		    modulePtr->module = module;
		    modulePtr->nextPtr = dyldLoadHandle->modulePtr;
		    dyldLoadHandle->modulePtr = modulePtr;
		}
#endif /* DYLD_SUPPORTS_DYLIB_UNLOADING */
	    } else {
		NSLinkEditErrors editError;
		int errorNumber;
		const char *errorName;

		NSLinkEditError(&editError, &errorNumber, &errorName, &errMsg);
		TclLoadDbgMsg("NSLookupSymbolInImage() failed: %s", errMsg);
	    }
	} else if (dyldLoadHandle->modulePtr) {
	    nsSymbol = NSLookupSymbolInModule(
		    dyldLoadHandle->modulePtr->module, native);
	    if (nsSymbol) {
		TclLoadDbgMsg("NSLookupSymbolInModule() successful");
	    } else {
		TclLoadDbgMsg("NSLookupSymbolInModule() failed");
	    }
	}
	if (nsSymbol) {
	    proc = NSAddressOfSymbol(nsSymbol);
	    if (proc) {
		TclLoadDbgMsg("NSAddressOfSymbol() successful");
	    } else {
		TclLoadDbgMsg("NSAddressOfSymbol() failed");
	    }
	}
	Tcl_DStringFree(&newName);
#endif /* TCL_DYLD_USE_NSMODULE */
    }
    Tcl_DStringFree(&ds);
    if (errMsg) {
	Tcl_AppendResult(interp, errMsg, NULL);
    }
    return proc;
}

/*
 *----------------------------------------------------------------------
 *
 * TclpUnloadFile --
 *
 *	Unloads a dynamically loaded binary code file from memory. Code
 *	pointers in the formerly loaded file are no longer valid after calling
 *	this function.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	Code dissapears from memory. Note that dyld currently only supports
 *	unloading of binaries of type MH_BUNDLE loaded with NSLinkModule() in
 *	TclpDlopen() above.
 *
 *----------------------------------------------------------------------
 */

MODULE_SCOPE void
TclpUnloadFile(
    Tcl_LoadHandle loadHandle)	/* loadHandle returned by a previous call to
				 * TclpDlopen(). The loadHandle is a token
				 * that represents the loaded file. */
{
    Tcl_DyldLoadHandle *dyldLoadHandle = (Tcl_DyldLoadHandle *) loadHandle;

#if TCL_DYLD_USE_DLFCN
    if (dyldLoadHandle->dlHandle) {
	int result;

	result = dlclose(dyldLoadHandle->dlHandle);
	if (!result) {
	    TclLoadDbgMsg("dlclose() successful");
	} else {
	    TclLoadDbgMsg("dlclose() failed: %s", dlerror());
	}
    } else
#endif /* TCL_DYLD_USE_DLFCN */
    {
#if TCL_DYLD_USE_NSMODULE || defined(TCL_LOAD_FROM_MEMORY)
	Tcl_DyldModuleHandle *modulePtr = dyldLoadHandle->modulePtr;

	while (modulePtr != NULL) {
	    void *ptr;
	    bool result;

	    result = NSUnLinkModule(modulePtr->module,
		    NSUNLINKMODULE_OPTION_RESET_LAZY_REFERENCES);
	    if (result) {
		TclLoadDbgMsg("NSUnLinkModule() successful");
	    } else {
		TclLoadDbgMsg("NSUnLinkModule() failed");
	    }
	    ptr = modulePtr;
	    modulePtr = modulePtr->nextPtr;
	    ckfree(ptr);
	}
#endif /* TCL_DYLD_USE_NSMODULE */
    }
    ckfree((char*) dyldLoadHandle);
}

/*
 *----------------------------------------------------------------------
 *
 * TclGuessPackageName --
 *
 *	If the "load" command is invoked without providing a package name,
 *	this procedure is invoked to try to figure it out.
 *
 * Results:
 *	Always returns 0 to indicate that we couldn't figure out a package
 *	name; generic code will then try to guess the package from the file
 *	name. A return value of 1 would have meant that we figured out the
 *	package name and put it in bufPtr.
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */

int
TclGuessPackageName(
    CONST char *fileName,	/* Name of file containing package (already
				 * translated to local form if needed). */
    Tcl_DString *bufPtr)	/* Initialized empty dstring. Append package
				 * name to this if possible. */
{
    return 0;
}

#ifdef TCL_LOAD_FROM_MEMORY
/*
 *----------------------------------------------------------------------
 *
 * TclpLoadMemoryGetBuffer --
 *
 *	Allocate a buffer that can be used with TclpLoadMemory() below.
 *
 * Results:
 *	Pointer to allocated buffer or NULL if an error occurs.
 *
 * Side effects:
 *	Buffer is allocated.
 *
 *----------------------------------------------------------------------
 */

MODULE_SCOPE void *
TclpLoadMemoryGetBuffer(
    Tcl_Interp *interp,		/* Used for error reporting. */
    int size)			/* Size of desired buffer. */
{
    void *buffer = NULL;

    /*
     * NSCreateObjectFileImageFromMemory is available but always fails
     * prior to Darwin 7.
     */
    if (tclMacOSXDarwinRelease >= 7) {
	/*
	 * We must allocate the buffer using vm_allocate, because
	 * NSCreateObjectFileImageFromMemory will dispose of it using
	 * vm_deallocate.
	 */

	if (vm_allocate(mach_task_self(), (vm_address_t *) &buffer, size, 1)) {
	    buffer = NULL;
	}
    }
    return buffer;
}

/*
 *----------------------------------------------------------------------
 *
 * TclpLoadMemory --
 *
 *	Dynamically loads binary code file from memory and returns a handle to
 *	the new code.
 *
 * Results:
 *	A standard Tcl completion code. If an error occurs, an error message
 *	is left in the interpreter's result.
 *
 * Side effects:
 *	New code is loaded from memory.
 *
 *----------------------------------------------------------------------
 */

MODULE_SCOPE int
TclpLoadMemory(
    Tcl_Interp *interp,		/* Used for error reporting. */
    void *buffer,		/* Buffer containing the desired code
				 * (allocated with TclpLoadMemoryGetBuffer). */
    int size,			/* Allocation size of buffer. */
    int codeSize,		/* Size of code data read into buffer or -1 if
				 * an error occurred and the buffer should
				 * just be freed. */
    Tcl_LoadHandle *loadHandle, /* Filled with token for dynamically loaded
				 * file which will be passed back to
				 * (*unloadProcPtr)() to unload the file. */
    Tcl_FSUnloadFileProc **unloadProcPtr)
				/* Filled with address of Tcl_FSUnloadFileProc
				 * function which should be used for this
				 * file. */
{
    Tcl_DyldLoadHandle *dyldLoadHandle;
    NSObjectFileImage dyldObjFileImage = NULL;
    Tcl_DyldModuleHandle *modulePtr;
    NSModule module;
    const char *objFileImageErrMsg = NULL;

    /*
     * Try to create an object file image that we can load from.
     */

    if (codeSize >= 0) {
	NSObjectFileImageReturnCode err = NSObjectFileImageSuccess;
	const struct fat_header *fh = buffer;
	uint32_t ms = 0;
#ifndef __LP64__
	const struct mach_header *mh = NULL;
	#define mh_size  sizeof(struct mach_header)
	#define mh_magic MH_MAGIC
	#define arch_abi 0
#else
	const struct mach_header_64 *mh = NULL;
	#define mh_size  sizeof(struct mach_header_64)
	#define mh_magic MH_MAGIC_64
	#define arch_abi CPU_ARCH_ABI64
#endif

	if ((size_t) codeSize >= sizeof(struct fat_header)
		&& fh->magic == OSSwapHostToBigInt32(FAT_MAGIC)) {
	    uint32_t fh_nfat_arch = OSSwapBigToHostInt32(fh->nfat_arch);

	    /*
	     * Fat binary, try to find mach_header for our architecture
	     */

	    TclLoadDbgMsg("Fat binary, %d archs", fh_nfat_arch);
	    if ((size_t) codeSize >= sizeof(struct fat_header) +
		    fh_nfat_arch * sizeof(struct fat_arch)) {
		void *fatarchs = (char*)buffer + sizeof(struct fat_header);
		const NXArchInfo *arch = NXGetLocalArchInfo();
		struct fat_arch *fa;

		if (fh->magic != FAT_MAGIC) {
		    swap_fat_arch(fatarchs, fh_nfat_arch, arch->byteorder);
		}
		fa = NXFindBestFatArch(arch->cputype | arch_abi,
			arch->cpusubtype, fatarchs, fh_nfat_arch);
		if (fa) {
		    TclLoadDbgMsg("NXFindBestFatArch() successful: "
			    "local cputype %d subtype %d, "
			    "fat cputype %d subtype %d",
			    arch->cputype | arch_abi, arch->cpusubtype,
			    fa->cputype, fa->cpusubtype);
		    mh = (void*)((char*)buffer + fa->offset);
		    ms = fa->size;
		} else {
		    TclLoadDbgMsg("NXFindBestFatArch() failed");
		    err = NSObjectFileImageInappropriateFile;
		}
		if (fh->magic != FAT_MAGIC) {
		    swap_fat_arch(fatarchs, fh_nfat_arch, arch->byteorder);
		}
	    } else {
		TclLoadDbgMsg("Fat binary header failure");
		err = NSObjectFileImageInappropriateFile;
	    }
	} else {
	    /*
	     * Thin binary
	     */

	    TclLoadDbgMsg("Thin binary");
	    mh = buffer;
	    ms = codeSize;
	}
	if (ms && !(ms >= mh_size && mh->magic == mh_magic &&
		 mh->filetype == MH_BUNDLE)) {
	    TclLoadDbgMsg("Inappropriate file: magic %x filetype %d",
		    mh->magic, mh->filetype);
	    err = NSObjectFileImageInappropriateFile;
	}
	if (err == NSObjectFileImageSuccess) {
	    err = NSCreateObjectFileImageFromMemory(buffer, codeSize,
		    &dyldObjFileImage);
	    if (err == NSObjectFileImageSuccess) {
		TclLoadDbgMsg("NSCreateObjectFileImageFromMemory() "
			"successful");
	    } else {
		objFileImageErrMsg = DyldOFIErrorMsg(err);
		TclLoadDbgMsg("NSCreateObjectFileImageFromMemory() failed: %s",
			objFileImageErrMsg);
	    }
	} else {
	    objFileImageErrMsg = DyldOFIErrorMsg(err);
	}
    }

    /*
     * If it went wrong (or we were asked to just deallocate), get rid of the
     * memory block and create an error message.
     */

    if (dyldObjFileImage == NULL) {
	vm_deallocate(mach_task_self(), (vm_address_t) buffer, size);
	if (objFileImageErrMsg != NULL) {
	    Tcl_AppendResult(interp, "NSCreateObjectFileImageFromMemory() "
		    "error: ", objFileImageErrMsg, NULL);
	}
	return TCL_ERROR;
    }

    /*
     * Extract the module we want from the image of the object file.
     */

    module = NSLinkModule(dyldObjFileImage, "[Memory Based Bundle]",
	    NSLINKMODULE_OPTION_BINDNOW | NSLINKMODULE_OPTION_RETURN_ON_ERROR);
    NSDestroyObjectFileImage(dyldObjFileImage);
    if (module) {
	TclLoadDbgMsg("NSLinkModule() successful");
    } else {
	NSLinkEditErrors editError;
	int errorNumber;
	const char *errorName, *errMsg;

	NSLinkEditError(&editError, &errorNumber, &errorName, &errMsg);
	TclLoadDbgMsg("NSLinkModule() failed: %s", errMsg);
	Tcl_AppendResult(interp, errMsg, NULL);
	return TCL_ERROR;
    }

    /*
     * Stash the module reference within the load handle we create and return.
     */

    modulePtr = (Tcl_DyldModuleHandle *) ckalloc(sizeof(Tcl_DyldModuleHandle));
    modulePtr->module = module;
    modulePtr->nextPtr = NULL;
    dyldLoadHandle = (Tcl_DyldLoadHandle *)
	    ckalloc(sizeof(Tcl_DyldLoadHandle));
#if TCL_DYLD_USE_DLFCN
    dyldLoadHandle->dlHandle = NULL;
#endif
    dyldLoadHandle->dyldLibHeader = NULL;
    dyldLoadHandle->modulePtr = modulePtr;
    *loadHandle = (Tcl_LoadHandle) dyldLoadHandle;
    *unloadProcPtr = &TclpUnloadFile;
    return TCL_OK;
}
#endif /* TCL_LOAD_FROM_MEMORY */

/*
 * Local Variables:
 * mode: c
 * c-basic-offset: 4
 * fill-column: 79
 * End:
 */
