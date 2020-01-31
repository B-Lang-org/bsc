/*
 * tclLoad.c --
 *
 *	This file provides the generic portion (those that are the same on all
 *	platforms) of Tcl's dynamic loading facilities.
 *
 * Copyright (c) 1995-1997 Sun Microsystems, Inc.
 *
 * See the file "license.terms" for information on usage and redistribution of
 * this file, and for a DISCLAIMER OF ALL WARRANTIES.
 *
 * RCS: @(#) $Id: tclLoad.c,v 1.16 2007/02/20 23:24:03 nijtmans Exp $
 */

#include "tclInt.h"

/*
 * The following structure describes a package that has been loaded either
 * dynamically (with the "load" command) or statically (as indicated by a call
 * to TclGetLoadedPackages). All such packages are linked together into a
 * single list for the process. Packages are never unloaded, until the
 * application exits, when TclFinalizeLoad is called, and these structures are
 * freed.
 */

typedef struct LoadedPackage {
    char *fileName;		/* Name of the file from which the package was
				 * loaded. An empty string means the package
				 * is loaded statically. Malloc-ed. */
    char *packageName;		/* Name of package prefix for the package,
				 * properly capitalized (first letter UC,
				 * others LC), no "_", as in "Net".
				 * Malloc-ed. */
    Tcl_LoadHandle loadHandle;	/* Token for the loaded file which should be
				 * passed to (*unLoadProcPtr)() when the file
				 * is no longer needed. If fileName is NULL,
				 * then this field is irrelevant. */
    Tcl_PackageInitProc *initProc;
				/* Initialization function to call to
				 * incorporate this package into a trusted
				 * interpreter. */
    Tcl_PackageInitProc *safeInitProc;
				/* Initialization function to call to
				 * incorporate this package into a safe
				 * interpreter (one that will execute
				 * untrusted scripts). NULL means the package
				 * can't be used in unsafe interpreters. */
    Tcl_PackageUnloadProc *unloadProc;
				/* Finalisation function to unload a package
				 * from a trusted interpreter. NULL means that
				 * the package cannot be unloaded. */
    Tcl_PackageUnloadProc *safeUnloadProc;
				/* Finalisation function to unload a package
				 * from a safe interpreter. NULL means that
				 * the package cannot be unloaded. */
    int interpRefCount;		/* How many times the package has been loaded
				 * in trusted interpreters. */
    int safeInterpRefCount;	/* How many times the package has been loaded
				 * in safe interpreters. */
    Tcl_FSUnloadFileProc *unLoadProcPtr;
				/* Function to use to unload this package. If
				 * NULL, then we do not attempt to unload the
				 * package. If fileName is NULL, then this
				 * field is irrelevant. */
    struct LoadedPackage *nextPtr;
				/* Next in list of all packages loaded into
				 * this application process. NULL means end of
				 * list. */
} LoadedPackage;

/*
 * TCL_THREADS
 * There is a global list of packages that is anchored at firstPackagePtr.
 * Access to this list is governed by a mutex.
 */

static LoadedPackage *firstPackagePtr = NULL;
				/* First in list of all packages loaded into
				 * this process. */

TCL_DECLARE_MUTEX(packageMutex)

/*
 * The following structure represents a particular package that has been
 * incorporated into a particular interpreter (by calling its initialization
 * function). There is a list of these structures for each interpreter, with
 * an AssocData value (key "load") for the interpreter that points to the
 * first package (if any).
 */

typedef struct InterpPackage {
    LoadedPackage *pkgPtr;	/* Points to detailed information about
				 * package. */
    struct InterpPackage *nextPtr;
				/* Next package in this interpreter, or NULL
				 * for end of list. */
} InterpPackage;

/*
 * Prototypes for functions that are private to this file:
 */

static void		LoadCleanupProc(ClientData clientData,
			    Tcl_Interp *interp);

/*
 *----------------------------------------------------------------------
 *
 * Tcl_LoadObjCmd --
 *
 *	This function is invoked to process the "load" Tcl command. See the
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
Tcl_LoadObjCmd(
    ClientData dummy,		/* Not used. */
    Tcl_Interp *interp,		/* Current interpreter. */
    int objc,			/* Number of arguments. */
    Tcl_Obj *const objv[])	/* Argument objects. */
{
    Tcl_Interp *target;
    LoadedPackage *pkgPtr, *defaultPtr;
    Tcl_DString pkgName, tmp, initName, safeInitName;
    Tcl_DString unloadName, safeUnloadName;
    Tcl_PackageInitProc *initProc, *safeInitProc, *unloadProc, *safeUnloadProc;
    InterpPackage *ipFirstPtr, *ipPtr;
    int code, namesMatch, filesMatch, offset;
    const char *symbols[4];
    Tcl_PackageInitProc **procPtrs[4];
    ClientData clientData;
    char *p, *fullFileName, *packageName;
    Tcl_LoadHandle loadHandle;
    Tcl_FSUnloadFileProc *unLoadProcPtr = NULL;
    Tcl_UniChar ch;

    if ((objc < 2) || (objc > 4)) {
	Tcl_WrongNumArgs(interp, 1, objv, "fileName ?packageName? ?interp?");
	return TCL_ERROR;
    }
    if (Tcl_FSConvertToPathType(interp, objv[1]) != TCL_OK) {
	return TCL_ERROR;
    }
    fullFileName = Tcl_GetString(objv[1]);

    Tcl_DStringInit(&pkgName);
    Tcl_DStringInit(&initName);
    Tcl_DStringInit(&safeInitName);
    Tcl_DStringInit(&unloadName);
    Tcl_DStringInit(&safeUnloadName);
    Tcl_DStringInit(&tmp);

    packageName = NULL;
    if (objc >= 3) {
	packageName = Tcl_GetString(objv[2]);
	if (packageName[0] == '\0') {
	    packageName = NULL;
	}
    }
    if ((fullFileName[0] == 0) && (packageName == NULL)) {
	Tcl_SetResult(interp,
		"must specify either file name or package name",
		TCL_STATIC);
	code = TCL_ERROR;
	goto done;
    }

    /*
     * Figure out which interpreter we're going to load the package into.
     */

    target = interp;
    if (objc == 4) {
	char *slaveIntName = Tcl_GetString(objv[3]);

	target = Tcl_GetSlave(interp, slaveIntName);
	if (target == NULL) {
	    code = TCL_ERROR;
	    goto done;
	}
    }

    /*
     * Scan through the packages that are currently loaded to see if the
     * package we want is already loaded. We'll use a loaded package if it
     * meets any of the following conditions:
     *  - Its name and file match the once we're looking for.
     *  - Its file matches, and we weren't given a name.
     *  - Its name matches, the file name was specified as empty, and there is
     *	  only no statically loaded package with the same name.
     */

    Tcl_MutexLock(&packageMutex);

    defaultPtr = NULL;
    for (pkgPtr = firstPackagePtr; pkgPtr != NULL; pkgPtr = pkgPtr->nextPtr) {
	if (packageName == NULL) {
	    namesMatch = 0;
	} else {
	    Tcl_DStringSetLength(&pkgName, 0);
	    Tcl_DStringAppend(&pkgName, packageName, -1);
	    Tcl_DStringSetLength(&tmp, 0);
	    Tcl_DStringAppend(&tmp, pkgPtr->packageName, -1);
	    Tcl_UtfToLower(Tcl_DStringValue(&pkgName));
	    Tcl_UtfToLower(Tcl_DStringValue(&tmp));
	    if (strcmp(Tcl_DStringValue(&tmp),
		    Tcl_DStringValue(&pkgName)) == 0) {
		namesMatch = 1;
	    } else {
		namesMatch = 0;
	    }
	}
	Tcl_DStringSetLength(&pkgName, 0);

	filesMatch = (strcmp(pkgPtr->fileName, fullFileName) == 0);
	if (filesMatch && (namesMatch || (packageName == NULL))) {
	    break;
	}
	if (namesMatch && (fullFileName[0] == 0)) {
	    defaultPtr = pkgPtr;
	}
	if (filesMatch && !namesMatch && (fullFileName[0] != 0)) {
	    /*
	     * Can't have two different packages loaded from the same file.
	     */

	    Tcl_AppendResult(interp, "file \"", fullFileName,
		    "\" is already loaded for package \"",
		    pkgPtr->packageName, "\"", NULL);
	    code = TCL_ERROR;
	    Tcl_MutexUnlock(&packageMutex);
	    goto done;
	}
    }
    Tcl_MutexUnlock(&packageMutex);
    if (pkgPtr == NULL) {
	pkgPtr = defaultPtr;
    }

    /*
     * Scan through the list of packages already loaded in the target
     * interpreter. If the package we want is already loaded there, then
     * there's nothing for us to do.
     */

    if (pkgPtr != NULL) {
	ipFirstPtr = (InterpPackage *) Tcl_GetAssocData(target,
		"tclLoad", NULL);
	for (ipPtr = ipFirstPtr; ipPtr != NULL; ipPtr = ipPtr->nextPtr) {
	    if (ipPtr->pkgPtr == pkgPtr) {
		code = TCL_OK;
		goto done;
	    }
	}
    }

    if (pkgPtr == NULL) {
	/*
	 * The desired file isn't currently loaded, so load it. It's an error
	 * if the desired package is a static one.
	 */

	if (fullFileName[0] == 0) {
	    Tcl_AppendResult(interp, "package \"", packageName,
		    "\" isn't loaded statically", NULL);
	    code = TCL_ERROR;
	    goto done;
	}

	/*
	 * Figure out the module name if it wasn't provided explicitly.
	 */

	if (packageName != NULL) {
	    Tcl_DStringAppend(&pkgName, packageName, -1);
	} else {
	    int retc;

	    /*
	     * Threading note - this call used to be protected by a mutex.
	     */

	    retc = TclGuessPackageName(fullFileName, &pkgName);
	    if (!retc) {
		Tcl_Obj *splitPtr;
		Tcl_Obj *pkgGuessPtr;
		int pElements;
		char *pkgGuess;

		/*
		 * The platform-specific code couldn't figure out the module
		 * name. Make a guess by taking the last element of the file
		 * name, stripping off any leading "lib", and then using all
		 * of the alphabetic and underline characters that follow
		 * that.
		 */

		splitPtr = Tcl_FSSplitPath(objv[1], &pElements);
		Tcl_ListObjIndex(NULL, splitPtr, pElements -1, &pkgGuessPtr);
		pkgGuess = Tcl_GetString(pkgGuessPtr);
		if ((pkgGuess[0] == 'l') && (pkgGuess[1] == 'i')
			&& (pkgGuess[2] == 'b')) {
		    pkgGuess += 3;
		}
		for (p = pkgGuess; *p != 0; p += offset) {
		    offset = Tcl_UtfToUniChar(p, &ch);
		    if ((ch > 0x100)
			    || !(isalpha(UCHAR(ch)) /* INTL: ISO only */
				    || (UCHAR(ch) == '_'))) {
			break;
		    }
		}
		if (p == pkgGuess) {
		    Tcl_DecrRefCount(splitPtr);
		    Tcl_AppendResult(interp,
			    "couldn't figure out package name for ",
			    fullFileName, NULL);
		    code = TCL_ERROR;
		    goto done;
		}
		Tcl_DStringAppend(&pkgName, pkgGuess, (p - pkgGuess));
		Tcl_DecrRefCount(splitPtr);
	    }
	}

	/*
	 * Fix the capitalization in the package name so that the first
	 * character is in caps (or title case) but the others are all
	 * lower-case.
	 */

	Tcl_DStringSetLength(&pkgName,
		Tcl_UtfToTitle(Tcl_DStringValue(&pkgName)));

	/*
	 * Compute the names of the two initialization functions, based on the
	 * package name.
	 */

	Tcl_DStringAppend(&initName, Tcl_DStringValue(&pkgName), -1);
	Tcl_DStringAppend(&initName, "_Init", 5);
	Tcl_DStringAppend(&safeInitName, Tcl_DStringValue(&pkgName), -1);
	Tcl_DStringAppend(&safeInitName, "_SafeInit", 9);
	Tcl_DStringAppend(&unloadName, Tcl_DStringValue(&pkgName), -1);
	Tcl_DStringAppend(&unloadName, "_Unload", 7);
	Tcl_DStringAppend(&safeUnloadName, Tcl_DStringValue(&pkgName), -1);
	Tcl_DStringAppend(&safeUnloadName, "_SafeUnload", 11);

	/*
	 * Call platform-specific code to load the package and find the two
	 * initialization functions.
	 */

	symbols[0] = Tcl_DStringValue(&initName);
	symbols[1] = Tcl_DStringValue(&safeInitName);
	symbols[2] = Tcl_DStringValue(&unloadName);
	symbols[3] = Tcl_DStringValue(&safeUnloadName);
	procPtrs[0] = &initProc;
	procPtrs[1] = &safeInitProc;
	procPtrs[2] = &unloadProc;
	procPtrs[3] = &safeUnloadProc;

	Tcl_MutexLock(&packageMutex);
	code = TclLoadFile(interp, objv[1], 4, symbols, procPtrs,
		&loadHandle, &clientData, &unLoadProcPtr);
	Tcl_MutexUnlock(&packageMutex);
	loadHandle = (Tcl_LoadHandle) clientData;
	if (code != TCL_OK) {
	    goto done;
	}

	if (*procPtrs[0] /* initProc */ == NULL) {
	    Tcl_AppendResult(interp, "couldn't find procedure ",
		    Tcl_DStringValue(&initName), NULL);
	    if (unLoadProcPtr != NULL) {
		(*unLoadProcPtr)(loadHandle);
	    }
	    code = TCL_ERROR;
	    goto done;
	}

	/*
	 * Create a new record to describe this package.
	 */

	pkgPtr = (LoadedPackage *) ckalloc(sizeof(LoadedPackage));
	pkgPtr->fileName	   = (char *) ckalloc((unsigned)
		(strlen(fullFileName) + 1));
	strcpy(pkgPtr->fileName, fullFileName);
	pkgPtr->packageName	   = (char *) ckalloc((unsigned)
		(Tcl_DStringLength(&pkgName) + 1));
	strcpy(pkgPtr->packageName, Tcl_DStringValue(&pkgName));
	pkgPtr->loadHandle	   = loadHandle;
	pkgPtr->unLoadProcPtr	   = unLoadProcPtr;
	pkgPtr->initProc	   = *procPtrs[0];
	pkgPtr->safeInitProc	   = *procPtrs[1];
	pkgPtr->unloadProc	   = (Tcl_PackageUnloadProc*) *procPtrs[2];
	pkgPtr->safeUnloadProc	   = (Tcl_PackageUnloadProc*) *procPtrs[3];
	pkgPtr->interpRefCount	   = 0;
	pkgPtr->safeInterpRefCount = 0;

	Tcl_MutexLock(&packageMutex);
	pkgPtr->nextPtr		   = firstPackagePtr;
	firstPackagePtr		   = pkgPtr;
	Tcl_MutexUnlock(&packageMutex);
    }

    /*
     * Invoke the package's initialization function (either the normal one or
     * the safe one, depending on whether or not the interpreter is safe).
     */

    if (Tcl_IsSafe(target)) {
	if (pkgPtr->safeInitProc != NULL) {
	    code = (*pkgPtr->safeInitProc)(target);
	} else {
	    Tcl_AppendResult(interp,
		    "can't use package in a safe interpreter: no ",
		    pkgPtr->packageName, "_SafeInit procedure", NULL);
	    code = TCL_ERROR;
	    goto done;
	}
    } else {
	code = (*pkgPtr->initProc)(target);
    }

    /*
     * Record the fact that the package has been loaded in the target
     * interpreter.
     */

    if (code == TCL_OK) {
	/*
	 * Update the proper reference count.
	 */

	Tcl_MutexLock(&packageMutex);
	if (Tcl_IsSafe(target)) {
	    ++pkgPtr->safeInterpRefCount;
	} else {
	    ++pkgPtr->interpRefCount;
	}
	Tcl_MutexUnlock(&packageMutex);

	/*
	 * Refetch ipFirstPtr: loading the package may have introduced
	 * additional static packages at the head of the linked list!
	 */

	ipFirstPtr = (InterpPackage *) Tcl_GetAssocData(target,
		"tclLoad", NULL);
	ipPtr = (InterpPackage *) ckalloc(sizeof(InterpPackage));
	ipPtr->pkgPtr = pkgPtr;
	ipPtr->nextPtr = ipFirstPtr;
	Tcl_SetAssocData(target, "tclLoad", LoadCleanupProc,
		(ClientData) ipPtr);
    } else {
	TclTransferResult(target, code, interp);
    }

  done:
    Tcl_DStringFree(&pkgName);
    Tcl_DStringFree(&initName);
    Tcl_DStringFree(&safeInitName);
    Tcl_DStringFree(&unloadName);
    Tcl_DStringFree(&safeUnloadName);
    Tcl_DStringFree(&tmp);
    return code;
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_UnloadObjCmd --
 *
 *	This function is invoked to process the "unload" Tcl command. See the
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
Tcl_UnloadObjCmd(
    ClientData dummy,		/* Not used. */
    Tcl_Interp *interp,		/* Current interpreter. */
    int objc,			/* Number of arguments. */
    Tcl_Obj *const objv[])	/* Argument objects. */
{
    Tcl_Interp *target;		/* Which interpreter to unload from. */
    LoadedPackage *pkgPtr, *defaultPtr;
    Tcl_DString pkgName, tmp;
    Tcl_PackageUnloadProc *unloadProc;
    InterpPackage *ipFirstPtr, *ipPtr;
    int i, index, code, complain = 1, keepLibrary = 0;
    int trustedRefCount = -1, safeRefCount = -1;
    const char *fullFileName = "";
    char *packageName;
    static const char *options[] = {
	"-nocomplain", "-keeplibrary", "--", NULL
    };
    enum options {
	UNLOAD_NOCOMPLAIN, UNLOAD_KEEPLIB, UNLOAD_LAST
    };

    for (i = 1; i < objc; i++) {
	if (Tcl_GetIndexFromObj(interp, objv[i], options, "option", 0,
		&index) != TCL_OK) {
	    fullFileName = Tcl_GetString(objv[i]);
	    if (fullFileName[0] == '-') {
		/*
		 * It looks like the command contains an option so signal an
		 * error
		 */

		return TCL_ERROR;
	    } else {
		/*
		 * This clearly isn't an option; assume it's the filename. We
		 * must clear the error.
		 */

		Tcl_ResetResult(interp);
		break;
	    }
	}
	switch (index) {
	case UNLOAD_NOCOMPLAIN:		/* -nocomplain */
	    complain = 0;
	    break;
	case UNLOAD_KEEPLIB:		/* -keeplibrary */
	    keepLibrary = 1;
	    break;
	case UNLOAD_LAST:		/* -- */
	    i++;
	    goto endOfForLoop;
	}
    }
  endOfForLoop:
    if ((objc-i < 1) || (objc-i > 3)) {
	Tcl_WrongNumArgs(interp, 1, objv,
		"?switches? fileName ?packageName? ?interp?");
	return TCL_ERROR;
    }
    if (Tcl_FSConvertToPathType(interp, objv[i]) != TCL_OK) {
	return TCL_ERROR;
    }

    fullFileName = Tcl_GetString(objv[i]);
    Tcl_DStringInit(&pkgName);
    Tcl_DStringInit(&tmp);

    packageName = NULL;
    if (objc - i >= 2) {
	packageName = Tcl_GetString(objv[i+1]);
	if (packageName[0] == '\0') {
	    packageName = NULL;
	}
    }
    if ((fullFileName[0] == 0) && (packageName == NULL)) {
	Tcl_SetResult(interp,
		"must specify either file name or package name",
		TCL_STATIC);
	code = TCL_ERROR;
	goto done;
    }

    /*
     * Figure out which interpreter we're going to load the package into.
     */

    target = interp;
    if (objc - i == 3) {
	char *slaveIntName;
	slaveIntName = Tcl_GetString(objv[i+2]);
	target = Tcl_GetSlave(interp, slaveIntName);
	if (target == NULL) {
	    return TCL_ERROR;
	}
    }

    /*
     * Scan through the packages that are currently loaded to see if the
     * package we want is already loaded. We'll use a loaded package if it
     * meets any of the following conditions:
     *  - Its name and file match the once we're looking for.
     *  - Its file matches, and we weren't given a name.
     *  - Its name matches, the file name was specified as empty, and there is
     *	  only no statically loaded package with the same name.
     */

    Tcl_MutexLock(&packageMutex);

    defaultPtr = NULL;
    for (pkgPtr = firstPackagePtr; pkgPtr != NULL; pkgPtr = pkgPtr->nextPtr) {
	int namesMatch, filesMatch;

	if (packageName == NULL) {
	    namesMatch = 0;
	} else {
	    Tcl_DStringSetLength(&pkgName, 0);
	    Tcl_DStringAppend(&pkgName, packageName, -1);
	    Tcl_DStringSetLength(&tmp, 0);
	    Tcl_DStringAppend(&tmp, pkgPtr->packageName, -1);
	    Tcl_UtfToLower(Tcl_DStringValue(&pkgName));
	    Tcl_UtfToLower(Tcl_DStringValue(&tmp));
	    if (strcmp(Tcl_DStringValue(&tmp),
		    Tcl_DStringValue(&pkgName)) == 0) {
		namesMatch = 1;
	    } else {
		namesMatch = 0;
	    }
	}
	Tcl_DStringSetLength(&pkgName, 0);

	filesMatch = (strcmp(pkgPtr->fileName, fullFileName) == 0);
	if (filesMatch && (namesMatch || (packageName == NULL))) {
	    break;
	}
	if (namesMatch && (fullFileName[0] == 0)) {
	    defaultPtr = pkgPtr;
	}
	if (filesMatch && !namesMatch && (fullFileName[0] != 0)) {
	    break;
	}
    }
    Tcl_MutexUnlock(&packageMutex);
    if (fullFileName[0] == 0) {
	/*
	 * It's an error to try unload a static package.
	 */

	Tcl_AppendResult(interp, "package \"", packageName,
		"\" is loaded statically and cannot be unloaded", NULL);
	code = TCL_ERROR;
	goto done;
    }
    if (pkgPtr == NULL) {
	/*
	 * The DLL pointed by the provided filename has never been loaded.
	 */

	Tcl_AppendResult(interp, "file \"", fullFileName,
		"\" has never been loaded", NULL);
	code = TCL_ERROR;
	goto done;
    }

    /*
     * Scan through the list of packages already loaded in the target
     * interpreter. If the package we want is already loaded there, then we
     * should proceed with unloading.
     */

    code = TCL_ERROR;
    if (pkgPtr != NULL) {
	ipFirstPtr = (InterpPackage *) Tcl_GetAssocData(target,
		"tclLoad", NULL);
	for (ipPtr = ipFirstPtr; ipPtr != NULL; ipPtr = ipPtr->nextPtr) {
	    if (ipPtr->pkgPtr == pkgPtr) {
		code = TCL_OK;
		break;
	    }
	}
    }
    if (code != TCL_OK) {
	/*
	 * The package has not been loaded in this interpreter.
	 */

	Tcl_AppendResult(interp, "file \"", fullFileName,
		"\" has never been loaded in this interpreter", NULL);
	code = TCL_ERROR;
	goto done;
    }

    /*
     * Ensure that the DLL can be unloaded. If it is a trusted interpreter,
     * pkgPtr->unloadProc must not be NULL for the DLL to be unloadable. If
     * the interpreter is a safe one, pkgPtr->safeUnloadProc must be non-NULL.
     */

    if (Tcl_IsSafe(target)) {
	if (pkgPtr->safeUnloadProc == NULL) {
	    Tcl_AppendResult(interp, "file \"", fullFileName,
		    "\" cannot be unloaded under a safe interpreter", NULL);
	    code = TCL_ERROR;
	    goto done;
	}
	unloadProc = pkgPtr->safeUnloadProc;
    } else {
	if (pkgPtr->unloadProc == NULL) {
	    Tcl_AppendResult(interp, "file \"", fullFileName,
		    "\" cannot be unloaded under a trusted interpreter", NULL);
	    code = TCL_ERROR;
	    goto done;
	}
	unloadProc = pkgPtr->unloadProc;
    }

    /*
     * We are ready to unload the package. First, evaluate the unload
     * function. If this fails, we cannot proceed with unload. Also, we must
     * specify the proper flag to pass to the unload callback.
     * TCL_UNLOAD_DETACH_FROM_INTERPRETER is defined when the callback should
     * only remove itself from the interpreter; the library will be unloaded
     * in a future call of unload. In case the library will be unloaded just
     * after the callback returns, TCL_UNLOAD_DETACH_FROM_PROCESS is passed.
     */

    code = TCL_UNLOAD_DETACH_FROM_INTERPRETER;
    if (!keepLibrary) {
	Tcl_MutexLock(&packageMutex);
	trustedRefCount = pkgPtr->interpRefCount;
	safeRefCount = pkgPtr->safeInterpRefCount;
	Tcl_MutexUnlock(&packageMutex);

	if (Tcl_IsSafe(target)) {
	    --safeRefCount;
	} else {
	    --trustedRefCount;
	}

	if (safeRefCount <= 0 && trustedRefCount <= 0) {
	    code = TCL_UNLOAD_DETACH_FROM_PROCESS;
	}
    }
    code = (*unloadProc)(target, code);
    if (code != TCL_OK) {
	TclTransferResult(target, code, interp);
	goto done;
    }

    /*
     * The unload function executed fine. Examine the reference count to see
     * if we unload the DLL.
     */

    Tcl_MutexLock(&packageMutex);
    if (Tcl_IsSafe(target)) {
	--pkgPtr->safeInterpRefCount;

	/*
	 * Do not let counter get negative.
	 */

	if (pkgPtr->safeInterpRefCount < 0) {
	    pkgPtr->safeInterpRefCount = 0;
	}
    } else {
	--pkgPtr->interpRefCount;

	/*
	 * Do not let counter get negative.
	 */

	if (pkgPtr->interpRefCount < 0) {
	    pkgPtr->interpRefCount = 0;
	}
    }
    trustedRefCount = pkgPtr->interpRefCount;
    safeRefCount = pkgPtr->safeInterpRefCount;
    Tcl_MutexUnlock(&packageMutex);

    code = TCL_OK;
    if (pkgPtr->safeInterpRefCount <= 0 && pkgPtr->interpRefCount <= 0
	    && !keepLibrary) {
	/*
	 * Unload the shared library from the application memory...
	 */

#if defined(TCL_UNLOAD_DLLS) || defined(__WIN32__)
	/*
	 * Some Unix dlls are poorly behaved - registering things like atexit
	 * calls that can't be unregistered. If you unload such dlls, you get
	 * a core on exit because it wants to call a function in the dll after
	 * it's been unloaded.
	 */

	if (pkgPtr->fileName[0] != '\0') {
	    Tcl_FSUnloadFileProc *unLoadProcPtr = pkgPtr->unLoadProcPtr;

	    if (unLoadProcPtr != NULL) {
		Tcl_MutexLock(&packageMutex);
		(*unLoadProcPtr)(pkgPtr->loadHandle);

		/*
		 * Remove this library from the loaded library cache.
		 */

		defaultPtr = pkgPtr;
		if (defaultPtr == firstPackagePtr) {
		    firstPackagePtr = pkgPtr->nextPtr;
		} else {
		    for (pkgPtr = firstPackagePtr; pkgPtr != NULL;
			    pkgPtr = pkgPtr->nextPtr) {
			if (pkgPtr->nextPtr == defaultPtr) {
			    pkgPtr->nextPtr = defaultPtr->nextPtr;
			    break;
			}
		    }
		}

		/*
		 * Remove this library from the interpreter's library cache.
		 */

		ipFirstPtr = (InterpPackage *) Tcl_GetAssocData(target,
			"tclLoad", NULL);
		ipPtr = ipFirstPtr;
		if (ipPtr->pkgPtr == defaultPtr) {
		    ipFirstPtr = ipFirstPtr->nextPtr;
		} else {
		    InterpPackage *ipPrevPtr;

		    for (ipPrevPtr = ipPtr; ipPtr != NULL;
			    ipPrevPtr = ipPtr, ipPtr = ipPtr->nextPtr) {
			if (ipPtr->pkgPtr == pkgPtr) {
			    ipPrevPtr->nextPtr = ipPtr->nextPtr;
			    break;
			}
		    }
		}
		Tcl_SetAssocData(target, "tclLoad", LoadCleanupProc,
			(ClientData) ipFirstPtr);
		ckfree(defaultPtr->fileName);
		ckfree(defaultPtr->packageName);
		ckfree((char *) defaultPtr);
		ckfree((char *) ipPtr);
		Tcl_MutexUnlock(&packageMutex);
	    } else {
		Tcl_AppendResult(interp, "file \"", fullFileName,
			"\" cannot be unloaded: filesystem does not support unloading",
			NULL);
		code = TCL_ERROR;
	    }
	}
#else
	Tcl_AppendResult(interp, "file \"", fullFileName,
		"\" cannot be unloaded: unloading disabled", NULL);
	code = TCL_ERROR;
#endif
    }

  done:
    Tcl_DStringFree(&pkgName);
    Tcl_DStringFree(&tmp);
    if (!complain && code!=TCL_OK) {
	code = TCL_OK;
	Tcl_ResetResult(interp);
    }
    if (code == TCL_OK) {
#if 0
	/*
	 * Result of [unload] was not documented in TIP#100, so force to be
	 * the empty string by commenting this out. DKF.
	 */

	Tcl_Obj *resultObjPtr, *objPtr[2];

	/*
	 * Our result is the two reference counts.
	 */

	objPtr[0] = Tcl_NewIntObj(trustedRefCount);
	objPtr[1] = Tcl_NewIntObj(safeRefCount);
	if (objPtr[0] == NULL || objPtr[1] == NULL) {
	    if (objPtr[0]) {
		Tcl_DecrRefCount(objPtr[0]);
	    }
	    if (objPtr[1]) {
		Tcl_DecrRefCount(objPtr[1]);
	    }
	} else {
	    resultObjPtr = Tcl_NewListObj(2, objPtr);
	    if (resultObjPtr != NULL) {
		Tcl_SetObjResult(interp, resultObjPtr);
	    }
	}
#endif
    }
    return code;
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_StaticPackage --
 *
 *	This function is invoked to indicate that a particular package has
 *	been linked statically with an application.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	Once this function completes, the package becomes loadable via the
 *	"load" command with an empty file name.
 *
 *----------------------------------------------------------------------
 */

void
Tcl_StaticPackage(
    Tcl_Interp *interp,		/* If not NULL, it means that the package has
				 * already been loaded into the given
				 * interpreter by calling the appropriate init
				 * proc. */
    const char *pkgName,	/* Name of package (must be properly
				 * capitalized: first letter upper case,
				 * others lower case). */
    Tcl_PackageInitProc *initProc,
				/* Function to call to incorporate this
				 * package into a trusted interpreter. */
    Tcl_PackageInitProc *safeInitProc)
				/* Function to call to incorporate this
				 * package into a safe interpreter (one that
				 * will execute untrusted scripts). NULL means
				 * the package can't be used in safe
				 * interpreters. */
{
    LoadedPackage *pkgPtr;
    InterpPackage *ipPtr, *ipFirstPtr;

    /*
     * Check to see if someone else has already reported this package as
     * statically loaded in the process.
     */

    Tcl_MutexLock(&packageMutex);
    for (pkgPtr = firstPackagePtr; pkgPtr != NULL; pkgPtr = pkgPtr->nextPtr) {
	if ((pkgPtr->initProc == initProc)
		&& (pkgPtr->safeInitProc == safeInitProc)
		&& (strcmp(pkgPtr->packageName, pkgName) == 0)) {
	    break;
	}
    }
    Tcl_MutexUnlock(&packageMutex);

    /*
     * If the package is not yet recorded as being loaded statically, add it
     * to the list now.
     */

    if ( pkgPtr == NULL ) {
	pkgPtr = (LoadedPackage *) ckalloc(sizeof(LoadedPackage));
	pkgPtr->fileName	= (char *) ckalloc((unsigned) 1);
	pkgPtr->fileName[0]	= 0;
	pkgPtr->packageName	= (char *)
		ckalloc((unsigned) (strlen(pkgName) + 1));
	strcpy(pkgPtr->packageName, pkgName);
	pkgPtr->loadHandle	= NULL;
	pkgPtr->initProc	= initProc;
	pkgPtr->safeInitProc	= safeInitProc;
	Tcl_MutexLock(&packageMutex);
	pkgPtr->nextPtr		= firstPackagePtr;
	firstPackagePtr		= pkgPtr;
	Tcl_MutexUnlock(&packageMutex);
    }

    if (interp != NULL) {

	/*
	 * If we're loading the package into an interpreter, determine whether
	 * it's already loaded.
	 */

	ipFirstPtr = (InterpPackage *) Tcl_GetAssocData(interp,
		"tclLoad", NULL);
	for ( ipPtr = ipFirstPtr; ipPtr != NULL; ipPtr = ipPtr->nextPtr ) {
	    if ( ipPtr->pkgPtr == pkgPtr ) {
		return;
	    }
	}

	/*
	 * Package isn't loade in the current interp yet. Mark it as now being
	 * loaded.
	 */

	ipPtr = (InterpPackage *) ckalloc(sizeof(InterpPackage));
	ipPtr->pkgPtr = pkgPtr;
	ipPtr->nextPtr = ipFirstPtr;
	Tcl_SetAssocData(interp, "tclLoad", LoadCleanupProc,
		(ClientData) ipPtr);
    }
}

/*
 *----------------------------------------------------------------------
 *
 * TclGetLoadedPackages --
 *
 *	This function returns information about all of the files that are
 *	loaded (either in a particular intepreter, or for all interpreters).
 *
 * Results:
 *	The return value is a standard Tcl completion code. If successful, a
 *	list of lists is placed in the interp's result. Each sublist
 *	corresponds to one loaded file; its first element is the name of the
 *	file (or an empty string for something that's statically loaded) and
 *	the second element is the name of the package in that file.
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */

int
TclGetLoadedPackages(
    Tcl_Interp *interp,		/* Interpreter in which to return information
				 * or error message. */
    char *targetName)		/* Name of target interpreter or NULL. If
				 * NULL, return info about all interps;
				 * otherwise, just return info about this
				 * interpreter. */
{
    Tcl_Interp *target;
    LoadedPackage *pkgPtr;
    InterpPackage *ipPtr;
    const char *prefix;

    if (targetName == NULL) {
	/*
	 * Return information about all of the available packages.
	 */

	prefix = "{";
	Tcl_MutexLock(&packageMutex);
	for (pkgPtr = firstPackagePtr; pkgPtr != NULL;
		pkgPtr = pkgPtr->nextPtr) {
	    Tcl_AppendResult(interp, prefix, NULL);
	    Tcl_AppendElement(interp, pkgPtr->fileName);
	    Tcl_AppendElement(interp, pkgPtr->packageName);
	    Tcl_AppendResult(interp, "}", NULL);
	    prefix = " {";
	}
	Tcl_MutexUnlock(&packageMutex);
	return TCL_OK;
    }

    /*
     * Return information about only the packages that are loaded in a given
     * interpreter.
     */

    target = Tcl_GetSlave(interp, targetName);
    if (target == NULL) {
	return TCL_ERROR;
    }
    ipPtr = (InterpPackage *) Tcl_GetAssocData(target, "tclLoad", NULL);
    prefix = "{";
    for ( ; ipPtr != NULL; ipPtr = ipPtr->nextPtr) {
	pkgPtr = ipPtr->pkgPtr;
	Tcl_AppendResult(interp, prefix, NULL);
	Tcl_AppendElement(interp, pkgPtr->fileName);
	Tcl_AppendElement(interp, pkgPtr->packageName);
	Tcl_AppendResult(interp, "}", NULL);
	prefix = " {";
    }
    return TCL_OK;
}

/*
 *----------------------------------------------------------------------
 *
 * LoadCleanupProc --
 *
 *	This function is called to delete all of the InterpPackage structures
 *	for an interpreter when the interpreter is deleted. It gets invoked
 *	via the Tcl AssocData mechanism.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	Storage for all of the InterpPackage functions for interp get deleted.
 *
 *----------------------------------------------------------------------
 */

static void
LoadCleanupProc(
    ClientData clientData,	/* Pointer to first InterpPackage structure
				 * for interp. */
    Tcl_Interp *interp)		/* Interpreter that is being deleted. */
{
    InterpPackage *ipPtr, *nextPtr;

    ipPtr = (InterpPackage *) clientData;
    while (ipPtr != NULL) {
	nextPtr = ipPtr->nextPtr;
	ckfree((char *) ipPtr);
	ipPtr = nextPtr;
    }
}

/*
 *----------------------------------------------------------------------
 *
 * TclFinalizeLoad --
 *
 *	This function is invoked just before the application exits. It frees
 *	all of the LoadedPackage structures.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	Memory is freed.
 *
 *----------------------------------------------------------------------
 */

void
TclFinalizeLoad(void)
{
    LoadedPackage *pkgPtr;

    /*
     * No synchronization here because there should just be one thread alive
     * at this point. Logically, packageMutex should be grabbed at this point,
     * but the Mutexes get finalized before the call to this routine. The
     * only subsystem left alive at this point is the memory allocator.
     */

    while (firstPackagePtr != NULL) {
	pkgPtr = firstPackagePtr;
	firstPackagePtr = pkgPtr->nextPtr;

#if defined(TCL_UNLOAD_DLLS) || defined(__WIN32__)
	/*
	 * Some Unix dlls are poorly behaved - registering things like atexit
	 * calls that can't be unregistered. If you unload such dlls, you get
	 * a core on exit because it wants to call a function in the dll after
	 * it has been unloaded.
	 */

	if (pkgPtr->fileName[0] != '\0') {
	    Tcl_FSUnloadFileProc *unLoadProcPtr = pkgPtr->unLoadProcPtr;
	    if (unLoadProcPtr != NULL) {
		(*unLoadProcPtr)(pkgPtr->loadHandle);
	    }
	}
#endif

	ckfree(pkgPtr->fileName);
	ckfree(pkgPtr->packageName);
	ckfree((char *) pkgPtr);
    }
}

/*
 * Local Variables:
 * mode: c
 * c-basic-offset: 4
 * fill-column: 78
 * End:
 */
