/*
 * tclEnv.c --
 *
 *	Tcl support for environment variables, including a setenv function.
 *	This file contains the generic portion of the environment module. It
 *	is primarily responsible for keeping the "env" arrays in sync with the
 *	system environment variables.
 *
 * Copyright (c) 1991-1994 The Regents of the University of California.
 * Copyright (c) 1994-1998 Sun Microsystems, Inc.
 *
 * See the file "license.terms" for information on usage and redistribution of
 * this file, and for a DISCLAIMER OF ALL WARRANTIES.
 *
 * RCS: @(#) $Id: tclEnv.c,v 1.37 2007/12/13 15:23:16 dgp Exp $
 */

#include "tclInt.h"

TCL_DECLARE_MUTEX(envMutex)	/* To serialize access to environ. */

static struct {
    int cacheSize;		/* Number of env strings in cache. */
    char **cache;		/* Array containing all of the environment
				 * strings that Tcl has allocated. */
#ifndef USE_PUTENV
    char **ourEnviron;		/* Cache of the array that we allocate. We
				 * need to track this in case another
				 * subsystem swaps around the environ array
				 * like we do. */
    int ourEnvironSize;		/* Non-zero means that the environ array was
				 * malloced and has this many total entries
				 * allocated to it (not all may be in use at
				 * once). Zero means that the environment
				 * array is in its original static state. */
#endif
} env;

/*
 * Declarations for local functions defined in this file:
 */

static char *		EnvTraceProc(ClientData clientData, Tcl_Interp *interp,
			    const char *name1, const char *name2, int flags);
static void		ReplaceString(const char *oldStr, char *newStr);
MODULE_SCOPE void	TclSetEnv(const char *name, const char *value);
MODULE_SCOPE void	TclUnsetEnv(const char *name);
#if defined(__CYGWIN__) && defined(__WIN32__)
static void		TclCygwinPutenv(const char *string);
#endif

/*
 *----------------------------------------------------------------------
 *
 * TclSetupEnv --
 *
 *	This function is invoked for an interpreter to make environment
 *	variables accessible from that interpreter via the "env" associative
 *	array.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	The interpreter is added to a list of interpreters managed by us, so
 *	that its view of envariables can be kept consistent with the view in
 *	other interpreters. If this is the first call to TclSetupEnv, then
 *	additional initialization happens, such as copying the environment to
 *	dynamically-allocated space for ease of management.
 *
 *----------------------------------------------------------------------
 */

void
TclSetupEnv(
    Tcl_Interp *interp)		/* Interpreter whose "env" array is to be
				 * managed. */
{
    Tcl_DString envString;
    char *p1, *p2;
    int i;

    /*
     * Synchronize the values in the environ array with the contents of the
     * Tcl "env" variable. To do this:
     *    1) Remove the trace that fires when the "env" var is unset.
     *    2) Unset the "env" variable.
     *    3) If there are no environ variables, create an empty "env" array.
     *	     Otherwise populate the array with current values.
     *    4) Add a trace that synchronizes the "env" array.
     */

    Tcl_UntraceVar2(interp, "env", NULL,
	    TCL_GLOBAL_ONLY | TCL_TRACE_WRITES | TCL_TRACE_UNSETS |
	    TCL_TRACE_READS | TCL_TRACE_ARRAY, EnvTraceProc, NULL);

    Tcl_UnsetVar2(interp, "env", NULL, TCL_GLOBAL_ONLY);

    if (environ[0] == NULL) {
	Tcl_Obj *varNamePtr;

	TclNewLiteralStringObj(varNamePtr, "env");
	Tcl_IncrRefCount(varNamePtr);
	TclArraySet(interp, varNamePtr, NULL);
	Tcl_DecrRefCount(varNamePtr);
    } else {
	Tcl_MutexLock(&envMutex);
	for (i = 0; environ[i] != NULL; i++) {
	    p1 = Tcl_ExternalToUtfDString(NULL, environ[i], -1, &envString);
	    p2 = strchr(p1, '=');
	    if (p2 == NULL) {
		/*
		 * This condition seem to happen occasionally under some
		 * versions of Solaris; ignore the entry.
		 */

		continue;
	    }
	    p2++;
	    p2[-1] = '\0';
	    Tcl_SetVar2(interp, "env", p1, p2, TCL_GLOBAL_ONLY);
	    Tcl_DStringFree(&envString);
	}
	Tcl_MutexUnlock(&envMutex);
    }

    Tcl_TraceVar2(interp, "env", NULL,
	    TCL_GLOBAL_ONLY | TCL_TRACE_WRITES | TCL_TRACE_UNSETS |
	    TCL_TRACE_READS | TCL_TRACE_ARRAY, EnvTraceProc, NULL);
}

/*
 *----------------------------------------------------------------------
 *
 * TclSetEnv --
 *
 *	Set an environment variable, replacing an existing value or creating a
 *	new variable if there doesn't exist a variable by the given name. This
 *	function is intended to be a stand-in for the UNIX "setenv" function
 *	so that applications using that function will interface properly to
 *	Tcl. To make it a stand-in, the Makefile must define "TclSetEnv" to
 *	"setenv".
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	The environ array gets updated.
 *
 *----------------------------------------------------------------------
 */

void
TclSetEnv(
    const char *name,		/* Name of variable whose value is to be set
				 * (UTF-8). */
    const char *value)		/* New value for variable (UTF-8). */
{
    Tcl_DString envString;
    int index, length, nameLength;
    char *p, *oldValue;
    const char *p2;

    /*
     * Figure out where the entry is going to go. If the name doesn't already
     * exist, enlarge the array if necessary to make room. If the name exists,
     * free its old entry.
     */

    Tcl_MutexLock(&envMutex);
    index = TclpFindVariable(name, &length);

    if (index == -1) {
#ifndef USE_PUTENV
	/*
	 * We need to handle the case where the environment may be changed
	 * outside our control. ourEnvironSize is only valid if the current
	 * environment is the one we allocated. [Bug 979640]
	 */

	if ((env.ourEnviron != environ) || (length+2 > env.ourEnvironSize)) {
	    char **newEnviron = (char **)
		    ckalloc(((unsigned) length + 5) * sizeof(char *));

	    memcpy(newEnviron, environ, length * sizeof(char *));
	    if ((env.ourEnvironSize != 0) && (env.ourEnviron != NULL)) {
		ckfree((char *) env.ourEnviron);
	    }
	    environ = env.ourEnviron = newEnviron;
	    env.ourEnvironSize = length + 5;
	}
	index = length;
	environ[index + 1] = NULL;
#endif /* USE_PUTENV */
	oldValue = NULL;
	nameLength = strlen(name);
    } else {
	const char *env;

	/*
	 * Compare the new value to the existing value. If they're the same
	 * then quit immediately (e.g. don't rewrite the value or propagate it
	 * to other interpreters). Otherwise, when there are N interpreters
	 * there will be N! propagations of the same value among the
	 * interpreters.
	 */

	env = Tcl_ExternalToUtfDString(NULL, environ[index], -1, &envString);
	if (strcmp(value, env + (length + 1)) == 0) {
	    Tcl_DStringFree(&envString);
	    Tcl_MutexUnlock(&envMutex);
	    return;
	}
	Tcl_DStringFree(&envString);

	oldValue = environ[index];
	nameLength = length;
    }

    /*
     * Create a new entry. Build a complete UTF string that contains a
     * "name=value" pattern. Then convert the string to the native encoding,
     * and set the environ array value.
     */

    p = ckalloc((unsigned) nameLength + strlen(value) + 2);
    strcpy(p, name);
    p[nameLength] = '=';
    strcpy(p+nameLength+1, value);
    p2 = Tcl_UtfToExternalDString(NULL, p, -1, &envString);

    /*
     * Copy the native string to heap memory.
     */

    p = ckrealloc(p, strlen(p2) + 1);
    strcpy(p, p2);
    Tcl_DStringFree(&envString);

#ifdef USE_PUTENV
    /*
     * Update the system environment.
     */

    putenv(p);
    index = TclpFindVariable(name, &length);
#else
    environ[index] = p;
#endif /* USE_PUTENV */

    /*
     * Watch out for versions of putenv that copy the string (e.g. VC++). In
     * this case we need to free the string immediately. Otherwise update the
     * string in the cache.
     */

    if ((index != -1) && (environ[index] == p)) {
	ReplaceString(oldValue, p);
#ifdef HAVE_PUTENV_THAT_COPIES
    } else {
	/*
	 * This putenv() copies instead of taking ownership.
	 */

	ckfree(p);
#endif /* HAVE_PUTENV_THAT_COPIES */
    }

    Tcl_MutexUnlock(&envMutex);

    if (!strcmp(name, "HOME")) {
	/*
	 * If the user's home directory has changed, we must invalidate the
	 * filesystem cache, because '~' expansions will now be incorrect.
	 */

	Tcl_FSMountsChanged(NULL);
    }
}

/*
 *----------------------------------------------------------------------
 *
 * Tcl_PutEnv --
 *
 *	Set an environment variable. Similar to setenv except that the
 *	information is passed in a single string of the form NAME=value,
 *	rather than as separate name strings. This function is intended to be
 *	a stand-in for the UNIX "putenv" function so that applications using
 *	that function will interface properly to Tcl. To make it a stand-in,
 *	the Makefile will define "Tcl_PutEnv" to "putenv".
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	The environ array gets updated, as do all of the interpreters that we
 *	manage.
 *
 *----------------------------------------------------------------------
 */

int
Tcl_PutEnv(
    const char *assignment)	/* Info about environment variable in the form
				 * NAME=value. (native) */
{
    Tcl_DString nameString;
    const char *name;
    char *value;

    if (assignment == NULL) {
	return 0;
    }

    /*
     * First convert the native string to UTF. Then separate the string into
     * name and value parts, and call TclSetEnv to do all of the real work.
     */

    name = Tcl_ExternalToUtfDString(NULL, assignment, -1, &nameString);
    value = strchr(name, '=');

    if ((value != NULL) && (value != name)) {
	value[0] = '\0';
	TclSetEnv(name, value+1);
    }

    Tcl_DStringFree(&nameString);
    return 0;
}

/*
 *----------------------------------------------------------------------
 *
 * TclUnsetEnv --
 *
 *	Remove an environment variable, updating the "env" arrays in all
 *	interpreters managed by us. This function is intended to replace the
 *	UNIX "unsetenv" function (but to do this the Makefile must be modified
 *	to redefine "TclUnsetEnv" to "unsetenv".
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	Interpreters are updated, as is environ.
 *
 *----------------------------------------------------------------------
 */

void
TclUnsetEnv(
    const char *name)		/* Name of variable to remove (UTF-8). */
{
    char *oldValue;
    int length;
    int index;
#ifdef USE_PUTENV_FOR_UNSET
    Tcl_DString envString;
    char *string;
#else
    char **envPtr;
#endif /* USE_PUTENV_FOR_UNSET */

    Tcl_MutexLock(&envMutex);
    index = TclpFindVariable(name, &length);

    /*
     * First make sure that the environment variable exists to avoid doing
     * needless work and to avoid recursion on the unset.
     */

    if (index == -1) {
	Tcl_MutexUnlock(&envMutex);
	return;
    }

    /*
     * Remember the old value so we can free it if Tcl created the string.
     */

    oldValue = environ[index];

    /*
     * Update the system environment. This must be done before we update the
     * interpreters or we will recurse.
     */

#ifdef USE_PUTENV_FOR_UNSET
    /*
     * For those platforms that support putenv to unset, Linux indicates
     * that no = should be included, and Windows requires it.
     */

#ifdef WIN32
    string = ckalloc((unsigned) length+2);
    memcpy(string, name, (size_t) length);
    string[length] = '=';
    string[length+1] = '\0';
#else
    string = ckalloc((unsigned) length+1);
    memcpy(string, name, (size_t) length);
    string[length] = '\0';
#endif /* WIN32 */

    Tcl_UtfToExternalDString(NULL, string, -1, &envString);
    string = ckrealloc(string, (unsigned) Tcl_DStringLength(&envString)+1);
    strcpy(string, Tcl_DStringValue(&envString));
    Tcl_DStringFree(&envString);

    putenv(string);

    /*
     * Watch out for versions of putenv that copy the string (e.g. VC++). In
     * this case we need to free the string immediately. Otherwise update the
     * string in the cache.
     */

    if (environ[index] == string) {
	ReplaceString(oldValue, string);
#ifdef HAVE_PUTENV_THAT_COPIES
    } else {
	/*
	 * This putenv() copies instead of taking ownership.
	 */

	ckfree(string);
#endif /* HAVE_PUTENV_THAT_COPIES */
    }
#else /* !USE_PUTENV_FOR_UNSET */
    for (envPtr = environ+index+1; ; envPtr++) {
	envPtr[-1] = *envPtr;
	if (*envPtr == NULL) {
	    break;
	}
    }
    ReplaceString(oldValue, NULL);
#endif /* USE_PUTENV_FOR_UNSET */

    Tcl_MutexUnlock(&envMutex);
}

/*
 *---------------------------------------------------------------------------
 *
 * TclGetEnv --
 *
 *	Retrieve the value of an environment variable.
 *
 * Results:
 *	The result is a pointer to a string specifying the value of the
 *	environment variable, or NULL if that environment variable does not
 *	exist. Storage for the result string is allocated in valuePtr; the
 *	caller must call Tcl_DStringFree() when the result is no longer
 *	needed.
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */

const char *
TclGetEnv(
    const char *name,		/* Name of environment variable to find
				 * (UTF-8). */
    Tcl_DString *valuePtr)	/* Uninitialized or free DString in which the
				 * value of the environment variable is
				 * stored. */
{
    int length, index;
    const char *result;

    Tcl_MutexLock(&envMutex);
    index = TclpFindVariable(name, &length);
    result = NULL;
    if (index != -1) {
	Tcl_DString envStr;

	result = Tcl_ExternalToUtfDString(NULL, environ[index], -1, &envStr);
	result += length;
	if (*result == '=') {
	    result++;
	    Tcl_DStringInit(valuePtr);
	    Tcl_DStringAppend(valuePtr, result, -1);
	    result = Tcl_DStringValue(valuePtr);
	} else {
	    result = NULL;
	}
	Tcl_DStringFree(&envStr);
    }
    Tcl_MutexUnlock(&envMutex);
    return result;
}

/*
 *----------------------------------------------------------------------
 *
 * EnvTraceProc --
 *
 *	This function is invoked whenever an environment variable is read,
 *	modified or deleted. It propagates the change to the global "environ"
 *	array.
 *
 * Results:
 *	Always returns NULL to indicate success.
 *
 * Side effects:
 *	Environment variable changes get propagated. If the whole "env" array
 *	is deleted, then we stop managing things for this interpreter (usually
 *	this happens because the whole interpreter is being deleted).
 *
 *----------------------------------------------------------------------
 */

	/* ARGSUSED */
static char *
EnvTraceProc(
    ClientData clientData,	/* Not used. */
    Tcl_Interp *interp,		/* Interpreter whose "env" variable is being
				 * modified. */
    const char *name1,		/* Better be "env". */
    const char *name2,		/* Name of variable being modified, or NULL if
				 * whole array is being deleted (UTF-8). */
    int flags)			/* Indicates what's happening. */
{
    /*
     * For array traces, let TclSetupEnv do all the work.
     */

    if (flags & TCL_TRACE_ARRAY) {
	TclSetupEnv(interp);
	return NULL;
    }

    /*
     * If name2 is NULL, then return and do nothing.
     */

    if (name2 == NULL) {
	return NULL;
    }

    /*
     * If a value is being set, call TclSetEnv to do all of the work.
     */

    if (flags & TCL_TRACE_WRITES) {
	const char *value;

	value = Tcl_GetVar2(interp, "env", name2, TCL_GLOBAL_ONLY);
	TclSetEnv(name2, value);
    }

    /*
     * If a value is being read, call TclGetEnv to do all of the work.
     */

    if (flags & TCL_TRACE_READS) {
	Tcl_DString valueString;
	const char *value = TclGetEnv(name2, &valueString);

	if (value == NULL) {
	    return "no such variable";
	}
	Tcl_SetVar2(interp, name1, name2, value, 0);
	Tcl_DStringFree(&valueString);
    }

    /*
     * For unset traces, let TclUnsetEnv do all the work.
     */

    if (flags & TCL_TRACE_UNSETS) {
	TclUnsetEnv(name2);
    }
    return NULL;
}

/*
 *----------------------------------------------------------------------
 *
 * ReplaceString --
 *
 *	Replace one string with another in the environment variable cache. The
 *	cache keeps track of all of the environment variables that Tcl has
 *	modified so they can be freed later.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	May free the old string.
 *
 *----------------------------------------------------------------------
 */

static void
ReplaceString(
    const char *oldStr,		/* Old environment string. */
    char *newStr)		/* New environment string. */
{
    int i;

    /*
     * Check to see if the old value was allocated by Tcl. If so, it needs to
     * be deallocated to avoid memory leaks. Note that this algorithm is O(n),
     * not O(1). This will result in n-squared behavior if lots of environment
     * changes are being made.
     */

    for (i = 0; i < env.cacheSize; i++) {
	if (env.cache[i]==oldStr || env.cache[i]==NULL) {
	    break;
	}
    }
    if (i < env.cacheSize) {
	/*
	 * Replace or delete the old value.
	 */

	if (env.cache[i]) {
	    ckfree(env.cache[i]);
	}

	if (newStr) {
	    env.cache[i] = newStr;
	} else {
	    for (; i < env.cacheSize-1; i++) {
		env.cache[i] = env.cache[i+1];
	    }
	    env.cache[env.cacheSize-1] = NULL;
	}
    } else {
	/*
	 * We need to grow the cache in order to hold the new string.
	 */

	const int growth = 5;

	env.cache = (char **) ckrealloc((char *) env.cache,
		(env.cacheSize + growth) * sizeof(char *));
	env.cache[env.cacheSize] = newStr;
	(void) memset(env.cache+env.cacheSize+1, (int) 0,
		(size_t) (growth-1) * sizeof(char*));
	env.cacheSize += growth;
    }
}

/*
 *----------------------------------------------------------------------
 *
 * TclFinalizeEnvironment --
 *
 *	This function releases any storage allocated by this module that isn't
 *	still in use by the global environment. Any strings that are still in
 *	the environment will be leaked.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	May deallocate storage.
 *
 *----------------------------------------------------------------------
 */

void
TclFinalizeEnvironment(void)
{
    /*
     * For now we just deallocate the cache array and none of the environment
     * strings. This may leak more memory that strictly necessary, since some
     * of the strings may no longer be in the environment. However,
     * determining which ones are ok to delete is n-squared, and is pretty
     * unlikely, so we don't bother.
     */

    if (env.cache) {
	ckfree((char *) env.cache);
	env.cache = NULL;
	env.cacheSize = 0;
#ifndef USE_PUTENV
	env.ourEnvironSize = 0;
#endif
    }
}

#if defined(__CYGWIN__) && defined(__WIN32__)

#include <windows.h>

/*
 * When using cygwin, when an environment variable changes, we need to synch
 * with both the cygwin environment (in case the application C code calls
 * fork) and the Windows environment (in case the application TCL code calls
 * exec, which calls the Windows CreateProcess function).
 */

static void
TclCygwinPutenv(
    const char *str)
{
    char *name, *value;

    /*
     * Get the name and value, so that we can change the environment variable
     * for Windows.
     */

    name = alloca(strlen(str) + 1);
    strcpy(name, str);
    for (value=name ; *value!='=' && *value!='\0' ; ++value) {
	/* Empty body */
    }
    if (*value == '\0') {
	/* Can't happen. */
	return;
    }
    *value = '\0';
    ++value;
    if (*value == '\0') {
	value = NULL;
    }

    /*
     * Set the cygwin environment variable.
     */

#undef putenv
    if (value == NULL) {
	unsetenv(name);
    } else {
	putenv(str);
    }

    /*
     * Before changing the environment variable in Windows, if this is PATH,
     * we need to convert the value back to a Windows style path.
     *
     * FIXME: The calling program may know it is running under windows, and
     * may have set the path to a Windows path, or, worse, appended or
     * prepended a Windows path to PATH.
     */

    if (strcmp(name, "PATH") != 0) {
	/*
	 * If this is Path, eliminate any PATH variable, to prevent any
	 * confusion.
	 */

	if (strcmp(name, "Path") == 0) {
	    SetEnvironmentVariable("PATH", NULL);
	    unsetenv("PATH");
	}

	SetEnvironmentVariable(name, value);
    } else {
	char *buf;

	/*
	 * Eliminate any Path variable, to prevent any confusion.
	 */

	SetEnvironmentVariable("Path", NULL);
	unsetenv("Path");

	if (value == NULL) {
	    buf = NULL;
	} else {
	    int size;

	    size = cygwin_posix_to_win32_path_list_buf_size(value);
	    buf = alloca(size + 1);
	    cygwin_posix_to_win32_path_list(value, buf);
	}

	SetEnvironmentVariable(name, buf);
    }
}
#endif /* __CYGWIN__ && __WIN32__ */

/*
 * Local Variables:
 * mode: c
 * c-basic-offset: 4
 * fill-column: 78
 * End:
 */
