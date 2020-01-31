/*
 * tclWinInit.c --
 *
 *	Contains the Windows-specific interpreter initialization functions.
 *
 * Copyright (c) 1994-1997 Sun Microsystems, Inc.
 * Copyright (c) 1998-1999 by Scriptics Corporation.
 * All rights reserved.
 *
 * See the file "license.terms" for information on usage and redistribution of
 * this file, and for a DISCLAIMER OF ALL WARRANTIES.
 *
 * RCS: @(#) $Id: tclWinInit.c,v 1.75 2007/12/13 15:28:44 dgp Exp $
 */

#include "tclWinInt.h"
#include <winnt.h>
#include <winbase.h>
#include <lmcons.h>

/*
 * GetUserName() is found in advapi32.dll
 */
#ifdef _MSC_VER
#   pragma comment(lib, "advapi32.lib")
#endif

/*
 * The following declaration is a workaround for some Microsoft brain damage.
 * The SYSTEM_INFO structure is different in various releases, even though the
 * layout is the same. So we overlay our own structure on top of it so we can
 * access the interesting slots in a uniform way.
 */

typedef struct {
    WORD wProcessorArchitecture;
    WORD wReserved;
} OemId;

/*
 * The following macros are missing from some versions of winnt.h.
 */

#ifndef PROCESSOR_ARCHITECTURE_INTEL
#define PROCESSOR_ARCHITECTURE_INTEL		0
#endif
#ifndef PROCESSOR_ARCHITECTURE_MIPS
#define PROCESSOR_ARCHITECTURE_MIPS		1
#endif
#ifndef PROCESSOR_ARCHITECTURE_ALPHA
#define PROCESSOR_ARCHITECTURE_ALPHA		2
#endif
#ifndef PROCESSOR_ARCHITECTURE_PPC
#define PROCESSOR_ARCHITECTURE_PPC		3
#endif
#ifndef PROCESSOR_ARCHITECTURE_SHX
#define PROCESSOR_ARCHITECTURE_SHX		4
#endif
#ifndef PROCESSOR_ARCHITECTURE_ARM
#define PROCESSOR_ARCHITECTURE_ARM		5
#endif
#ifndef PROCESSOR_ARCHITECTURE_IA64
#define PROCESSOR_ARCHITECTURE_IA64		6
#endif
#ifndef PROCESSOR_ARCHITECTURE_ALPHA64
#define PROCESSOR_ARCHITECTURE_ALPHA64		7
#endif
#ifndef PROCESSOR_ARCHITECTURE_MSIL
#define PROCESSOR_ARCHITECTURE_MSIL		8
#endif
#ifndef PROCESSOR_ARCHITECTURE_AMD64
#define PROCESSOR_ARCHITECTURE_AMD64		9
#endif
#ifndef PROCESSOR_ARCHITECTURE_IA32_ON_WIN64
#define PROCESSOR_ARCHITECTURE_IA32_ON_WIN64	10
#endif
#ifndef PROCESSOR_ARCHITECTURE_UNKNOWN
#define PROCESSOR_ARCHITECTURE_UNKNOWN		0xFFFF
#endif

/*
 * The following arrays contain the human readable strings for the Windows
 * platform and processor values.
 */


#define NUMPLATFORMS 4
static char* platforms[NUMPLATFORMS] = {
    "Win32s", "Windows 95", "Windows NT", "Windows CE"
};

#define NUMPROCESSORS 11
static char* processors[NUMPROCESSORS] = {
    "intel", "mips", "alpha", "ppc", "shx", "arm", "ia64", "alpha64", "msil",
    "amd64", "ia32_on_win64"
};

/*
 * The default directory in which the init.tcl file is expected to be found.
 */

static TclInitProcessGlobalValueProc	InitializeDefaultLibraryDir;
static ProcessGlobalValue defaultLibraryDir =
	{0, 0, NULL, NULL, InitializeDefaultLibraryDir, NULL, NULL};

static void		AppendEnvironment(Tcl_Obj *listPtr, CONST char *lib);
static int		ToUtf(CONST WCHAR *wSrc, char *dst);

/*
 *---------------------------------------------------------------------------
 *
 * TclpInitPlatform --
 *
 *	Initialize all the platform-dependant things like signals and
 *	floating-point error handling.
 *
 *	Called at process initialization time.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	None.
 *
 *---------------------------------------------------------------------------
 */

void
TclpInitPlatform(void)
{
    tclPlatform = TCL_PLATFORM_WINDOWS;

    /*
     * The following code stops Windows 3.X and Windows NT 3.51 from
     * automatically putting up Sharing Violation dialogs, e.g, when someone
     * tries to access a file that is locked or a drive with no disk in it.
     * Tcl already returns the appropriate error to the caller, and they can
     * decide to put up their own dialog in response to that failure.
     *
     * Under 95 and NT 4.0, this is a NOOP because the system doesn't
     * automatically put up dialogs when the above operations fail.
     */

    SetErrorMode(SetErrorMode(0) | SEM_FAILCRITICALERRORS);

#ifdef STATIC_BUILD
    /*
     * If we are in a statically linked executable, then we need to explicitly
     * initialize the Windows function tables here since DllMain() will not be
     * invoked.
     */

    TclWinInit(GetModuleHandle(NULL));
#endif
}

/*
 *-------------------------------------------------------------------------
 *
 * TclpInitLibraryPath --
 *
 *	This is the fallback routine that sets the library path if the
 *	application has not set one by the first time it is needed.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	Sets the library path to an initial value.
 *
 *-------------------------------------------------------------------------
 */

void
TclpInitLibraryPath(
    char **valuePtr,
    int *lengthPtr,
    Tcl_Encoding *encodingPtr)
{
#define LIBRARY_SIZE	    32
    Tcl_Obj *pathPtr;
    char installLib[LIBRARY_SIZE];
    char *bytes;

    pathPtr = Tcl_NewObj();

    /*
     * Initialize the substring used when locating the script library. The
     * installLib variable computes the script library path relative to the
     * installed DLL.
     */

    sprintf(installLib, "lib/tcl%s", TCL_VERSION);

    /*
     * Look for the library relative to the TCL_LIBRARY env variable. If the
     * last dirname in the TCL_LIBRARY path does not match the last dirname in
     * the installLib variable, use the last dir name of installLib in
     * addition to the orginal TCL_LIBRARY path.
     */

    AppendEnvironment(pathPtr, installLib);

    /*
     * Look for the library in its default location.
     */

    Tcl_ListObjAppendElement(NULL, pathPtr,
	    TclGetProcessGlobalValue(&defaultLibraryDir));

    *encodingPtr = NULL;
    bytes = Tcl_GetStringFromObj(pathPtr, lengthPtr);
    *valuePtr = ckalloc((unsigned int)(*lengthPtr)+1);
    memcpy(*valuePtr, bytes, (size_t)(*lengthPtr)+1);
    Tcl_DecrRefCount(pathPtr);
}

/*
 *---------------------------------------------------------------------------
 *
 * AppendEnvironment --
 *
 *	Append the value of the TCL_LIBRARY environment variable onto the path
 *	pointer. If the env variable points to another version of tcl (e.g.
 *	"tcl7.6") also append the path to this version (e.g.,
 *	"tcl7.6/../tcl8.2")
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	None.
 *
 *---------------------------------------------------------------------------
 */

static void
AppendEnvironment(
    Tcl_Obj *pathPtr,
    CONST char *lib)
{
    int pathc;
    WCHAR wBuf[MAX_PATH];
    char buf[MAX_PATH * TCL_UTF_MAX];
    Tcl_Obj *objPtr;
    Tcl_DString ds;
    CONST char **pathv;
    char *shortlib;

    /*
     * The shortlib value needs to be the tail component of the lib path. For
     * example, "lib/tcl8.4" -> "tcl8.4" while "usr/share/tcl8.5" -> "tcl8.5".
     */

    for (shortlib = (char *) &lib[strlen(lib)-1]; shortlib>lib ; shortlib--) {
	if (*shortlib == '/') {
	    if ((unsigned)(shortlib - lib) == strlen(lib) - 1) {
		Tcl_Panic("last character in lib cannot be '/'");
	    }
	    shortlib++;
	    break;
	}
    }
    if (shortlib == lib) {
	Tcl_Panic("no '/' character found in lib");
    }

    /*
     * The "L" preceeding the TCL_LIBRARY string is used to tell VC++ that
     * this is a unicode string.
     */

    if (GetEnvironmentVariableW(L"TCL_LIBRARY", wBuf, MAX_PATH) == 0) {
	buf[0] = '\0';
	GetEnvironmentVariableA("TCL_LIBRARY", buf, MAX_PATH);
    } else {
	ToUtf(wBuf, buf);
    }

    if (buf[0] != '\0') {
	objPtr = Tcl_NewStringObj(buf, -1);
	Tcl_ListObjAppendElement(NULL, pathPtr, objPtr);

	TclWinNoBackslash(buf);
	Tcl_SplitPath(buf, &pathc, &pathv);

	/*
	 * The lstrcmpi() will work even if pathv[pathc-1] is random UTF-8
	 * chars because I know shortlib is ascii.
	 */

	if ((pathc > 0) && (lstrcmpiA(shortlib, pathv[pathc - 1]) != 0)) {
	    CONST char *str;

	    /*
	     * TCL_LIBRARY is set but refers to a different tcl installation
	     * than the current version. Try fiddling with the specified
	     * directory to make it refer to this installation by removing the
	     * old "tclX.Y" and substituting the current version string.
	     */

	    pathv[pathc - 1] = shortlib;
	    Tcl_DStringInit(&ds);
	    str = Tcl_JoinPath(pathc, pathv, &ds);
	    objPtr = Tcl_NewStringObj(str, Tcl_DStringLength(&ds));
	    Tcl_DStringFree(&ds);
	} else {
	    objPtr = Tcl_NewStringObj(buf, -1);
	}
	Tcl_ListObjAppendElement(NULL, pathPtr, objPtr);
	ckfree((char *) pathv);
    }
}

/*
 *---------------------------------------------------------------------------
 *
 * InitializeDefaultLibraryDir --
 *
 *	Locate the Tcl script library default location relative to the
 *	location of the Tcl DLL.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	None.
 *
 *---------------------------------------------------------------------------
 */

static void
InitializeDefaultLibraryDir(
    char **valuePtr,
    int *lengthPtr,
    Tcl_Encoding *encodingPtr)
{
    HMODULE hModule = TclWinGetTclInstance();
    WCHAR wName[MAX_PATH + LIBRARY_SIZE];
    char name[(MAX_PATH + LIBRARY_SIZE) * TCL_UTF_MAX];
    char *end, *p;

    if (GetModuleFileNameW(hModule, wName, MAX_PATH) == 0) {
	GetModuleFileNameA(hModule, name, MAX_PATH);
    } else {
	ToUtf(wName, name);
    }

    end = strrchr(name, '\\');
    *end = '\0';
    p = strrchr(name, '\\');
    if (p != NULL) {
	end = p;
    }
    *end = '\\';

    TclWinNoBackslash(name);
    sprintf(end + 1, "lib/tcl%s", TCL_VERSION);
    *lengthPtr = strlen(name);
    *valuePtr = ckalloc((unsigned int) *lengthPtr + 1);
    *encodingPtr = NULL;
    memcpy(*valuePtr, name, (size_t) *lengthPtr + 1);
}

/*
 *---------------------------------------------------------------------------
 *
 * ToUtf --
 *
 *	Convert a char string to a UTF string.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	None.
 *
 *---------------------------------------------------------------------------
 */

static int
ToUtf(
    CONST WCHAR *wSrc,
    char *dst)
{
    char *start;

    start = dst;
    while (*wSrc != '\0') {
	dst += Tcl_UniCharToUtf(*wSrc, dst);
	wSrc++;
    }
    *dst = '\0';
    return (int) (dst - start);
}

/*
 *---------------------------------------------------------------------------
 *
 * TclWinEncodingsCleanup --
 *
 *	Reset information to its original state in finalization to allow for
 *	reinitialization to be possible. This must not be called until after
 *	the filesystem has been finalised, or exit crashes may occur when
 *	using virtual filesystems.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	Static information reset to startup state.
 *
 *---------------------------------------------------------------------------
 */

void
TclWinEncodingsCleanup(void)
{
    TclWinResetInterfaceEncodings();
}

/*
 *---------------------------------------------------------------------------
 *
 * TclpSetInitialEncodings --
 *
 *	Based on the locale, determine the encoding of the operating system
 *	and the default encoding for newly opened files.
 *
 *	Called at process initialization time, and part way through startup,
 *	we verify that the initial encodings were correctly setup. Depending
 *	on Tcl's environment, there may not have been enough information first
 *	time through (above).
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	The Tcl library path is converted from native encoding to UTF-8, on
 *	the first call, and the encodings may be changed on first or second
 *	call.
 *
 *---------------------------------------------------------------------------
 */

void
TclpSetInitialEncodings(void)
{
    Tcl_DString encodingName;

    TclpSetInterfaces();
    Tcl_SetSystemEncoding(NULL,
	    Tcl_GetEncodingNameFromEnvironment(&encodingName));
    Tcl_DStringFree(&encodingName);
}

void
TclpSetInterfaces(void)
{
    int platformId, useWide;

    platformId = TclWinGetPlatformId();
    useWide = ((platformId == VER_PLATFORM_WIN32_NT)
	    || (platformId == VER_PLATFORM_WIN32_CE));
    TclWinSetInterfaces(useWide);
}

CONST char *
Tcl_GetEncodingNameFromEnvironment(
    Tcl_DString *bufPtr)
{
    Tcl_DStringInit(bufPtr);
    Tcl_DStringSetLength(bufPtr, 2+TCL_INTEGER_SPACE);
    wsprintfA(Tcl_DStringValue(bufPtr), "cp%d", GetACP());
    Tcl_DStringSetLength(bufPtr, strlen(Tcl_DStringValue(bufPtr)));
    return Tcl_DStringValue(bufPtr);
}

/*
 *---------------------------------------------------------------------------
 *
 * TclpSetVariables --
 *
 *	Performs platform-specific interpreter initialization related to the
 *	tcl_platform and env variables, and other platform-specific things.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	Sets "tcl_platform", and "env(HOME)" Tcl variables.
 *
 *----------------------------------------------------------------------
 */

void
TclpSetVariables(
    Tcl_Interp *interp)		/* Interp to initialize. */
{
    CONST char *ptr;
    char buffer[TCL_INTEGER_SPACE * 2];
    SYSTEM_INFO sysInfo, *sysInfoPtr = &sysInfo;
    OemId *oemId;
    OSVERSIONINFOA osInfo;
    Tcl_DString ds;
    TCHAR szUserName[UNLEN+1];
    DWORD dwUserNameLen = sizeof(szUserName);

    Tcl_SetVar2Ex(interp, "tclDefaultLibrary", NULL,
	    TclGetProcessGlobalValue(&defaultLibraryDir), TCL_GLOBAL_ONLY);

    osInfo.dwOSVersionInfoSize = sizeof(OSVERSIONINFOA);
    GetVersionExA(&osInfo);

    oemId = (OemId *) sysInfoPtr;
    GetSystemInfo(&sysInfo);

    /*
     * Define the tcl_platform array.
     */

    Tcl_SetVar2(interp, "tcl_platform", "platform", "windows",
	    TCL_GLOBAL_ONLY);
    if (osInfo.dwPlatformId < NUMPLATFORMS) {
	Tcl_SetVar2(interp, "tcl_platform", "os",
		platforms[osInfo.dwPlatformId], TCL_GLOBAL_ONLY);
    }
    wsprintfA(buffer, "%d.%d", osInfo.dwMajorVersion, osInfo.dwMinorVersion);
    Tcl_SetVar2(interp, "tcl_platform", "osVersion", buffer, TCL_GLOBAL_ONLY);
    if (oemId->wProcessorArchitecture < NUMPROCESSORS) {
	Tcl_SetVar2(interp, "tcl_platform", "machine",
		processors[oemId->wProcessorArchitecture],
		TCL_GLOBAL_ONLY);
    }

#ifdef _DEBUG
    /*
     * The existence of the "debug" element of the tcl_platform array
     * indicates that this particular Tcl shell has been compiled with debug
     * information. Using "info exists tcl_platform(debug)" a Tcl script can
     * direct the interpreter to load debug versions of DLLs with the load
     * command.
     */

    Tcl_SetVar2(interp, "tcl_platform", "debug", "1",
	    TCL_GLOBAL_ONLY);
#endif

    /*
     * Set up the HOME environment variable from the HOMEDRIVE & HOMEPATH
     * environment variables, if necessary.
     */

    Tcl_DStringInit(&ds);
    ptr = Tcl_GetVar2(interp, "env", "HOME", TCL_GLOBAL_ONLY);
    if (ptr == NULL) {
	ptr = Tcl_GetVar2(interp, "env", "HOMEDRIVE", TCL_GLOBAL_ONLY);
	if (ptr != NULL) {
	    Tcl_DStringAppend(&ds, ptr, -1);
	}
	ptr = Tcl_GetVar2(interp, "env", "HOMEPATH", TCL_GLOBAL_ONLY);
	if (ptr != NULL) {
	    Tcl_DStringAppend(&ds, ptr, -1);
	}
	if (Tcl_DStringLength(&ds) > 0) {
	    Tcl_SetVar2(interp, "env", "HOME", Tcl_DStringValue(&ds),
		    TCL_GLOBAL_ONLY);
	} else {
	    Tcl_SetVar2(interp, "env", "HOME", "c:\\", TCL_GLOBAL_ONLY);
	}
    }

    /*
     * Initialize the user name from the environment first, since this is much
     * faster than asking the system.
     */

    Tcl_DStringInit(&ds);
    if (TclGetEnv("USERNAME", &ds) == NULL) {
	if (GetUserName(szUserName, &dwUserNameLen) != 0) {
	    Tcl_WinTCharToUtf(szUserName, (int) dwUserNameLen, &ds);
	}
    }
    Tcl_SetVar2(interp, "tcl_platform", "user", Tcl_DStringValue(&ds),
	    TCL_GLOBAL_ONLY);
    Tcl_DStringFree(&ds);
}

/*
 *----------------------------------------------------------------------
 *
 * TclpFindVariable --
 *
 *	Locate the entry in environ for a given name. On Unix this routine is
 *	case sensitive, on Windows this matches mioxed case.
 *
 * Results:
 *	The return value is the index in environ of an entry with the name
 *	"name", or -1 if there is no such entry. The integer at *lengthPtr is
 *	filled in with the length of name (if a matching entry is found) or
 *	the length of the environ array (if no matching entry is found).
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */

int
TclpFindVariable(
    CONST char *name,		/* Name of desired environment variable
				 * (UTF-8). */
    int *lengthPtr)		/* Used to return length of name (for
				 * successful searches) or number of non-NULL
				 * entries in environ (for unsuccessful
				 * searches). */
{
    int i, length, result = -1;
    register CONST char *env, *p1, *p2;
    char *envUpper, *nameUpper;
    Tcl_DString envString;

    /*
     * Convert the name to all upper case for the case insensitive comparison.
     */

    length = strlen(name);
    nameUpper = (char *) ckalloc((unsigned) length+1);
    memcpy(nameUpper, name, (size_t) length+1);
    Tcl_UtfToUpper(nameUpper);

    Tcl_DStringInit(&envString);
    for (i = 0, env = environ[i]; env != NULL; i++, env = environ[i]) {
	/*
	 * Chop the env string off after the equal sign, then Convert the name
	 * to all upper case, so we do not have to convert all the characters
	 * after the equal sign.
	 */

	envUpper = Tcl_ExternalToUtfDString(NULL, env, -1, &envString);
	p1 = strchr(envUpper, '=');
	if (p1 == NULL) {
	    continue;
	}
	length = (int) (p1 - envUpper);
	Tcl_DStringSetLength(&envString, length+1);
	Tcl_UtfToUpper(envUpper);

	p1 = envUpper;
	p2 = nameUpper;
	for (; *p2 == *p1; p1++, p2++) {
	    /* NULL loop body. */
	}
	if ((*p1 == '=') && (*p2 == '\0')) {
	    *lengthPtr = length;
	    result = i;
	    goto done;
	}

	Tcl_DStringFree(&envString);
    }

    *lengthPtr = i;

  done:
    Tcl_DStringFree(&envString);
    ckfree(nameUpper);
    return result;
}

/*
 * Local Variables:
 * mode: c
 * c-basic-offset: 4
 * fill-column: 78
 * End:
 */
