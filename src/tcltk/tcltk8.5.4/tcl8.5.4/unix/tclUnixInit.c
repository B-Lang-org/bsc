/*
 * tclUnixInit.c --
 *
 *	Contains the Unix-specific interpreter initialization functions.
 *
 * Copyright (c) 1995-1997 Sun Microsystems, Inc.
 * Copyright (c) 1999 by Scriptics Corporation.
 * All rights reserved.
 *
 * RCS: @(#) $Id: tclUnixInit.c,v 1.82 2007/12/13 15:28:42 dgp Exp $
 */

#include "tclInt.h"
#include <stddef.h>
#include <locale.h>
#ifdef HAVE_LANGINFO
#   include <langinfo.h>
#   ifdef __APPLE__
#       if defined(HAVE_WEAK_IMPORT) && MAC_OS_X_VERSION_MIN_REQUIRED < 1030
	    /* Support for weakly importing nl_langinfo on Darwin. */
#           define WEAK_IMPORT_NL_LANGINFO
	    extern char *nl_langinfo(nl_item) WEAK_IMPORT_ATTRIBUTE;
#       endif
#    endif
#endif
#include <sys/resource.h>
#if defined(__FreeBSD__) && defined(__GNUC__)
#   include <floatingpoint.h>
#endif
#if defined(__bsdi__)
#   include <sys/param.h>
#   if _BSDI_VERSION > 199501
#	include <dlfcn.h>
#   endif
#endif
#ifdef HAVE_COREFOUNDATION
#include <CoreFoundation/CoreFoundation.h>
#endif

/*
 * Define TCL_NO_STACK_CHECK in the compiler options if you want to revert to
 * the old behavior of never checking the stack.
 */

/*
 * Define this if you want to see a lot of output regarding stack checking.
 */

#undef TCL_DEBUG_STACK_CHECK

/*
 * Values used to compute how much space is really available for Tcl's use for
 * the stack.
 *
 * The getrlimit() function is documented to return the maximum stack size in
 * bytes. However, with threads enabled, the pthread library on some platforms
 * does bad things to the stack size limits. First, the limits cannot be
 * changed. Second, they appear to be sometimes reported incorrectly.
 *
 * The defines below may need to be adjusted if more platforms have this
 * broken behavior with threads enabled.
 */

#ifndef TCL_MAGIC_STACK_DIVISOR
#define TCL_MAGIC_STACK_DIVISOR		1
#endif
#ifndef TCL_RESERVED_STACK_PAGES
#define TCL_RESERVED_STACK_PAGES	8
#endif

/*
 * Thread specific data for stack checking.
 */

#ifndef TCL_NO_STACK_CHECK
typedef struct ThreadSpecificData {
    int *outerVarPtr;		/* The "outermost" stack frame pointer for
				 * this thread. */
    int *stackBound;            /* The current stack boundary */
} ThreadSpecificData;
static Tcl_ThreadDataKey dataKey;
#ifdef TCL_CROSS_COMPILE
static int stackGrowsDown = -1;
static int StackGrowsDown(int *parent);
#elif defined(TCL_STACK_GROWS_UP)
#define stackGrowsDown 0
#else
#define stackGrowsDown 1
#endif
#endif /* TCL_NO_STACK_CHECK */

#ifdef TCL_DEBUG_STACK_CHECK
#define STACK_DEBUG(args) printf args
#else
#define STACK_DEBUG(args) (void)0
#endif /* TCL_DEBUG_STACK_CHECK */

/*
 * Tcl tries to use standard and homebrew methods to guess the right encoding
 * on the platform. However, there is always a final fallback, and this value
 * is it. Make sure it is a real Tcl encoding.
 */

#ifndef TCL_DEFAULT_ENCODING
#define TCL_DEFAULT_ENCODING "iso8859-1"
#endif

/*
 * Default directory in which to look for Tcl library scripts. The symbol is
 * defined by Makefile.
 */

static char defaultLibraryDir[sizeof(TCL_LIBRARY)+200] = TCL_LIBRARY;

/*
 * Directory in which to look for packages (each package is typically
 * installed as a subdirectory of this directory). The symbol is defined by
 * Makefile.
 */

static char pkgPath[sizeof(TCL_PACKAGE_PATH)+200] = TCL_PACKAGE_PATH;

/*
 * The following table is used to map from Unix locale strings to encoding
 * files. If HAVE_LANGINFO is defined, then this is a fallback table when the
 * result from nl_langinfo isn't a recognized encoding. Otherwise this is the
 * first list checked for a mapping from env encoding to Tcl encoding name.
 */

typedef struct LocaleTable {
    CONST char *lang;
    CONST char *encoding;
} LocaleTable;

/*
 * The table below is sorted for the sake of doing binary searches on it. The
 * indenting reflects different categories of data. The leftmost data
 * represent the encoding names directly implemented by data files in Tcl's
 * default encoding directory. Indented by one TAB are the encoding names that
 * are common alternative spellings. Indented by two TABs are the accumulated
 * "bug fixes" that have been added to deal with the wide variability seen
 * among existing platforms.
 */

static CONST LocaleTable localeTable[] = {
	    {"",		"iso8859-1"},
		    {"ansi-1251",	"cp1251"},
	    {"ansi_x3.4-1968",	"iso8859-1"},
    {"ascii",		"ascii"},
    {"big5",		"big5"},
    {"cp1250",		"cp1250"},
    {"cp1251",		"cp1251"},
    {"cp1252",		"cp1252"},
    {"cp1253",		"cp1253"},
    {"cp1254",		"cp1254"},
    {"cp1255",		"cp1255"},
    {"cp1256",		"cp1256"},
    {"cp1257",		"cp1257"},
    {"cp1258",		"cp1258"},
    {"cp437",		"cp437"},
    {"cp737",		"cp737"},
    {"cp775",		"cp775"},
    {"cp850",		"cp850"},
    {"cp852",		"cp852"},
    {"cp855",		"cp855"},
    {"cp857",		"cp857"},
    {"cp860",		"cp860"},
    {"cp861",		"cp861"},
    {"cp862",		"cp862"},
    {"cp863",		"cp863"},
    {"cp864",		"cp864"},
    {"cp865",		"cp865"},
    {"cp866",		"cp866"},
    {"cp869",		"cp869"},
    {"cp874",		"cp874"},
    {"cp932",		"cp932"},
    {"cp936",		"cp936"},
    {"cp949",		"cp949"},
    {"cp950",		"cp950"},
    {"dingbats",	"dingbats"},
    {"ebcdic",		"ebcdic"},
    {"euc-cn",		"euc-cn"},
    {"euc-jp",		"euc-jp"},
    {"euc-kr",		"euc-kr"},
		    {"eucjp",		"euc-jp"},
		    {"euckr",		"euc-kr"},
		    {"euctw",		"euc-cn"},
    {"gb12345",		"gb12345"},
    {"gb1988",		"gb1988"},
    {"gb2312",		"gb2312"},
		    {"gb2312-1980",	"gb2312"},
    {"gb2312-raw",	"gb2312-raw"},
		    {"greek8",		"cp869"},
	    {"ibm1250",		"cp1250"},
	    {"ibm1251",		"cp1251"},
	    {"ibm1252",		"cp1252"},
	    {"ibm1253",		"cp1253"},
	    {"ibm1254",		"cp1254"},
	    {"ibm1255",		"cp1255"},
	    {"ibm1256",		"cp1256"},
	    {"ibm1257",		"cp1257"},
	    {"ibm1258",		"cp1258"},
	    {"ibm437",		"cp437"},
	    {"ibm737",		"cp737"},
	    {"ibm775",		"cp775"},
	    {"ibm850",		"cp850"},
	    {"ibm852",		"cp852"},
	    {"ibm855",		"cp855"},
	    {"ibm857",		"cp857"},
	    {"ibm860",		"cp860"},
	    {"ibm861",		"cp861"},
	    {"ibm862",		"cp862"},
	    {"ibm863",		"cp863"},
	    {"ibm864",		"cp864"},
	    {"ibm865",		"cp865"},
	    {"ibm866",		"cp866"},
	    {"ibm869",		"cp869"},
	    {"ibm874",		"cp874"},
	    {"ibm932",		"cp932"},
	    {"ibm936",		"cp936"},
	    {"ibm949",		"cp949"},
	    {"ibm950",		"cp950"},
	    {"iso-2022",	"iso2022"},
	    {"iso-2022-jp",	"iso2022-jp"},
	    {"iso-2022-kr",	"iso2022-kr"},
	    {"iso-8859-1",	"iso8859-1"},
	    {"iso-8859-10",	"iso8859-10"},
	    {"iso-8859-13",	"iso8859-13"},
	    {"iso-8859-14",	"iso8859-14"},
	    {"iso-8859-15",	"iso8859-15"},
	    {"iso-8859-16",	"iso8859-16"},
	    {"iso-8859-2",	"iso8859-2"},
	    {"iso-8859-3",	"iso8859-3"},
	    {"iso-8859-4",	"iso8859-4"},
	    {"iso-8859-5",	"iso8859-5"},
	    {"iso-8859-6",	"iso8859-6"},
	    {"iso-8859-7",	"iso8859-7"},
	    {"iso-8859-8",	"iso8859-8"},
	    {"iso-8859-9",	"iso8859-9"},
    {"iso2022",		"iso2022"},
    {"iso2022-jp",	"iso2022-jp"},
    {"iso2022-kr",	"iso2022-kr"},
    {"iso8859-1",	"iso8859-1"},
    {"iso8859-10",	"iso8859-10"},
    {"iso8859-13",	"iso8859-13"},
    {"iso8859-14",	"iso8859-14"},
    {"iso8859-15",	"iso8859-15"},
    {"iso8859-16",	"iso8859-16"},
    {"iso8859-2",	"iso8859-2"},
    {"iso8859-3",	"iso8859-3"},
    {"iso8859-4",	"iso8859-4"},
    {"iso8859-5",	"iso8859-5"},
    {"iso8859-6",	"iso8859-6"},
    {"iso8859-7",	"iso8859-7"},
    {"iso8859-8",	"iso8859-8"},
    {"iso8859-9",	"iso8859-9"},
		    {"iso88591",	"iso8859-1"},
		    {"iso885915",	"iso8859-15"},
		    {"iso88592",	"iso8859-2"},
		    {"iso88595",	"iso8859-5"},
		    {"iso88596",	"iso8859-6"},
		    {"iso88597",	"iso8859-7"},
		    {"iso88598",	"iso8859-8"},
		    {"iso88599",	"iso8859-9"},
#ifdef hpux
		    {"ja",		"shiftjis"},
#else
		    {"ja",		"euc-jp"},
#endif
		    {"ja_jp",		"euc-jp"},
		    {"ja_jp.euc",	"euc-jp"},
		    {"ja_jp.eucjp",	"euc-jp"},
		    {"ja_jp.jis",	"iso2022-jp"},
		    {"ja_jp.mscode",	"shiftjis"},
		    {"ja_jp.sjis",	"shiftjis"},
		    {"ja_jp.ujis",	"euc-jp"},
		    {"japan",		"euc-jp"},
#ifdef hpux
		    {"japanese",	"shiftjis"},
#else
		    {"japanese",	"euc-jp"},
#endif
		    {"japanese-sjis",	"shiftjis"},
		    {"japanese-ujis",	"euc-jp"},
		    {"japanese.euc",	"euc-jp"},
		    {"japanese.sjis",	"shiftjis"},
    {"jis0201",		"jis0201"},
    {"jis0208",		"jis0208"},
    {"jis0212",		"jis0212"},
		    {"jp_jp",		"shiftjis"},
		    {"ko",		"euc-kr"},
		    {"ko_kr",		"euc-kr"},
		    {"ko_kr.euc",	"euc-kr"},
		    {"ko_kw.euckw",	"euc-kr"},
    {"koi8-r",		"koi8-r"},
    {"koi8-u",		"koi8-u"},
		    {"korean",		"euc-kr"},
    {"ksc5601",		"ksc5601"},
    {"maccenteuro",	"macCentEuro"},
    {"maccroatian",	"macCroatian"},
    {"maccyrillic",	"macCyrillic"},
    {"macdingbats",	"macDingbats"},
    {"macgreek",	"macGreek"},
    {"maciceland",	"macIceland"},
    {"macjapan",	"macJapan"},
    {"macroman",	"macRoman"},
    {"macromania",	"macRomania"},
    {"macthai",		"macThai"},
    {"macturkish",	"macTurkish"},
    {"macukraine",	"macUkraine"},
		    {"roman8",		"iso8859-1"},
		    {"ru",		"iso8859-5"},
		    {"ru_ru",		"iso8859-5"},
		    {"ru_su",		"iso8859-5"},
    {"shiftjis",	"shiftjis"},
		    {"sjis",		"shiftjis"},
    {"symbol",		"symbol"},
    {"tis-620",		"tis-620"},
		    {"tis620",		"tis-620"},
		    {"turkish8",	"cp857"},
		    {"utf8",		"utf-8"},
		    {"zh",		"cp936"},
		    {"zh_cn.gb2312",	"euc-cn"},
		    {"zh_cn.gbk",	"euc-cn"},
		    {"zh_cz.gb2312",	"euc-cn"},
		    {"zh_tw",		"euc-tw"},
		    {"zh_tw.big5",	"big5"},
};

#ifndef TCL_NO_STACK_CHECK
static int		GetStackSize(size_t *stackSizePtr);
#endif /* TCL_NO_STACK_CHECK */
#ifdef HAVE_COREFOUNDATION
static int		MacOSXGetLibraryPath(Tcl_Interp *interp,
			    int maxPathLen, char *tclLibPath);
#endif /* HAVE_COREFOUNDATION */
#if defined(__APPLE__) && (defined(TCL_LOAD_FROM_MEMORY) || ( \
	defined(TCL_THREADS) && defined(MAC_OS_X_VERSION_MIN_REQUIRED) && \
	MAC_OS_X_VERSION_MIN_REQUIRED < 1030) || ( \
	defined(__LP64__) && defined(MAC_OS_X_VERSION_MIN_REQUIRED) && \
	MAC_OS_X_VERSION_MIN_REQUIRED < 1050))
/*
 * Need to check Darwin release at runtime in tclUnixFCmd.c and tclLoadDyld.c:
 * initialize release global at startup from uname().
 */
#define GET_DARWIN_RELEASE 1
MODULE_SCOPE long tclMacOSXDarwinRelease;
long tclMacOSXDarwinRelease = 0;
#endif


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
#ifdef DJGPP
    tclPlatform = TCL_PLATFORM_WINDOWS;
#else
    tclPlatform = TCL_PLATFORM_UNIX;
#endif

    /*
     * Make sure, that the standard FDs exist. [Bug 772288]
     */

    if (TclOSseek(0, (Tcl_SeekOffset) 0, SEEK_CUR) == -1 && errno == EBADF) {
	open("/dev/null", O_RDONLY);
    }
    if (TclOSseek(1, (Tcl_SeekOffset) 0, SEEK_CUR) == -1 && errno == EBADF) {
	open("/dev/null", O_WRONLY);
    }
    if (TclOSseek(2, (Tcl_SeekOffset) 0, SEEK_CUR) == -1 && errno == EBADF) {
	open("/dev/null", O_WRONLY);
    }

    /*
     * The code below causes SIGPIPE (broken pipe) errors to be ignored. This
     * is needed so that Tcl processes don't die if they create child
     * processes (e.g. using "exec" or "open") that terminate prematurely.
     * The signal handler is only set up when the first interpreter is
     * created; after this the application can override the handler with a
     * different one of its own, if it wants.
     */

#ifdef SIGPIPE
    (void) signal(SIGPIPE, SIG_IGN);
#endif /* SIGPIPE */

#if defined(__FreeBSD__) && defined(__GNUC__)
    /*
     * Adjust the rounding mode to be more conventional. Note that FreeBSD
     * only provides the __fpsetreg() used by the following two for the GNU
     * Compiler. When using, say, Intel's icc they break. (Partially based on
     * patch in BSD ports system from root@celsius.bychok.com)
     */

    fpsetround(FP_RN);
    (void) fpsetmask(0L);
#endif

#if defined(__bsdi__) && (_BSDI_VERSION > 199501)
    /*
     * Find local symbols. Don't report an error if we fail.
     */

    (void) dlopen(NULL, RTLD_NOW);			/* INTL: Native. */
#endif

    /*
     * Initialize the C library's locale subsystem. This is required for input
     * methods to work properly on X11. We only do this for LC_CTYPE because
     * that's the necessary one, and we don't want to affect LC_TIME here.
     * The side effect of setting the default locale should be to load any
     * locale specific modules that are needed by X. [BUG: 5422 3345 4236 2522
     * 2521].
     */

    setlocale(LC_CTYPE, "");

    /*
     * In case the initial locale is not "C", ensure that the numeric
     * processing is done in "C" locale regardless. This is needed because Tcl
     * relies on routines like strtod, but should not have locale dependent
     * behavior.
     */

    setlocale(LC_NUMERIC, "C");

#ifdef GET_DARWIN_RELEASE
    {
	struct utsname name;

	if (!uname(&name)) {
	    tclMacOSXDarwinRelease = strtol(name.release, NULL, 10);
	}
    }
#endif
}

/*
 *---------------------------------------------------------------------------
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
    Tcl_Obj *pathPtr, *objPtr;
    CONST char *str;
    Tcl_DString buffer;

    pathPtr = Tcl_NewObj();

    /*
     * Look for the library relative to the TCL_LIBRARY env variable. If the
     * last dirname in the TCL_LIBRARY path does not match the last dirname in
     * the installLib variable, use the last dir name of installLib in
     * addition to the orginal TCL_LIBRARY path.
     */

    str = getenv("TCL_LIBRARY");			/* INTL: Native. */
    Tcl_ExternalToUtfDString(NULL, str, -1, &buffer);
    str = Tcl_DStringValue(&buffer);

    if ((str != NULL) && (str[0] != '\0')) {
	Tcl_DString ds;
	int pathc;
	CONST char **pathv;
	char installLib[LIBRARY_SIZE];

	Tcl_DStringInit(&ds);

	/*
	 * Initialize the substrings used when locating an executable. The
	 * installLib variable computes the path as though the executable is
	 * installed.
	 */

	sprintf(installLib, "lib/tcl%s", TCL_VERSION);

	/*
	 * If TCL_LIBRARY is set, search there.
	 */

	objPtr = Tcl_NewStringObj(str, -1);
	Tcl_ListObjAppendElement(NULL, pathPtr, objPtr);

	Tcl_SplitPath(str, &pathc, &pathv);
	if ((pathc > 0) && (strcasecmp(installLib + 4, pathv[pathc-1]) != 0)) {
	    /*
	     * If TCL_LIBRARY is set but refers to a different tcl
	     * installation than the current version, try fiddling with the
	     * specified directory to make it refer to this installation by
	     * removing the old "tclX.Y" and substituting the current version
	     * string.
	     */

	    pathv[pathc - 1] = installLib + 4;
	    str = Tcl_JoinPath(pathc, pathv, &ds);
	    objPtr = Tcl_NewStringObj(str, Tcl_DStringLength(&ds));
	    Tcl_ListObjAppendElement(NULL, pathPtr, objPtr);
	    Tcl_DStringFree(&ds);
	}
	ckfree((char *) pathv);
    }

    /*
     * Finally, look for the library relative to the compiled-in path. This is
     * needed when users install Tcl with an exec-prefix that is different
     * from the prefix.
     */

    {
#ifdef HAVE_COREFOUNDATION
	char tclLibPath[MAXPATHLEN + 1];

	if (MacOSXGetLibraryPath(NULL, MAXPATHLEN, tclLibPath) == TCL_OK) {
	    str = tclLibPath;
	} else
#endif /* HAVE_COREFOUNDATION */
	{
	    /*
	     * TODO: Pull this value from the TIP 59 table.
	     */

	    str = defaultLibraryDir;
	}
	if (str[0] != '\0') {
	    objPtr = Tcl_NewStringObj(str, -1);
	    Tcl_ListObjAppendElement(NULL, pathPtr, objPtr);
	}
    }
    Tcl_DStringFree(&buffer);

    *encodingPtr = Tcl_GetEncoding(NULL, NULL);
    str = Tcl_GetStringFromObj(pathPtr, lengthPtr);
    *valuePtr = ckalloc((unsigned int) (*lengthPtr)+1);
    memcpy(*valuePtr, str, (size_t)(*lengthPtr)+1);
    Tcl_DecrRefCount(pathPtr);
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
    Tcl_SetSystemEncoding(NULL,
	    Tcl_GetEncodingNameFromEnvironment(&encodingName));
    Tcl_DStringFree(&encodingName);
}

void
TclpSetInterfaces(void)
{
    /* do nothing */
}

static CONST char *
SearchKnownEncodings(
    CONST char *encoding)
{
    int left = 0;
    int right = sizeof(localeTable)/sizeof(LocaleTable);

    while (left <= right) {
	int test = (left + right)/2;
	int code = strcmp(localeTable[test].lang, encoding);

	if (code == 0) {
	    return localeTable[test].encoding;
	}
	if (code < 0) {
	    left = test+1;
	} else {
	    right = test-1;
	}
    }
    return NULL;
}

CONST char *
Tcl_GetEncodingNameFromEnvironment(
    Tcl_DString *bufPtr)
{
    CONST char *encoding;
    CONST char *knownEncoding;

    Tcl_DStringInit(bufPtr);

    /*
     * Determine the current encoding from the LC_* or LANG environment
     * variables. We previously used setlocale() to determine the locale, but
     * this does not work on some systems (e.g. Linux/i386 RH 5.0).
     */

#ifdef HAVE_LANGINFO
    if (
#ifdef WEAK_IMPORT_NL_LANGINFO
	    nl_langinfo != NULL &&
#endif
	    setlocale(LC_CTYPE, "") != NULL) {
	Tcl_DString ds;

	/*
	 * Use a DString so we can modify case.
	 */

	Tcl_DStringInit(&ds);
	encoding = Tcl_DStringAppend(&ds, nl_langinfo(CODESET), -1);
	Tcl_UtfToLower(Tcl_DStringValue(&ds));
	knownEncoding = SearchKnownEncodings(encoding);
	if (knownEncoding != NULL) {
	    Tcl_DStringAppend(bufPtr, knownEncoding, -1);
	} else if (NULL != Tcl_GetEncoding(NULL, encoding)) {
	    Tcl_DStringAppend(bufPtr, encoding, -1);
	}
	Tcl_DStringFree(&ds);
	if (Tcl_DStringLength(bufPtr)) {
	    return Tcl_DStringValue(bufPtr);
	}
    }
#endif /* HAVE_LANGINFO */

    /*
     * Classic fallback check. This tries a homebrew algorithm to determine
     * what encoding should be used based on env vars.
     */

    encoding = getenv("LC_ALL");

    if (encoding == NULL || encoding[0] == '\0') {
	encoding = getenv("LC_CTYPE");
    }
    if (encoding == NULL || encoding[0] == '\0') {
	encoding = getenv("LANG");
    }
    if (encoding == NULL || encoding[0] == '\0') {
	encoding = NULL;
    }

    if (encoding != NULL) {
	CONST char *p;
	Tcl_DString ds;

	Tcl_DStringInit(&ds);
	p = encoding;
	encoding = Tcl_DStringAppend(&ds, p, -1);
	Tcl_UtfToLower(Tcl_DStringValue(&ds));

	knownEncoding = SearchKnownEncodings(encoding);
	if (knownEncoding != NULL) {
	    Tcl_DStringAppend(bufPtr, knownEncoding, -1);
	} else if (NULL != Tcl_GetEncoding(NULL, encoding)) {
	    Tcl_DStringAppend(bufPtr, encoding, -1);
	}
	if (Tcl_DStringLength(bufPtr)) {
	    Tcl_DStringFree(&ds);
	    return Tcl_DStringValue(bufPtr);
	}

	/*
	 * We didn't recognize the full value as an encoding name. If there is
	 * an encoding subfield, we can try to guess from that.
	 */

	for (p = encoding; *p != '\0'; p++) {
	    if (*p == '.') {
		p++;
		break;
	    }
	}
	if (*p != '\0') {
	    knownEncoding = SearchKnownEncodings(p);
	    if (knownEncoding != NULL) {
		Tcl_DStringAppend(bufPtr, knownEncoding, -1);
	    } else if (NULL != Tcl_GetEncoding(NULL, p)) {
		Tcl_DStringAppend(bufPtr, p, -1);
	    }
	}
	Tcl_DStringFree(&ds);
	if (Tcl_DStringLength(bufPtr)) {
	    return Tcl_DStringValue(bufPtr);
	}
    }
    return Tcl_DStringAppend(bufPtr, TCL_DEFAULT_ENCODING, -1);
}

/*
 *---------------------------------------------------------------------------
 *
 * TclpSetVariables --
 *
 *	Performs platform-specific interpreter initialization related to the
 *	tcl_library and tcl_platform variables, and other platform-specific
 *	things.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	Sets "tclDefaultLibrary", "tcl_pkgPath", and "tcl_platform" Tcl
 *	variables.
 *
 *----------------------------------------------------------------------
 */

void
TclpSetVariables(
    Tcl_Interp *interp)
{
#ifndef NO_UNAME
    struct utsname name;
#endif
    int unameOK;
    Tcl_DString ds;

#ifdef HAVE_COREFOUNDATION
    char tclLibPath[MAXPATHLEN + 1];

#if MAC_OS_X_VERSION_MAX_ALLOWED > 1020
    /*
     * Set msgcat fallback locale to current CFLocale identifier.
     */

    CFLocaleRef localeRef;
    
    if (CFLocaleCopyCurrent != NULL && CFLocaleGetIdentifier != NULL &&
	    (localeRef = CFLocaleCopyCurrent())) {
	CFStringRef locale = CFLocaleGetIdentifier(localeRef);

	if (locale) {
	    char loc[256];

	    if (CFStringGetCString(locale, loc, 256, kCFStringEncodingUTF8)) {
		if (!Tcl_CreateNamespace(interp, "::tcl::mac", NULL, NULL)) {
		    Tcl_ResetResult(interp);
		}
		Tcl_SetVar(interp, "::tcl::mac::locale", loc, TCL_GLOBAL_ONLY);
	    }
	}
	CFRelease(localeRef);
    }
#endif /* MAC_OS_X_VERSION_MAX_ALLOWED > 1020 */

    if (MacOSXGetLibraryPath(interp, MAXPATHLEN, tclLibPath) == TCL_OK) {
	CONST char *str;
	CFBundleRef bundleRef;

	Tcl_SetVar(interp, "tclDefaultLibrary", tclLibPath, TCL_GLOBAL_ONLY);
	Tcl_SetVar(interp, "tcl_pkgPath", tclLibPath, TCL_GLOBAL_ONLY);
	Tcl_SetVar(interp, "tcl_pkgPath", " ",
		TCL_GLOBAL_ONLY | TCL_APPEND_VALUE);

	str = TclGetEnv("DYLD_FRAMEWORK_PATH", &ds);
	if ((str != NULL) && (str[0] != '\0')) {
	    char *p = Tcl_DStringValue(&ds);

	    /*
	     * Convert DYLD_FRAMEWORK_PATH from colon to space separated.
	     */

	    do {
		if (*p == ':') {
		    *p = ' ';
		}
	    } while (*p++);
	    Tcl_SetVar(interp, "tcl_pkgPath", Tcl_DStringValue(&ds),
		    TCL_GLOBAL_ONLY | TCL_APPEND_VALUE);
	    Tcl_SetVar(interp, "tcl_pkgPath", " ",
		    TCL_GLOBAL_ONLY | TCL_APPEND_VALUE);
	    Tcl_DStringFree(&ds);
	}
	bundleRef = CFBundleGetMainBundle();
	if (bundleRef) {
	    CFURLRef frameworksURL;
	    Tcl_StatBuf statBuf;

	    frameworksURL = CFBundleCopyPrivateFrameworksURL(bundleRef);
	    if (frameworksURL) {
		if (CFURLGetFileSystemRepresentation(frameworksURL, TRUE,
			(unsigned char*) tclLibPath, MAXPATHLEN) &&
			! TclOSstat(tclLibPath, &statBuf) &&
			S_ISDIR(statBuf.st_mode)) {
		    Tcl_SetVar(interp, "tcl_pkgPath", tclLibPath,
			    TCL_GLOBAL_ONLY | TCL_APPEND_VALUE);
		    Tcl_SetVar(interp, "tcl_pkgPath", " ",
			    TCL_GLOBAL_ONLY | TCL_APPEND_VALUE);
		}
		CFRelease(frameworksURL);
	    }
	    frameworksURL = CFBundleCopySharedFrameworksURL(bundleRef);
	    if (frameworksURL) {
		if (CFURLGetFileSystemRepresentation(frameworksURL, TRUE,
			(unsigned char*) tclLibPath, MAXPATHLEN) &&
			! TclOSstat(tclLibPath, &statBuf) &&
			S_ISDIR(statBuf.st_mode)) {
		    Tcl_SetVar(interp, "tcl_pkgPath", tclLibPath,
			    TCL_GLOBAL_ONLY | TCL_APPEND_VALUE);
		    Tcl_SetVar(interp, "tcl_pkgPath", " ",
			    TCL_GLOBAL_ONLY | TCL_APPEND_VALUE);
		}
		CFRelease(frameworksURL);
	    }
	}
	Tcl_SetVar(interp, "tcl_pkgPath", pkgPath,
		TCL_GLOBAL_ONLY | TCL_APPEND_VALUE);
    } else
#endif /* HAVE_COREFOUNDATION */
    {
	Tcl_SetVar(interp, "tcl_pkgPath", pkgPath, TCL_GLOBAL_ONLY);
    }

#ifdef DJGPP
    Tcl_SetVar2(interp, "tcl_platform", "platform", "dos", TCL_GLOBAL_ONLY);
#else
    Tcl_SetVar2(interp, "tcl_platform", "platform", "unix", TCL_GLOBAL_ONLY);
#endif

    unameOK = 0;
#ifndef NO_UNAME
    if (uname(&name) >= 0) {
	CONST char *native;

	unameOK = 1;

	native = Tcl_ExternalToUtfDString(NULL, name.sysname, -1, &ds);
	Tcl_SetVar2(interp, "tcl_platform", "os", native, TCL_GLOBAL_ONLY);
	Tcl_DStringFree(&ds);

	/*
	 * The following code is a special hack to handle differences in the
	 * way version information is returned by uname. On most systems the
	 * full version number is available in name.release. However, under
	 * AIX the major version number is in name.version and the minor
	 * version number is in name.release.
	 */

	if ((strchr(name.release, '.') != NULL)
		|| !isdigit(UCHAR(name.version[0]))) {	/* INTL: digit */
	    Tcl_SetVar2(interp, "tcl_platform", "osVersion", name.release,
		    TCL_GLOBAL_ONLY);
	} else {
#ifdef DJGPP
	    /*
	     * For some obscure reason DJGPP puts major version into
	     * name.release and minor into name.version. As of DJGPP 2.04 this
	     * is documented in djgpp libc.info file.
	     */

	    Tcl_SetVar2(interp, "tcl_platform", "osVersion", name.release,
		    TCL_GLOBAL_ONLY);
	    Tcl_SetVar2(interp, "tcl_platform", "osVersion", ".",
		    TCL_GLOBAL_ONLY|TCL_APPEND_VALUE);
	    Tcl_SetVar2(interp, "tcl_platform", "osVersion", name.version,
		    TCL_GLOBAL_ONLY|TCL_APPEND_VALUE);
#else
	    Tcl_SetVar2(interp, "tcl_platform", "osVersion", name.version,
		    TCL_GLOBAL_ONLY);
	    Tcl_SetVar2(interp, "tcl_platform", "osVersion", ".",
		    TCL_GLOBAL_ONLY|TCL_APPEND_VALUE);
	    Tcl_SetVar2(interp, "tcl_platform", "osVersion", name.release,
		    TCL_GLOBAL_ONLY|TCL_APPEND_VALUE);

#endif /* DJGPP */
	}
	Tcl_SetVar2(interp, "tcl_platform", "machine", name.machine,
		TCL_GLOBAL_ONLY);
    }
#endif /* !NO_UNAME */
    if (!unameOK) {
	Tcl_SetVar2(interp, "tcl_platform", "os", "", TCL_GLOBAL_ONLY);
	Tcl_SetVar2(interp, "tcl_platform", "osVersion", "", TCL_GLOBAL_ONLY);
	Tcl_SetVar2(interp, "tcl_platform", "machine", "", TCL_GLOBAL_ONLY);
    }

    /*
     * Copy the username of the real user (according to getuid()) into
     * tcl_platform(user).
     */

    {
	struct passwd *pwEnt = TclpGetPwUid(getuid());
	const char *user;

	if (pwEnt == NULL) {
	    user = "";
	    Tcl_DStringInit(&ds);	/* ensure cleanliness */
	} else {
	    user = Tcl_ExternalToUtfDString(NULL, pwEnt->pw_name, -1, &ds);
	}

	Tcl_SetVar2(interp, "tcl_platform", "user", user, TCL_GLOBAL_ONLY);
	Tcl_DStringFree(&ds);
    }
}

/*
 *----------------------------------------------------------------------
 *
 * TclpFindVariable --
 *
 *	Locate the entry in environ for a given name. On Unix this routine is
 *	case sensetive, on Windows this matches mixed case.
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
				 * (native). */
    int *lengthPtr)		/* Used to return length of name (for
				 * successful searches) or number of non-NULL
				 * entries in environ (for unsuccessful
				 * searches). */
{
    int i, result = -1;
    register CONST char *env, *p1, *p2;
    Tcl_DString envString;

    Tcl_DStringInit(&envString);
    for (i = 0, env = environ[i]; env != NULL; i++, env = environ[i]) {
	p1 = Tcl_ExternalToUtfDString(NULL, env, -1, &envString);
	p2 = name;

	for (; *p2 == *p1; p1++, p2++) {
	    /* NULL loop body. */
	}
	if ((*p1 == '=') && (*p2 == '\0')) {
	    *lengthPtr = p2 - name;
	    result = i;
	    goto done;
	}

	Tcl_DStringFree(&envString);
    }

    *lengthPtr = i;

  done:
    Tcl_DStringFree(&envString);
    return result;
}

#ifndef TCL_NO_STACK_CHECK
/*
 *----------------------------------------------------------------------
 *
 * TclpGetCStackParams --
 *
 *	Determine the stack params for the current thread: in which
 *	direction does the stack grow, and what is the stack lower (resp.
 *	upper) bound for safe invocation of a new command? This is used to
 *	cache the values needed for an efficient computation of
 *	TclpCheckStackSpace() when the interp is known.
 *
 * Results:
 *	Returns 1 if the stack grows down, in which case a stack lower bound
 *	is stored at stackBoundPtr. If the stack grows up, 0 is returned and
 *	an upper bound is stored at stackBoundPtr. If a bound cannot be
 *	determined NULL is stored at stackBoundPtr.
 *
 *----------------------------------------------------------------------
 */

int
TclpGetCStackParams(
    int **stackBoundPtr)
{
    int result = TCL_OK;
    size_t stackSize = 0;	/* The size of the current stack. */
    ThreadSpecificData *tsdPtr = TCL_TSD_INIT(&dataKey);
				/* Most variables are actually in a
				 * thread-specific data block to minimise the
				 * impact on the stack. */
#ifdef TCL_CROSS_COMPILE
    if (stackGrowsDown == -1) {
	/*
	 * Not initialised!
	 */

	stackGrowsDown = StackGrowsDown(&result);
    }
#endif
    
    /*
     * The first time through in a thread: record the "outermost" stack
     * frame and inquire with the OS about the stack size.
     */

    if (tsdPtr->outerVarPtr == NULL) {
	tsdPtr->outerVarPtr = &result;
	result = GetStackSize(&stackSize);
	if (result != TCL_OK) {
	    /* Can't check, assume it always succeeds */
#ifdef TCL_CROSS_COMPILE
	    stackGrowsDown = 1;
#endif
	    tsdPtr->stackBound = NULL;
	    goto done;
	}
    }

    if (stackSize || (tsdPtr->stackBound &&
	    ((stackGrowsDown && (&result < tsdPtr->stackBound)) ||
	    (!stackGrowsDown && (&result > tsdPtr->stackBound))))) {
	/*
	 * Either the thread's first pass or stack failure: set the params
	 */

	if (!stackSize) {
	    /*
	     * Stack failure: if we didn't already blow up, we are within the
	     * safety area. Recheck with the OS in case the stack was grown. 
	     */
	    result = GetStackSize(&stackSize);
	    if (result != TCL_OK) {
		/* Can't check, assume it always succeeds */
#ifdef TCL_CROSS_COMPILE
		stackGrowsDown = 1;
#endif
		tsdPtr->stackBound = NULL;
		goto done;
	    }
	}

	if (stackGrowsDown) {
	    tsdPtr->stackBound = (int *) ((char *)tsdPtr->outerVarPtr -
		    stackSize);
	} else {
	    tsdPtr->stackBound = (int *) ((char *)tsdPtr->outerVarPtr +
		    stackSize);
	}
    }

    done:
    *stackBoundPtr = tsdPtr->stackBound;
    return stackGrowsDown;
}

#ifdef TCL_CROSS_COMPILE
int
StackGrowsDown(
    int *parent)
{
    int here;
    return (&here < parent);
}
#endif

/*
 *----------------------------------------------------------------------
 *
 * GetStackSize --
 *
 *	Discover what the stack size for the current thread/process actually
 *	is. Expects to only ever be called once per thread and then only at a
 *	point when there is a reasonable amount of space left on the current
 *	stack; TclpCheckStackSpace is called sufficiently frequently that that
 *	is true.
 *
 * Results:
 *	TCL_OK if the stack space was discovered, TCL_BREAK if the stack space
 *	was undiscoverable in a way that stack checks should fail, and
 *	TCL_CONTINUE if the stack space was undiscoverable in a way that stack
 *	checks should succeed.
 *
 * Side effects:
 *	None
 *
 *----------------------------------------------------------------------
 */

static int
GetStackSize(
    size_t *stackSizePtr)
{
    size_t rawStackSize;
    struct rlimit rLimit;	/* The result from getrlimit(). */

#ifdef TCL_THREADS
    rawStackSize = TclpThreadGetStackSize();
    if (rawStackSize == (size_t) -1) {
	/*
	 * Some kind of confirmed error in TclpThreadGetStackSize?! Fall back
	 * to whatever getrlimit can determine.
	 */
	STACK_DEBUG(("stack checks: TclpThreadGetStackSize failed in \n"));
    }
    if (rawStackSize > 0) {
	goto finalSanityCheck;
    }

    /*
     * If we have zero or an error, try the system limits instead. After all,
     * the pthread documentation states that threads should always be bound by
     * the system stack size limit in any case.
     */
#endif /* TCL_THREADS */

    if (getrlimit(RLIMIT_STACK, &rLimit) != 0) {
	/*
	 * getrlimit() failed, just fail the whole thing.
	 */
	STACK_DEBUG(("skipping stack checks with failure: getrlimit failed\n"));
	return TCL_BREAK;
    }
    if (rLimit.rlim_cur == RLIM_INFINITY) {
	/*
	 * Limit is "infinite"; there is no stack limit.
	 */
	STACK_DEBUG(("skipping stack checks with success: infinite limit\n"));
	return TCL_CONTINUE;
    }
    rawStackSize = rLimit.rlim_cur;

    /*
     * Final sanity check on the determined stack size. If we fail this,
     * assume there are bogus values about and that we can't actually figure
     * out what the stack size really is.
     */

#ifdef TCL_THREADS /* Stop warning... */
  finalSanityCheck:
#endif
    if (rawStackSize <= 0) {
	STACK_DEBUG(("skipping stack checks with success\n"));
	return TCL_CONTINUE;
    }

    /*
     * Calculate a stack size with a safety margin.
     */

    *stackSizePtr = (rawStackSize / TCL_MAGIC_STACK_DIVISOR)
	    - (getpagesize() * TCL_RESERVED_STACK_PAGES);

    return TCL_OK;
}
#endif /* TCL_NO_STACK_CHECK */

/*
 *----------------------------------------------------------------------
 *
 * MacOSXGetLibraryPath --
 *
 *	If we have a bundle structure for the Tcl installation, then check
 *	there first to see if we can find the libraries there.
 *
 * Results:
 *	TCL_OK if we have found the tcl library; TCL_ERROR otherwise.
 *
 * Side effects:
 *	Same as for Tcl_MacOSXOpenVersionedBundleResources.
 *
 *----------------------------------------------------------------------
 */

#ifdef HAVE_COREFOUNDATION
static int
MacOSXGetLibraryPath(
    Tcl_Interp *interp,
    int maxPathLen,
    char *tclLibPath)
{
    int foundInFramework = TCL_ERROR;

#ifdef TCL_FRAMEWORK
    foundInFramework = Tcl_MacOSXOpenVersionedBundleResources(interp,
	    "com.tcltk.tcllibrary", TCL_FRAMEWORK_VERSION, 0, maxPathLen,
	    tclLibPath);
#endif

    return foundInFramework;
}
#endif /* HAVE_COREFOUNDATION */

/*
 * Local Variables:
 * mode: c
 * c-basic-offset: 4
 * fill-column: 78
 * End:
 */
