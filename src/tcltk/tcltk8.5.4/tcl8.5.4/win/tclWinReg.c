/*
 * tclWinReg.c --
 *
 *	This file contains the implementation of the "registry" Tcl built-in
 *	command. This command is built as a dynamically loadable extension in
 *	a separate DLL.
 *
 * Copyright (c) 1997 by Sun Microsystems, Inc.
 * Copyright (c) 1998-1999 by Scriptics Corporation.
 *
 * See the file "license.terms" for information on usage and redistribution of
 * this file, and for a DISCLAIMER OF ALL WARRANTIES.
 *
 * RCS: @(#) $Id: tclWinReg.c,v 1.40 2007/05/15 16:12:53 dgp Exp $
 */

#include "tclInt.h"
#ifdef _MSC_VER
#   pragma comment (lib, "advapi32.lib")
#endif
#include <stdlib.h>

/*
 * TCL_STORAGE_CLASS is set unconditionally to DLLEXPORT because the
 * Registry_Init declaration is in the source file itself, which is only
 * accessed when we are building a library.
 */

#undef TCL_STORAGE_CLASS
#define TCL_STORAGE_CLASS DLLEXPORT

/*
 * The following macros convert between different endian ints.
 */

#define SWAPWORD(x) MAKEWORD(HIBYTE(x), LOBYTE(x))
#define SWAPLONG(x) MAKELONG(SWAPWORD(HIWORD(x)), SWAPWORD(LOWORD(x)))

/*
 * The following flag is used in OpenKeys to indicate that the specified key
 * should be created if it doesn't currently exist.
 */

#define REG_CREATE 1

/*
 * The following tables contain the mapping from registry root names to the
 * system predefined keys.
 */

static CONST char *rootKeyNames[] = {
    "HKEY_LOCAL_MACHINE", "HKEY_USERS", "HKEY_CLASSES_ROOT",
    "HKEY_CURRENT_USER", "HKEY_CURRENT_CONFIG",
    "HKEY_PERFORMANCE_DATA", "HKEY_DYN_DATA", NULL
};

static HKEY rootKeys[] = {
    HKEY_LOCAL_MACHINE, HKEY_USERS, HKEY_CLASSES_ROOT, HKEY_CURRENT_USER,
    HKEY_CURRENT_CONFIG, HKEY_PERFORMANCE_DATA, HKEY_DYN_DATA
};

static CONST char REGISTRY_ASSOC_KEY[] = "registry::command";

/*
 * The following table maps from registry types to strings. Note that the
 * indices for this array are the same as the constants for the known registry
 * types so we don't need a separate table to hold the mapping.
 */

static CONST char *typeNames[] = {
    "none", "sz", "expand_sz", "binary", "dword",
    "dword_big_endian", "link", "multi_sz", "resource_list", NULL
};

static DWORD lastType = REG_RESOURCE_LIST;

/*
 * The following structures allow us to select between the Unicode and ASCII
 * interfaces at run time based on whether Unicode APIs are available. The
 * Unicode APIs are preferable because they will handle characters outside of
 * the current code page.
 */

typedef struct RegWinProcs {
    int useWide;

    LONG (WINAPI *regConnectRegistryProc)(CONST TCHAR *, HKEY, PHKEY);
    LONG (WINAPI *regCreateKeyExProc)(HKEY, CONST TCHAR *, DWORD, TCHAR *,
	    DWORD, REGSAM, SECURITY_ATTRIBUTES *, HKEY *, DWORD *);
    LONG (WINAPI *regDeleteKeyProc)(HKEY, CONST TCHAR *);
    LONG (WINAPI *regDeleteValueProc)(HKEY, CONST TCHAR *);
    LONG (WINAPI *regEnumKeyProc)(HKEY, DWORD, TCHAR *, DWORD);
    LONG (WINAPI *regEnumKeyExProc)(HKEY, DWORD, TCHAR *, DWORD *, DWORD *,
	    TCHAR *, DWORD *, FILETIME *);
    LONG (WINAPI *regEnumValueProc)(HKEY, DWORD, TCHAR *, DWORD *, DWORD *,
	    DWORD *, BYTE *, DWORD *);
    LONG (WINAPI *regOpenKeyExProc)(HKEY, CONST TCHAR *, DWORD, REGSAM,
	    HKEY *);
    LONG (WINAPI *regQueryInfoKeyProc)(HKEY, TCHAR *, DWORD *, DWORD *,
	    DWORD *, DWORD *, DWORD *, DWORD *, DWORD *, DWORD *, DWORD *,
	    FILETIME *);
    LONG (WINAPI *regQueryValueExProc)(HKEY, CONST TCHAR *, DWORD *, DWORD *,
	    BYTE *, DWORD *);
    LONG (WINAPI *regSetValueExProc)(HKEY, CONST TCHAR *, DWORD, DWORD,
	    CONST BYTE*, DWORD);
} RegWinProcs;

static RegWinProcs *regWinProcs;

static RegWinProcs asciiProcs = {
    0,

    (LONG (WINAPI *)(CONST TCHAR *, HKEY, PHKEY)) RegConnectRegistryA,
    (LONG (WINAPI *)(HKEY, CONST TCHAR *, DWORD, TCHAR *,
	    DWORD, REGSAM, SECURITY_ATTRIBUTES *, HKEY *,
	    DWORD *)) RegCreateKeyExA,
    (LONG (WINAPI *)(HKEY, CONST TCHAR *)) RegDeleteKeyA,
    (LONG (WINAPI *)(HKEY, CONST TCHAR *)) RegDeleteValueA,
    (LONG (WINAPI *)(HKEY, DWORD, TCHAR *, DWORD)) RegEnumKeyA,
    (LONG (WINAPI *)(HKEY, DWORD, TCHAR *, DWORD *, DWORD *,
	    TCHAR *, DWORD *, FILETIME *)) RegEnumKeyExA,
    (LONG (WINAPI *)(HKEY, DWORD, TCHAR *, DWORD *, DWORD *,
	    DWORD *, BYTE *, DWORD *)) RegEnumValueA,
    (LONG (WINAPI *)(HKEY, CONST TCHAR *, DWORD, REGSAM,
	    HKEY *)) RegOpenKeyExA,
    (LONG (WINAPI *)(HKEY, TCHAR *, DWORD *, DWORD *,
	    DWORD *, DWORD *, DWORD *, DWORD *, DWORD *, DWORD *, DWORD *,
	    FILETIME *)) RegQueryInfoKeyA,
    (LONG (WINAPI *)(HKEY, CONST TCHAR *, DWORD *, DWORD *,
	    BYTE *, DWORD *)) RegQueryValueExA,
    (LONG (WINAPI *)(HKEY, CONST TCHAR *, DWORD, DWORD,
	    CONST BYTE*, DWORD)) RegSetValueExA,
};

static RegWinProcs unicodeProcs = {
    1,

    (LONG (WINAPI *)(CONST TCHAR *, HKEY, PHKEY)) RegConnectRegistryW,
    (LONG (WINAPI *)(HKEY, CONST TCHAR *, DWORD, TCHAR *,
	    DWORD, REGSAM, SECURITY_ATTRIBUTES *, HKEY *,
	    DWORD *)) RegCreateKeyExW,
    (LONG (WINAPI *)(HKEY, CONST TCHAR *)) RegDeleteKeyW,
    (LONG (WINAPI *)(HKEY, CONST TCHAR *)) RegDeleteValueW,
    (LONG (WINAPI *)(HKEY, DWORD, TCHAR *, DWORD)) RegEnumKeyW,
    (LONG (WINAPI *)(HKEY, DWORD, TCHAR *, DWORD *, DWORD *,
	    TCHAR *, DWORD *, FILETIME *)) RegEnumKeyExW,
    (LONG (WINAPI *)(HKEY, DWORD, TCHAR *, DWORD *, DWORD *,
	    DWORD *, BYTE *, DWORD *)) RegEnumValueW,
    (LONG (WINAPI *)(HKEY, CONST TCHAR *, DWORD, REGSAM,
	    HKEY *)) RegOpenKeyExW,
    (LONG (WINAPI *)(HKEY, TCHAR *, DWORD *, DWORD *,
	    DWORD *, DWORD *, DWORD *, DWORD *, DWORD *, DWORD *, DWORD *,
	    FILETIME *)) RegQueryInfoKeyW,
    (LONG (WINAPI *)(HKEY, CONST TCHAR *, DWORD *, DWORD *,
	    BYTE *, DWORD *)) RegQueryValueExW,
    (LONG (WINAPI *)(HKEY, CONST TCHAR *, DWORD, DWORD,
	    CONST BYTE*, DWORD)) RegSetValueExW,
};


/*
 * Declarations for functions defined in this file.
 */

static void		AppendSystemError(Tcl_Interp *interp, DWORD error);
static int		BroadcastValue(Tcl_Interp *interp, int objc,
			    Tcl_Obj * CONST objv[]);
static DWORD		ConvertDWORD(DWORD type, DWORD value);
static void		DeleteCmd(ClientData clientData);
static int		DeleteKey(Tcl_Interp *interp, Tcl_Obj *keyNameObj);
static int		DeleteValue(Tcl_Interp *interp, Tcl_Obj *keyNameObj,
			    Tcl_Obj *valueNameObj);
static int		GetKeyNames(Tcl_Interp *interp, Tcl_Obj *keyNameObj,
			    Tcl_Obj *patternObj);
static int		GetType(Tcl_Interp *interp, Tcl_Obj *keyNameObj,
			    Tcl_Obj *valueNameObj);
static int		GetValue(Tcl_Interp *interp, Tcl_Obj *keyNameObj,
			    Tcl_Obj *valueNameObj);
static int		GetValueNames(Tcl_Interp *interp, Tcl_Obj *keyNameObj,
			    Tcl_Obj *patternObj);
static int		OpenKey(Tcl_Interp *interp, Tcl_Obj *keyNameObj,
			    REGSAM mode, int flags, HKEY *keyPtr);
static DWORD		OpenSubKey(char *hostName, HKEY rootKey,
			    char *keyName, REGSAM mode, int flags,
			    HKEY *keyPtr);
static int		ParseKeyName(Tcl_Interp *interp, char *name,
			    char **hostNamePtr, HKEY *rootKeyPtr,
			    char **keyNamePtr);
static DWORD		RecursiveDeleteKey(HKEY hStartKey,
			    CONST TCHAR * pKeyName);
static int		RegistryObjCmd(ClientData clientData,
			    Tcl_Interp *interp, int objc,
			    Tcl_Obj * CONST objv[]);
static int		SetValue(Tcl_Interp *interp, Tcl_Obj *keyNameObj,
			    Tcl_Obj *valueNameObj, Tcl_Obj *dataObj,
			    Tcl_Obj *typeObj);

EXTERN int		Registry_Init(Tcl_Interp *interp);
EXTERN int		Registry_Unload(Tcl_Interp *interp, int flags);

/*
 *----------------------------------------------------------------------
 *
 * Registry_Init --
 *
 *	This function initializes the registry command.
 *
 * Results:
 *	A standard Tcl result.
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */

int
Registry_Init(
    Tcl_Interp *interp)
{
    Tcl_Command cmd;

    if (Tcl_InitStubs(interp, "8.1", 0) == NULL) {
	return TCL_ERROR;
    }

    /*
     * Determine if the unicode interfaces are available and select the
     * appropriate registry function table.
     */

    if (TclWinGetPlatformId() == VER_PLATFORM_WIN32_NT) {
	regWinProcs = &unicodeProcs;
    } else {
	regWinProcs = &asciiProcs;
    }

    cmd = Tcl_CreateObjCommand(interp, "registry", RegistryObjCmd,
	(ClientData)interp, DeleteCmd);
    Tcl_SetAssocData(interp, REGISTRY_ASSOC_KEY, NULL, (ClientData)cmd);
    return Tcl_PkgProvide(interp, "registry", "1.2.1");
}

/*
 *----------------------------------------------------------------------
 *
 * Registry_Unload --
 *
 *	This function removes the registry command.
 *
 * Results:
 *	A standard Tcl result.
 *
 * Side effects:
 *	The registry command is deleted and the dll may be unloaded.
 *
 *----------------------------------------------------------------------
 */

int
Registry_Unload(
    Tcl_Interp *interp,		/* Interpreter for unloading */
    int flags)			/* Flags passed by the unload system */
{
    Tcl_Command cmd;
    Tcl_Obj *objv[3];

    /*
     * Unregister the registry package. There is no Tcl_PkgForget()
     */

    objv[0] = Tcl_NewStringObj("package", -1);
    objv[1] = Tcl_NewStringObj("forget", -1);
    objv[2] = Tcl_NewStringObj("registry", -1);
    Tcl_EvalObjv(interp, 3, objv, TCL_EVAL_GLOBAL);

    /*
     * Delete the originally registered command.
     */

    cmd = (Tcl_Command)Tcl_GetAssocData(interp, REGISTRY_ASSOC_KEY, NULL);
    if (cmd != NULL) {
	Tcl_DeleteCommandFromToken(interp, cmd);
    }

    return TCL_OK;
}

/*
 *----------------------------------------------------------------------
 *
 * DeleteCmd --
 *
 *	Cleanup the interp command token so that unloading doesn't try to
 *	re-delete the command (which will crash).
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	The unload command will not attempt to delete this command.
 *
 *----------------------------------------------------------------------
 */

static void
DeleteCmd(
    ClientData clientData)
{
    Tcl_Interp *interp = clientData;
    Tcl_SetAssocData(interp, REGISTRY_ASSOC_KEY, NULL, (ClientData)NULL);
}

/*
 *----------------------------------------------------------------------
 *
 * RegistryObjCmd --
 *
 *	This function implements the Tcl "registry" command.
 *
 * Results:
 *	A standard Tcl result.
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */

static int
RegistryObjCmd(
    ClientData clientData,	/* Not used. */
    Tcl_Interp *interp,		/* Current interpreter. */
    int objc,			/* Number of arguments. */
    Tcl_Obj * CONST objv[])	/* Argument values. */
{
    int index;
    char *errString = NULL;

    static CONST char *subcommands[] = {
	"broadcast", "delete", "get", "keys", "set", "type", "values", NULL
    };
    enum SubCmdIdx {
	BroadcastIdx, DeleteIdx, GetIdx, KeysIdx, SetIdx, TypeIdx, ValuesIdx
    };

    if (objc < 2) {
	Tcl_WrongNumArgs(interp, objc, objv, "option ?arg arg ...?");
	return TCL_ERROR;
    }

    if (Tcl_GetIndexFromObj(interp, objv[1], subcommands, "option", 0, &index)
	    != TCL_OK) {
	return TCL_ERROR;
    }

    switch (index) {
    case BroadcastIdx:		/* broadcast */
	return BroadcastValue(interp, objc, objv);
	break;
    case DeleteIdx:		/* delete */
	if (objc == 3) {
	    return DeleteKey(interp, objv[2]);
	} else if (objc == 4) {
	    return DeleteValue(interp, objv[2], objv[3]);
	}
	errString = "keyName ?valueName?";
	break;
    case GetIdx:		/* get */
	if (objc == 4) {
	    return GetValue(interp, objv[2], objv[3]);
	}
	errString = "keyName valueName";
	break;
    case KeysIdx:		/* keys */
	if (objc == 3) {
	    return GetKeyNames(interp, objv[2], NULL);
	} else if (objc == 4) {
	    return GetKeyNames(interp, objv[2], objv[3]);
	}
	errString = "keyName ?pattern?";
	break;
    case SetIdx:		/* set */
	if (objc == 3) {
	    HKEY key;

	    /*
	     * Create the key and then close it immediately.
	     */

	    if (OpenKey(interp, objv[2], KEY_ALL_ACCESS, 1, &key) != TCL_OK) {
		return TCL_ERROR;
	    }
	    RegCloseKey(key);
	    return TCL_OK;
	} else if (objc == 5 || objc == 6) {
	    Tcl_Obj *typeObj = (objc == 5) ? NULL : objv[5];
	    return SetValue(interp, objv[2], objv[3], objv[4], typeObj);
	}
	errString = "keyName ?valueName data ?type??";
	break;
    case TypeIdx:		/* type */
	if (objc == 4) {
	    return GetType(interp, objv[2], objv[3]);
	}
	errString = "keyName valueName";
	break;
    case ValuesIdx:		/* values */
	if (objc == 3) {
	    return GetValueNames(interp, objv[2], NULL);
	} else if (objc == 4) {
	    return GetValueNames(interp, objv[2], objv[3]);
	}
	errString = "keyName ?pattern?";
	break;
    }
    Tcl_WrongNumArgs(interp, 2, objv, errString);
    return TCL_ERROR;
}

/*
 *----------------------------------------------------------------------
 *
 * DeleteKey --
 *
 *	This function deletes a registry key.
 *
 * Results:
 *	A standard Tcl result.
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */

static int
DeleteKey(
    Tcl_Interp *interp,		/* Current interpreter. */
    Tcl_Obj *keyNameObj)	/* Name of key to delete. */
{
    char *tail, *buffer, *hostName, *keyName;
    CONST char *nativeTail;
    HKEY rootKey, subkey;
    DWORD result;
    int length;
    Tcl_DString buf;

    /*
     * Find the parent of the key being deleted and open it.
     */

    keyName = Tcl_GetStringFromObj(keyNameObj, &length);
    buffer = ckalloc((unsigned int) length + 1);
    strcpy(buffer, keyName);

    if (ParseKeyName(interp, buffer, &hostName, &rootKey,
	    &keyName) != TCL_OK) {
	ckfree(buffer);
	return TCL_ERROR;
    }

    if (*keyName == '\0') {
	Tcl_SetObjResult(interp, Tcl_NewStringObj(
		"bad key: cannot delete root keys", -1));
	ckfree(buffer);
	return TCL_ERROR;
    }

    tail = strrchr(keyName, '\\');
    if (tail) {
	*tail++ = '\0';
    } else {
	tail = keyName;
	keyName = NULL;
    }

    result = OpenSubKey(hostName, rootKey, keyName,
	    KEY_ENUMERATE_SUB_KEYS | DELETE, 0, &subkey);
    if (result != ERROR_SUCCESS) {
	ckfree(buffer);
	if (result == ERROR_FILE_NOT_FOUND) {
	    return TCL_OK;
	}
	Tcl_SetObjResult(interp, Tcl_NewStringObj(
		"unable to delete key: ", -1));
	AppendSystemError(interp, result);
	return TCL_ERROR;
    }

    /*
     * Now we recursively delete the key and everything below it.
     */

    nativeTail = Tcl_WinUtfToTChar(tail, -1, &buf);
    result = RecursiveDeleteKey(subkey, nativeTail);
    Tcl_DStringFree(&buf);

    if (result != ERROR_SUCCESS && result != ERROR_FILE_NOT_FOUND) {
	Tcl_SetObjResult(interp,
		Tcl_NewStringObj("unable to delete key: ", -1));
	AppendSystemError(interp, result);
	result = TCL_ERROR;
    } else {
	result = TCL_OK;
    }

    RegCloseKey(subkey);
    ckfree(buffer);
    return result;
}

/*
 *----------------------------------------------------------------------
 *
 * DeleteValue --
 *
 *	This function deletes a value from a registry key.
 *
 * Results:
 *	A standard Tcl result.
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */

static int
DeleteValue(
    Tcl_Interp *interp,		/* Current interpreter. */
    Tcl_Obj *keyNameObj,	/* Name of key. */
    Tcl_Obj *valueNameObj)	/* Name of value to delete. */
{
    HKEY key;
    char *valueName;
    int length;
    DWORD result;
    Tcl_DString ds;

    /*
     * Attempt to open the key for deletion.
     */

    if (OpenKey(interp, keyNameObj, KEY_SET_VALUE, 0, &key)
	    != TCL_OK) {
	return TCL_ERROR;
    }

    valueName = Tcl_GetStringFromObj(valueNameObj, &length);
    Tcl_WinUtfToTChar(valueName, length, &ds);
    result = (*regWinProcs->regDeleteValueProc)(key, Tcl_DStringValue(&ds));
    Tcl_DStringFree(&ds);
    if (result != ERROR_SUCCESS) {
	Tcl_AppendResult(interp, "unable to delete value \"",
		Tcl_GetString(valueNameObj), "\" from key \"",
		Tcl_GetString(keyNameObj), "\": ", NULL);
	AppendSystemError(interp, result);
	result = TCL_ERROR;
    } else {
	result = TCL_OK;
    }
    RegCloseKey(key);
    return result;
}

/*
 *----------------------------------------------------------------------
 *
 * GetKeyNames --
 *
 *	This function enumerates the subkeys of a given key. If the optional
 *	pattern is supplied, then only keys that match the pattern will be
 *	returned.
 *
 * Results:
 *	Returns the list of subkeys in the result object of the interpreter,
 *	or an error message on failure.
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */

static int
GetKeyNames(
    Tcl_Interp *interp,		/* Current interpreter. */
    Tcl_Obj *keyNameObj,	/* Key to enumerate. */
    Tcl_Obj *patternObj)	/* Optional match pattern. */
{
    char *pattern;		/* Pattern being matched against subkeys */
    HKEY key;			/* Handle to the key being examined */
    DWORD subKeyCount;		/* Number of subkeys to list */
    DWORD maxSubKeyLen;		/* Maximum string length of any subkey */
    char *buffer;		/* Buffer to hold the subkey name */
    DWORD bufSize;		/* Size of the buffer */
    DWORD index;		/* Position of the current subkey */
    char *name;			/* Subkey name */
    Tcl_Obj *resultPtr;		/* List of subkeys being accumulated */
    int result = TCL_OK;	/* Return value from this command */
    Tcl_DString ds;		/* Buffer to translate subkey name to UTF-8 */

    if (patternObj) {
	pattern = Tcl_GetString(patternObj);
    } else {
	pattern = NULL;
    }

    /* Attempt to open the key for enumeration. */

    if (OpenKey(interp, keyNameObj,
		KEY_QUERY_VALUE | KEY_ENUMERATE_SUB_KEYS,
		0, &key) != TCL_OK) {
	return TCL_ERROR;
    }

    /* 
     * Determine how big a buffer is needed for enumerating subkeys, and
     * how many subkeys there are
     */

    result = (*regWinProcs->regQueryInfoKeyProc)
	(key, NULL, NULL, NULL, &subKeyCount, &maxSubKeyLen, NULL, NULL, 
	 NULL, NULL, NULL, NULL);
    if (result != ERROR_SUCCESS) {
	Tcl_SetObjResult(interp, Tcl_NewObj());
	Tcl_AppendResult(interp, "unable to query key \"", 
			 Tcl_GetString(keyNameObj), "\": ", NULL);
	AppendSystemError(interp, result);
	RegCloseKey(key);
	return TCL_ERROR;
    }
    if (regWinProcs->useWide) {
	buffer = ckalloc((maxSubKeyLen+1) * sizeof(WCHAR));
    } else {
	buffer = ckalloc(maxSubKeyLen+1);
    }

    /* Enumerate the subkeys */

    resultPtr = Tcl_NewObj();
    for (index = 0; index < subKeyCount; ++index) {
	bufSize = maxSubKeyLen+1;
	result = (*regWinProcs->regEnumKeyExProc)
	    (key, index, buffer, &bufSize, NULL, NULL, NULL, NULL);
	if (result != ERROR_SUCCESS) {
	    Tcl_SetObjResult(interp, Tcl_NewObj());
	    Tcl_AppendResult(interp,
			     "unable to enumerate subkeys of \"",
			     Tcl_GetString(keyNameObj),
			     "\": ", NULL);
	    AppendSystemError(interp, result);
	    result = TCL_ERROR;
	    break;
	}
	if (regWinProcs->useWide) {
	    Tcl_WinTCharToUtf((TCHAR *) buffer, bufSize * sizeof(WCHAR), &ds);
	} else {
	    Tcl_WinTCharToUtf((TCHAR *) buffer, bufSize, &ds);
	}
	name = Tcl_DStringValue(&ds);
	if (pattern && !Tcl_StringMatch(name, pattern)) {
	    Tcl_DStringFree(&ds);
	    continue;
	}
	result = Tcl_ListObjAppendElement(interp, resultPtr,
		Tcl_NewStringObj(name, Tcl_DStringLength(&ds)));
	Tcl_DStringFree(&ds);
	if (result != TCL_OK) {
	    break;
	}
    }
    if (result == TCL_OK) {
	Tcl_SetObjResult(interp, resultPtr);
    }

    ckfree(buffer);
    RegCloseKey(key);
    return result;
}

/*
 *----------------------------------------------------------------------
 *
 * GetType --
 *
 *	This function gets the type of a given registry value and places it in
 *	the interpreter result.
 *
 * Results:
 *	Returns a normal Tcl result.
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */

static int
GetType(
    Tcl_Interp *interp,		/* Current interpreter. */
    Tcl_Obj *keyNameObj,	/* Name of key. */
    Tcl_Obj *valueNameObj)	/* Name of value to get. */
{
    HKEY key;
    DWORD result;
    DWORD type;
    Tcl_DString ds;
    char *valueName;
    CONST char *nativeValue;
    int length;

    /*
     * Attempt to open the key for reading.
     */

    if (OpenKey(interp, keyNameObj, KEY_QUERY_VALUE, 0, &key)
	    != TCL_OK) {
	return TCL_ERROR;
    }

    /*
     * Get the type of the value.
     */

    valueName = Tcl_GetStringFromObj(valueNameObj, &length);
    nativeValue = Tcl_WinUtfToTChar(valueName, length, &ds);
    result = (*regWinProcs->regQueryValueExProc)(key, nativeValue, NULL, &type,
	    NULL, NULL);
    Tcl_DStringFree(&ds);
    RegCloseKey(key);

    if (result != ERROR_SUCCESS) {
	Tcl_AppendResult(interp, "unable to get type of value \"",
		Tcl_GetString(valueNameObj), "\" from key \"",
		Tcl_GetString(keyNameObj), "\": ", NULL);
	AppendSystemError(interp, result);
	return TCL_ERROR;
    }

    /*
     * Set the type into the result. Watch out for unknown types. If we don't
     * know about the type, just use the numeric value.
     */

    if (type > lastType || type < 0) {
	Tcl_SetObjResult(interp, Tcl_NewIntObj((int) type));
    } else {
	Tcl_SetObjResult(interp, Tcl_NewStringObj(typeNames[type], -1));
    }
    return TCL_OK;
}

/*
 *----------------------------------------------------------------------
 *
 * GetValue --
 *
 *	This function gets the contents of a registry value and places a list
 *	containing the data and the type in the interpreter result.
 *
 * Results:
 *	Returns a normal Tcl result.
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */

static int
GetValue(
    Tcl_Interp *interp,		/* Current interpreter. */
    Tcl_Obj *keyNameObj,	/* Name of key. */
    Tcl_Obj *valueNameObj)	/* Name of value to get. */
{
    HKEY key;
    char *valueName;
    CONST char *nativeValue;
    DWORD result, length, type;
    Tcl_DString data, buf;
    int nameLen;

    /*
     * Attempt to open the key for reading.
     */

    if (OpenKey(interp, keyNameObj, KEY_QUERY_VALUE, 0, &key) != TCL_OK) {
	return TCL_ERROR;
    }

    /*
     * Initialize a Dstring to maximum statically allocated size we could get
     * one more byte by avoiding Tcl_DStringSetLength() and just setting
     * length to TCL_DSTRING_STATIC_SIZE, but this should be safer if the
     * implementation of Dstrings changes.
     *
     * This allows short values to be read from the registy in one call.
     * Longer values need a second call with an expanded DString.
     */

    Tcl_DStringInit(&data);
    length = TCL_DSTRING_STATIC_SIZE - 1;
    Tcl_DStringSetLength(&data, (int) length);

    valueName = Tcl_GetStringFromObj(valueNameObj, &nameLen);
    nativeValue = Tcl_WinUtfToTChar(valueName, nameLen, &buf);

    result = (*regWinProcs->regQueryValueExProc)(key, nativeValue, NULL, &type,
	    (BYTE *) Tcl_DStringValue(&data), &length);
    while (result == ERROR_MORE_DATA) {
	/*
	 * The Windows docs say that in this error case, we just need to
	 * expand our buffer and request more data. Required for
	 * HKEY_PERFORMANCE_DATA
	 */

	length *= 2;
	Tcl_DStringSetLength(&data, (int) length);
	result = (*regWinProcs->regQueryValueExProc)(key, (char *) nativeValue,
		NULL, &type, (BYTE *) Tcl_DStringValue(&data), &length);
    }
    Tcl_DStringFree(&buf);
    RegCloseKey(key);
    if (result != ERROR_SUCCESS) {
	Tcl_AppendResult(interp, "unable to get value \"",
		Tcl_GetString(valueNameObj), "\" from key \"",
		Tcl_GetString(keyNameObj), "\": ", NULL);
	AppendSystemError(interp, result);
	Tcl_DStringFree(&data);
	return TCL_ERROR;
    }

    /*
     * If the data is a 32-bit quantity, store it as an integer object. If it
     * is a multi-string, store it as a list of strings. For null-terminated
     * strings, append up the to first null. Otherwise, store it as a binary
     * string.
     */

    if (type == REG_DWORD || type == REG_DWORD_BIG_ENDIAN) {
	Tcl_SetObjResult(interp, Tcl_NewIntObj((int) ConvertDWORD(type,
		*((DWORD*) Tcl_DStringValue(&data)))));
    } else if (type == REG_MULTI_SZ) {
	char *p = Tcl_DStringValue(&data);
	char *end = Tcl_DStringValue(&data) + length;
	Tcl_Obj *resultPtr = Tcl_NewObj();

	/*
	 * Multistrings are stored as an array of null-terminated strings,
	 * terminated by two null characters. Also do a bounds check in case
	 * we get bogus data.
	 */

	while (p < end 	&& ((regWinProcs->useWide)
		? *((Tcl_UniChar *)p) : *p) != 0) {
	    Tcl_WinTCharToUtf((TCHAR *) p, -1, &buf);
	    Tcl_ListObjAppendElement(interp, resultPtr,
		    Tcl_NewStringObj(Tcl_DStringValue(&buf),
			    Tcl_DStringLength(&buf)));
	    if (regWinProcs->useWide) {
		Tcl_UniChar* up = (Tcl_UniChar*) p;
		while (*up++ != 0) {}
		p = (char*) up;
	    } else {
		while (*p++ != '\0') {}
	    }
	    Tcl_DStringFree(&buf);
	}
	Tcl_SetObjResult(interp, resultPtr);
    } else if ((type == REG_SZ) || (type == REG_EXPAND_SZ)) {
	Tcl_WinTCharToUtf((TCHAR *) Tcl_DStringValue(&data), -1, &buf);
	Tcl_DStringResult(interp, &buf);
    } else {
	/*
	 * Save binary data as a byte array.
	 */

	Tcl_SetObjResult(interp, Tcl_NewByteArrayObj(
		Tcl_DStringValue(&data), (int) length));
    }
    Tcl_DStringFree(&data);
    return result;
}

/*
 *----------------------------------------------------------------------
 *
 * GetValueNames --
 *
 *	This function enumerates the values of the a given key. If the
 *	optional pattern is supplied, then only value names that match the
 *	pattern will be returned.
 *
 * Results:
 *	Returns the list of value names in the result object of the
 *	interpreter, or an error message on failure.
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */

static int
GetValueNames(
    Tcl_Interp *interp,		/* Current interpreter. */
    Tcl_Obj *keyNameObj,	/* Key to enumerate. */
    Tcl_Obj *patternObj)	/* Optional match pattern. */
{
    HKEY key;
    Tcl_Obj *resultPtr;
    DWORD index, size, maxSize, result;
    Tcl_DString buffer, ds;
    char *pattern, *name;

    /*
     * Attempt to open the key for enumeration.
     */

    if (OpenKey(interp, keyNameObj, KEY_QUERY_VALUE, 0, &key)
	    != TCL_OK) {
	return TCL_ERROR;
    }

    /*
     * Query the key to determine the appropriate buffer size to hold the
     * largest value name plus the terminating null.
     */

    result = (*regWinProcs->regQueryInfoKeyProc)(key, NULL, NULL, NULL, NULL,
	    NULL, NULL, &index, &maxSize, NULL, NULL, NULL);
    if (result != ERROR_SUCCESS) {
	Tcl_AppendResult(interp, "unable to query key \"",
		Tcl_GetString(keyNameObj), "\": ", NULL);
	AppendSystemError(interp, result);
	RegCloseKey(key);
	result = TCL_ERROR;
	goto done;
    }
    maxSize++;

    resultPtr = Tcl_NewObj();
    Tcl_DStringInit(&buffer);
    Tcl_DStringSetLength(&buffer,
	    (int) ((regWinProcs->useWide) ? maxSize*2 : maxSize));
    index = 0;
    result = TCL_OK;

    if (patternObj) {
	pattern = Tcl_GetString(patternObj);
    } else {
	pattern = NULL;
    }

    /*
     * Enumerate the values under the given subkey until we get an error,
     * indicating the end of the list. Note that we need to reset size after
     * each iteration because RegEnumValue smashes the old value.
     */

    size = maxSize;
    while ((*regWinProcs->regEnumValueProc)(key, index,
	    Tcl_DStringValue(&buffer), &size, NULL, NULL, NULL, NULL)
	    == ERROR_SUCCESS) {

	if (regWinProcs->useWide) {
	    size *= 2;
	}

	Tcl_WinTCharToUtf((TCHAR *) Tcl_DStringValue(&buffer), (int) size,
		&ds);
	name = Tcl_DStringValue(&ds);
	if (!pattern || Tcl_StringMatch(name, pattern)) {
	    result = Tcl_ListObjAppendElement(interp, resultPtr,
		    Tcl_NewStringObj(name, Tcl_DStringLength(&ds)));
	    if (result != TCL_OK) {
		Tcl_DStringFree(&ds);
		break;
	    }
	}
	Tcl_DStringFree(&ds);

	index++;
	size = maxSize;
    }
    Tcl_SetObjResult(interp, resultPtr);
    Tcl_DStringFree(&buffer);

  done:
    RegCloseKey(key);
    return result;
}

/*
 *----------------------------------------------------------------------
 *
 * OpenKey --
 *
 *	This function opens the specified key. This function is a simple
 *	wrapper around ParseKeyName and OpenSubKey.
 *
 * Results:
 *	Returns the opened key in the keyPtr argument and a Tcl result code.
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */

static int
OpenKey(
    Tcl_Interp *interp,		/* Current interpreter. */
    Tcl_Obj *keyNameObj,	/* Key to open. */
    REGSAM mode,		/* Access mode. */
    int flags,			/* 0 or REG_CREATE. */
    HKEY *keyPtr)		/* Returned HKEY. */
{
    char *keyName, *buffer, *hostName;
    int length;
    HKEY rootKey;
    DWORD result;

    keyName = Tcl_GetStringFromObj(keyNameObj, &length);
    buffer = ckalloc((unsigned int) length + 1);
    strcpy(buffer, keyName);

    result = ParseKeyName(interp, buffer, &hostName, &rootKey, &keyName);
    if (result == TCL_OK) {
	result = OpenSubKey(hostName, rootKey, keyName, mode, flags, keyPtr);
	if (result != ERROR_SUCCESS) {
	    Tcl_SetObjResult(interp,
		    Tcl_NewStringObj("unable to open key: ", -1));
	    AppendSystemError(interp, result);
	    result = TCL_ERROR;
	} else {
	    result = TCL_OK;
	}
    }

    ckfree(buffer);
    return result;
}

/*
 *----------------------------------------------------------------------
 *
 * OpenSubKey --
 *
 *	This function opens a given subkey of a root key on the specified
 *	host.
 *
 * Results:
 *	Returns the opened key in the keyPtr and a Windows error code as the
 *	return value.
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */

static DWORD
OpenSubKey(
    char *hostName,		/* Host to access, or NULL for local. */
    HKEY rootKey,		/* Root registry key. */
    char *keyName,		/* Subkey name. */
    REGSAM mode,		/* Access mode. */
    int flags,			/* 0 or REG_CREATE. */
    HKEY *keyPtr)		/* Returned HKEY. */
{
    DWORD result;
    Tcl_DString buf;

    /*
     * Attempt to open the root key on a remote host if necessary.
     */

    if (hostName) {
	hostName = (char *) Tcl_WinUtfToTChar(hostName, -1, &buf);
	result = (*regWinProcs->regConnectRegistryProc)(hostName, rootKey,
		&rootKey);
	Tcl_DStringFree(&buf);
	if (result != ERROR_SUCCESS) {
	    return result;
	}
    }

    /*
     * Now open the specified key with the requested permissions. Note that
     * this key must be closed by the caller.
     */

    keyName = (char *) Tcl_WinUtfToTChar(keyName, -1, &buf);
    if (flags & REG_CREATE) {
	DWORD create;
	result = (*regWinProcs->regCreateKeyExProc)(rootKey, keyName, 0, NULL,
		REG_OPTION_NON_VOLATILE, mode, NULL, keyPtr, &create);
    } else if (rootKey == HKEY_PERFORMANCE_DATA) {
	/*
	 * Here we fudge it for this special root key. See MSDN for more info
	 * on HKEY_PERFORMANCE_DATA and the peculiarities surrounding it.
	 */
	*keyPtr = HKEY_PERFORMANCE_DATA;
	result = ERROR_SUCCESS;
    } else {
	result = (*regWinProcs->regOpenKeyExProc)(rootKey, keyName, 0, mode,
		keyPtr);
    }
    Tcl_DStringFree(&buf);

    /*
     * Be sure to close the root key since we are done with it now.
     */

    if (hostName) {
	RegCloseKey(rootKey);
    }
    return result;
}

/*
 *----------------------------------------------------------------------
 *
 * ParseKeyName --
 *
 *	This function parses a key name into the host, root, and subkey parts.
 *
 * Results:
 *	The pointers to the start of the host and subkey names are returned in
 *	the hostNamePtr and keyNamePtr variables. The specified root HKEY is
 *	returned in rootKeyPtr. Returns a standard Tcl result.
 *
 * Side effects:
 *	Modifies the name string by inserting nulls.
 *
 *----------------------------------------------------------------------
 */

static int
ParseKeyName(
    Tcl_Interp *interp,		/* Current interpreter. */
    char *name,
    char **hostNamePtr,
    HKEY *rootKeyPtr,
    char **keyNamePtr)
{
    char *rootName;
    int result, index;
    Tcl_Obj *rootObj;

    /*
     * Split the key into host and root portions.
     */

    *hostNamePtr = *keyNamePtr = rootName = NULL;
    if (name[0] == '\\') {
	if (name[1] == '\\') {
	    *hostNamePtr = name;
	    for (rootName = name+2; *rootName != '\0'; rootName++) {
		if (*rootName == '\\') {
		    *rootName++ = '\0';
		    break;
		}
	    }
	}
    } else {
	rootName = name;
    }
    if (!rootName) {
	Tcl_AppendResult(interp, "bad key \"", name,
		"\": must start with a valid root", NULL);
	return TCL_ERROR;
    }

    /*
     * Split the root into root and subkey portions.
     */

    for (*keyNamePtr = rootName; **keyNamePtr != '\0'; (*keyNamePtr)++) {
	if (**keyNamePtr == '\\') {
	    **keyNamePtr = '\0';
	    (*keyNamePtr)++;
	    break;
	}
    }

    /*
     * Look for a matching root name.
     */

    rootObj = Tcl_NewStringObj(rootName, -1);
    result = Tcl_GetIndexFromObj(interp, rootObj, rootKeyNames, "root name",
	    TCL_EXACT, &index);
    Tcl_DecrRefCount(rootObj);
    if (result != TCL_OK) {
	return TCL_ERROR;
    }
    *rootKeyPtr = rootKeys[index];
    return TCL_OK;
}

/*
 *----------------------------------------------------------------------
 *
 * RecursiveDeleteKey --
 *
 *	This function recursively deletes all the keys below a starting key.
 *	Although Windows 95 does this automatically, we still need to do this
 *	for Windows NT.
 *
 * Results:
 *	Returns a Windows error code.
 *
 * Side effects:
 *	Deletes all of the keys and values below the given key.
 *
 *----------------------------------------------------------------------
 */

static DWORD
RecursiveDeleteKey(
    HKEY startKey,		/* Parent of key to be deleted. */
    CONST char *keyName)	/* Name of key to be deleted in external
				 * encoding, not UTF. */
{
    DWORD result, size, maxSize;
    Tcl_DString subkey;
    HKEY hKey;

    /*
     * Do not allow NULL or empty key name.
     */

    if (!keyName || *keyName == '\0') {
	return ERROR_BADKEY;
    }

    result = (*regWinProcs->regOpenKeyExProc)(startKey, keyName, 0,
	    KEY_ENUMERATE_SUB_KEYS | DELETE | KEY_QUERY_VALUE, &hKey);
    if (result != ERROR_SUCCESS) {
	return result;
    }
    result = (*regWinProcs->regQueryInfoKeyProc)(hKey, NULL, NULL, NULL, NULL,
	    &maxSize, NULL, NULL, NULL, NULL, NULL, NULL);
    maxSize++;
    if (result != ERROR_SUCCESS) {
	return result;
    }

    Tcl_DStringInit(&subkey);
    Tcl_DStringSetLength(&subkey,
	    (int) ((regWinProcs->useWide) ? maxSize * 2 : maxSize));

    while (result == ERROR_SUCCESS) {
	/*
	 * Always get index 0 because key deletion changes ordering.
	 */

	size = maxSize;
	result=(*regWinProcs->regEnumKeyExProc)(hKey, 0,
		Tcl_DStringValue(&subkey), &size, NULL, NULL, NULL, NULL);
	if (result == ERROR_NO_MORE_ITEMS) {
	    result = (*regWinProcs->regDeleteKeyProc)(startKey, keyName);
	    break;
	} else if (result == ERROR_SUCCESS) {
	    result = RecursiveDeleteKey(hKey, Tcl_DStringValue(&subkey));
	}
    }
    Tcl_DStringFree(&subkey);
    RegCloseKey(hKey);
    return result;
}

/*
 *----------------------------------------------------------------------
 *
 * SetValue --
 *
 *	This function sets the contents of a registry value. If the key or
 *	value does not exist, it will be created. If it does exist, then the
 *	data and type will be replaced.
 *
 * Results:
 *	Returns a normal Tcl result.
 *
 * Side effects:
 *	May create new keys or values.
 *
 *----------------------------------------------------------------------
 */

static int
SetValue(
    Tcl_Interp *interp,		/* Current interpreter. */
    Tcl_Obj *keyNameObj,	/* Name of key. */
    Tcl_Obj *valueNameObj,	/* Name of value to set. */
    Tcl_Obj *dataObj,		/* Data to be written. */
    Tcl_Obj *typeObj)		/* Type of data to be written. */
{
    int type;
    DWORD result;
    HKEY key;
    int length;
    char *valueName;
    Tcl_DString nameBuf;

    if (typeObj == NULL) {
	type = REG_SZ;
    } else if (Tcl_GetIndexFromObj(interp, typeObj, typeNames, "type",
	    0, (int *) &type) != TCL_OK) {
	if (Tcl_GetIntFromObj(NULL, typeObj, (int*) &type) != TCL_OK) {
	    return TCL_ERROR;
	}
	Tcl_ResetResult(interp);
    }
    if (OpenKey(interp, keyNameObj, KEY_ALL_ACCESS, 1, &key) != TCL_OK) {
	return TCL_ERROR;
    }

    valueName = Tcl_GetStringFromObj(valueNameObj, &length);
    valueName = (char *) Tcl_WinUtfToTChar(valueName, length, &nameBuf);

    if (type == REG_DWORD || type == REG_DWORD_BIG_ENDIAN) {
	int value;

	if (Tcl_GetIntFromObj(interp, dataObj, &value) != TCL_OK) {
	    RegCloseKey(key);
	    Tcl_DStringFree(&nameBuf);
	    return TCL_ERROR;
	}

	value = ConvertDWORD((DWORD)type, (DWORD)value);
	result = (*regWinProcs->regSetValueExProc)(key, valueName, 0,
		(DWORD) type, (BYTE *) &value, sizeof(DWORD));
    } else if (type == REG_MULTI_SZ) {
	Tcl_DString data, buf;
	int objc, i;
	Tcl_Obj **objv;

	if (Tcl_ListObjGetElements(interp, dataObj, &objc, &objv) != TCL_OK) {
	    RegCloseKey(key);
	    Tcl_DStringFree(&nameBuf);
	    return TCL_ERROR;
	}

	/*
	 * Append the elements as null terminated strings. Note that we must
	 * not assume the length of the string in case there are embedded
	 * nulls, which aren't allowed in REG_MULTI_SZ values.
	 */

	Tcl_DStringInit(&data);
	for (i = 0; i < objc; i++) {
	    Tcl_DStringAppend(&data, Tcl_GetString(objv[i]), -1);

	    /*
	     * Add a null character to separate this value from the next. We
	     * accomplish this by growing the string by one byte. Since the
	     * DString always tacks on an extra null byte, the new byte will
	     * already be set to null.
	     */

	    Tcl_DStringSetLength(&data, Tcl_DStringLength(&data)+1);
	}

	Tcl_WinUtfToTChar(Tcl_DStringValue(&data), Tcl_DStringLength(&data)+1,
		&buf);
	result = (*regWinProcs->regSetValueExProc)(key, valueName, 0,
                (DWORD) type, (BYTE *) Tcl_DStringValue(&buf),
		(DWORD) Tcl_DStringLength(&buf));
	Tcl_DStringFree(&data);
	Tcl_DStringFree(&buf);
    } else if (type == REG_SZ || type == REG_EXPAND_SZ) {
	Tcl_DString buf;
	char *data = Tcl_GetStringFromObj(dataObj, &length);

	data = (char *) Tcl_WinUtfToTChar(data, length, &buf);

	/*
	 * Include the null in the length, padding if needed for Unicode.
	 */

	if (regWinProcs->useWide) {
	    Tcl_DStringSetLength(&buf, Tcl_DStringLength(&buf)+1);
	}
	length = Tcl_DStringLength(&buf) + 1;

	result = (*regWinProcs->regSetValueExProc)(key, valueName, 0,
                (DWORD) type, (BYTE *) data, (DWORD) length);
	Tcl_DStringFree(&buf);
    } else {
	char *data;

	/*
	 * Store binary data in the registry.
	 */

	data = Tcl_GetByteArrayFromObj(dataObj, &length);
	result = (*regWinProcs->regSetValueExProc)(key, valueName, 0,
                (DWORD) type, (BYTE *) data, (DWORD) length);
    }

    Tcl_DStringFree(&nameBuf);
    RegCloseKey(key);

    if (result != ERROR_SUCCESS) {
	Tcl_SetObjResult(interp,
		Tcl_NewStringObj("unable to set value: ", -1));
	AppendSystemError(interp, result);
	return TCL_ERROR;
    }
    return TCL_OK;
}

/*
 *----------------------------------------------------------------------
 *
 * BroadcastValue --
 *
 *	This function broadcasts a WM_SETTINGCHANGE message to indicate to
 *	other programs that we have changed the contents of a registry value.
 *
 * Results:
 *	Returns a normal Tcl result.
 *
 * Side effects:
 *	Will cause other programs to reload their system settings.
 *
 *----------------------------------------------------------------------
 */

static int
BroadcastValue(
    Tcl_Interp *interp,		/* Current interpreter. */
    int objc,			/* Number of arguments. */
    Tcl_Obj *CONST objv[])	/* Argument values. */
{
    LRESULT result, sendResult;
    UINT timeout = 3000;
    int len;
    char *str;
    Tcl_Obj *objPtr;

    if ((objc != 3) && (objc != 5)) {
	Tcl_WrongNumArgs(interp, 2, objv, "keyName ?-timeout millisecs?");
	return TCL_ERROR;
    }

    if (objc > 3) {
	str = Tcl_GetStringFromObj(objv[3], &len);
	if ((len < 2) || (*str != '-')
		|| strncmp(str, "-timeout", (size_t) len)) {
	    Tcl_WrongNumArgs(interp, 2, objv, "keyName ?-timeout millisecs?");
	    return TCL_ERROR;
	}
	if (Tcl_GetIntFromObj(interp, objv[4], (int *) &timeout) != TCL_OK) {
	    return TCL_ERROR;
	}
    }

    str = Tcl_GetStringFromObj(objv[2], &len);
    if (len == 0) {
	str = NULL;
    }

    /*
     * Use the ignore the result.
     */

    result = SendMessageTimeout(HWND_BROADCAST, WM_SETTINGCHANGE,
	    (WPARAM) 0, (LPARAM) str, SMTO_ABORTIFHUNG, timeout, &sendResult);

    objPtr = Tcl_NewObj();
    Tcl_ListObjAppendElement(NULL, objPtr, Tcl_NewLongObj((long) result));
    Tcl_ListObjAppendElement(NULL, objPtr, Tcl_NewLongObj((long) sendResult));
    Tcl_SetObjResult(interp, objPtr);

    return TCL_OK;
}

/*
 *----------------------------------------------------------------------
 *
 * AppendSystemError --
 *
 *	This routine formats a Windows system error message and places it into
 *	the interpreter result.
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
AppendSystemError(
    Tcl_Interp *interp,		/* Current interpreter. */
    DWORD error)		/* Result code from error. */
{
    int length;
    WCHAR *wMsgPtr, **wMsgPtrPtr = &wMsgPtr;
    char *msg;
    char id[TCL_INTEGER_SPACE], msgBuf[24 + TCL_INTEGER_SPACE];
    Tcl_DString ds;
    Tcl_Obj *resultPtr = Tcl_GetObjResult(interp);

    if (Tcl_IsShared(resultPtr)) {
	resultPtr = Tcl_DuplicateObj(resultPtr);
    }
    length = FormatMessageW(FORMAT_MESSAGE_FROM_SYSTEM
	    | FORMAT_MESSAGE_ALLOCATE_BUFFER, NULL, error,
	    MAKELANGID(LANG_NEUTRAL, SUBLANG_DEFAULT), (WCHAR *) wMsgPtrPtr,
	    0, NULL);
    if (length == 0) {
	char *msgPtr;

	length = FormatMessageA(FORMAT_MESSAGE_FROM_SYSTEM
		| FORMAT_MESSAGE_ALLOCATE_BUFFER, NULL, error,
		MAKELANGID(LANG_NEUTRAL, SUBLANG_DEFAULT), (char *) &msgPtr,
		0, NULL);
	if (length > 0) {
	    wMsgPtr = (WCHAR *) LocalAlloc(LPTR, (length + 1) * sizeof(WCHAR));
	    MultiByteToWideChar(CP_ACP, 0, msgPtr, length + 1, wMsgPtr,
		    length + 1);
	    LocalFree(msgPtr);
	}
    }
    if (length == 0) {
	if (error == ERROR_CALL_NOT_IMPLEMENTED) {
	    msg = "function not supported under Win32s";
	} else {
	    sprintf(msgBuf, "unknown error: %ld", error);
	    msg = msgBuf;
	}
    } else {
	Tcl_Encoding encoding;

	encoding = Tcl_GetEncoding(NULL, "unicode");
	Tcl_ExternalToUtfDString(encoding, (char *) wMsgPtr, -1, &ds);
	Tcl_FreeEncoding(encoding);
	LocalFree(wMsgPtr);

	msg = Tcl_DStringValue(&ds);
	length = Tcl_DStringLength(&ds);

	/*
	 * Trim the trailing CR/LF from the system message.
	 */

	if (msg[length-1] == '\n') {
	    msg[--length] = 0;
	}
	if (msg[length-1] == '\r') {
	    msg[--length] = 0;
	}
    }

    sprintf(id, "%ld", error);
    Tcl_SetErrorCode(interp, "WINDOWS", id, msg, NULL);
    Tcl_AppendToObj(resultPtr, msg, length);
    Tcl_SetObjResult(interp, resultPtr);

    if (length != 0) {
	Tcl_DStringFree(&ds);
    }
}

/*
 *----------------------------------------------------------------------
 *
 * ConvertDWORD --
 *
 *	This function determines whether a DWORD needs to be byte swapped, and
 *	returns the appropriately swapped value.
 *
 * Results:
 *	Returns a converted DWORD.
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */

static DWORD
ConvertDWORD(
    DWORD type,			/* Either REG_DWORD or REG_DWORD_BIG_ENDIAN */
    DWORD value)		/* The value to be converted. */
{
    DWORD order = 1;
    DWORD localType;

    /*
     * Check to see if the low bit is in the first byte.
     */

    localType = (*((char*)(&order)) == 1) ? REG_DWORD : REG_DWORD_BIG_ENDIAN;
    return (type != localType) ? SWAPLONG(value) : value;
}

/*
 * Local Variables:
 * mode: c
 * c-basic-offset: 4
 * fill-column: 78
 * End:
 */
