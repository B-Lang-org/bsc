/*
 * tclTestObj.c --
 *
 *	This file contains C command functions for the additional Tcl commands
 *	that are used for testing implementations of the Tcl object types.
 *	These commands are not normally included in Tcl applications; they're
 *	only used for testing.
 *
 * Copyright (c) 1995-1998 Sun Microsystems, Inc.
 * Copyright (c) 1999 by Scriptics Corporation.
 * Copyright (c) 2005 by Kevin B. Kenny.  All rights reserved.
 *
 * See the file "license.terms" for information on usage and redistribution of
 * this file, and for a DISCLAIMER OF ALL WARRANTIES.
 *
 * RCS: @(#) $Id: tclTestObj.c,v 1.21 2007/12/13 15:23:20 dgp Exp $
 */

#include "tclInt.h"
#include "tommath.h"

/*
 * An array of Tcl_Obj pointers used in the commands that operate on or get
 * the values of Tcl object-valued variables. varPtr[i] is the i-th variable's
 * Tcl_Obj *.
 */

#define NUMBER_OF_OBJECT_VARS 20
static Tcl_Obj *varPtr[NUMBER_OF_OBJECT_VARS];

/*
 * Forward declarations for functions defined later in this file:
 */

static int		CheckIfVarUnset(Tcl_Interp *interp, int varIndex);
static int		GetVariableIndex(Tcl_Interp *interp,
			    char *string, int *indexPtr);
static void		SetVarToObj(int varIndex, Tcl_Obj *objPtr);
int			TclObjTest_Init(Tcl_Interp *interp);
static int		TestbignumobjCmd(ClientData dummy, Tcl_Interp *interp,
			    int objc, Tcl_Obj *const objv[]);
static int		TestbooleanobjCmd(ClientData dummy,
			    Tcl_Interp *interp, int objc,
			    Tcl_Obj *const objv[]);
static int		TestdoubleobjCmd(ClientData dummy, Tcl_Interp *interp,
			    int objc, Tcl_Obj *const objv[]);
static int		TestindexobjCmd(ClientData dummy, Tcl_Interp *interp,
			    int objc, Tcl_Obj *const objv[]);
static int		TestintobjCmd(ClientData dummy, Tcl_Interp *interp,
			    int objc, Tcl_Obj *const objv[]);
static int		TestobjCmd(ClientData dummy, Tcl_Interp *interp,
			    int objc, Tcl_Obj *const objv[]);
static int		TeststringobjCmd(ClientData dummy, Tcl_Interp *interp,
			    int objc, Tcl_Obj *const objv[]);

typedef struct TestString {
    int numChars;
    size_t allocated;
    size_t uallocated;
    Tcl_UniChar unicode[2];
} TestString;

/*
 *----------------------------------------------------------------------
 *
 * TclObjTest_Init --
 *
 *	This function creates additional commands that are used to test the
 *	Tcl object support.
 *
 * Results:
 *	Returns a standard Tcl completion code, and leaves an error
 *	message in the interp's result if an error occurs.
 *
 * Side effects:
 *	Creates and registers several new testing commands.
 *
 *----------------------------------------------------------------------
 */

int
TclObjTest_Init(
    Tcl_Interp *interp)
{
    register int i;

    for (i = 0;  i < NUMBER_OF_OBJECT_VARS;  i++) {
        varPtr[i] = NULL;
    }

    Tcl_CreateObjCommand(interp, "testbignumobj", TestbignumobjCmd,
	    (ClientData) 0, NULL);
    Tcl_CreateObjCommand(interp, "testbooleanobj", TestbooleanobjCmd,
	    (ClientData) 0, NULL);
    Tcl_CreateObjCommand(interp, "testdoubleobj", TestdoubleobjCmd,
	    (ClientData) 0, NULL);
    Tcl_CreateObjCommand(interp, "testintobj", TestintobjCmd,
	    (ClientData) 0, NULL);
    Tcl_CreateObjCommand(interp, "testindexobj", TestindexobjCmd,
	    (ClientData) 0, NULL);
    Tcl_CreateObjCommand(interp, "testobj", TestobjCmd, (ClientData) 0, NULL);
    Tcl_CreateObjCommand(interp, "teststringobj", TeststringobjCmd,
	    (ClientData) 0, NULL);
    return TCL_OK;
}

/*
 *----------------------------------------------------------------------
 *
 * TestbignumobjCmd --
 *
 *	This function implmenets the "testbignumobj" command.  It is used
 *	to exercise the bignum Tcl object type implementation.
 *
 * Results:
 *	Returns a standard Tcl object result.
 *
 * Side effects:
 *	Creates and frees bignum objects; converts objects to have bignum
 *	type.
 *
 *----------------------------------------------------------------------
 */

static int
TestbignumobjCmd(
    ClientData clientData,	/* unused */
    Tcl_Interp *interp,		/* Tcl interpreter */
    int objc,			/* Argument count */
    Tcl_Obj *const objv[])	/* Argument vector */
{
    const char * subcmds[] = {
	"set",      "get",      "mult10",      "div10", NULL
    };
    enum options {
	BIGNUM_SET, BIGNUM_GET, BIGNUM_MULT10, BIGNUM_DIV10
    };

    int index, varIndex;
    char* string;
    mp_int bignumValue, newValue;

    if (objc < 3) {
	Tcl_WrongNumArgs(interp, 1, objv, "option ?arg?...");
	return TCL_ERROR;
    }
    if (Tcl_GetIndexFromObj(interp, objv[1], subcmds, "option", 0,
	    &index) != TCL_OK) {
	return TCL_ERROR;
    }
    string = Tcl_GetString(objv[2]);
    if (GetVariableIndex(interp, string, &varIndex) != TCL_OK) {
	return TCL_ERROR;
    }

    switch (index) {
    case BIGNUM_SET:
	if (objc != 4) {
	    Tcl_WrongNumArgs(interp, 2, objv, "var value");
	    return TCL_ERROR;
	}
	string = Tcl_GetString(objv[3]);
	if (mp_init(&bignumValue) != MP_OKAY) {
	    Tcl_SetObjResult(interp,
		    Tcl_NewStringObj("error in mp_init", -1));
	    return TCL_ERROR;
	}
	if (mp_read_radix(&bignumValue, string, 10) != MP_OKAY) {
	    mp_clear(&bignumValue);
	    Tcl_SetObjResult(interp,
		    Tcl_NewStringObj("error in mp_read_radix", -1));
	    return TCL_ERROR;
	}

	/*
	 * If the object currently bound to the variable with index varIndex
	 * has ref count 1 (i.e. the object is unshared) we can modify that
	 * object directly.  Otherwise, if RC>1 (i.e. the object is shared),
	 * we must create a new object to modify/set and decrement the old
	 * formerly-shared object's ref count. This is "copy on write".
	 */

	if ((varPtr[varIndex] != NULL) && !Tcl_IsShared(varPtr[varIndex])) {
	    Tcl_SetBignumObj(varPtr[varIndex], &bignumValue);
	} else {
	    SetVarToObj(varIndex, Tcl_NewBignumObj(&bignumValue));
	}
	break;

    case BIGNUM_GET:
	if (objc != 3) {
	    Tcl_WrongNumArgs(interp, 2, objv, "varIndex");
	    return TCL_ERROR;
	}
	if (CheckIfVarUnset(interp, varIndex)) {
	    return TCL_ERROR;
	}
	break;

    case BIGNUM_MULT10:
	if (objc != 3) {
	    Tcl_WrongNumArgs(interp, 2, objv, "varIndex");
	    return TCL_ERROR;
	}
	if (CheckIfVarUnset(interp, varIndex)) {
	    return TCL_ERROR;
	}
	if (Tcl_GetBignumFromObj(interp, varPtr[varIndex],
		&bignumValue) != TCL_OK) {
	    return TCL_ERROR;
	}
	if (mp_init(&newValue) != MP_OKAY
		|| (mp_mul_d(&bignumValue, 10, &newValue) != MP_OKAY)) {
	    mp_clear(&bignumValue);
	    mp_clear(&newValue);
	    Tcl_SetObjResult(interp,
		    Tcl_NewStringObj("error in mp_mul_d", -1));
	    return TCL_ERROR;
	}
	mp_clear(&bignumValue);
	if (!Tcl_IsShared(varPtr[varIndex])) {
	    Tcl_SetBignumObj(varPtr[varIndex], &newValue);
	} else {
	    SetVarToObj(varIndex, Tcl_NewBignumObj(&newValue));
	}
	break;

    case BIGNUM_DIV10:
	if (objc != 3) {
	    Tcl_WrongNumArgs(interp, 2, objv, "varIndex");
	    return TCL_ERROR;
	}
	if (CheckIfVarUnset(interp, varIndex)) {
	    return TCL_ERROR;
	}
	if (Tcl_GetBignumFromObj(interp, varPtr[varIndex],
		&bignumValue) != TCL_OK) {
	    return TCL_ERROR;
	}
	if (mp_init(&newValue) != MP_OKAY
		|| (mp_div_d(&bignumValue, 10, &newValue, NULL) != MP_OKAY)) {
	    mp_clear(&bignumValue);
	    mp_clear(&newValue);
	    Tcl_SetObjResult(interp,
		    Tcl_NewStringObj("error in mp_div_d", -1));
	    return TCL_ERROR;
	}
	mp_clear(&bignumValue);
	if (!Tcl_IsShared(varPtr[varIndex])) {
	    Tcl_SetBignumObj(varPtr[varIndex], &newValue);
	} else {
	    SetVarToObj(varIndex, Tcl_NewBignumObj(&newValue));
	}
    }

    Tcl_SetObjResult(interp, varPtr[varIndex]);
    return TCL_OK;
}

/*
 *----------------------------------------------------------------------
 *
 * TestbooleanobjCmd --
 *
 *	This function implements the "testbooleanobj" command.  It is used to
 *	test the boolean Tcl object type implementation.
 *
 * Results:
 *	A standard Tcl object result.
 *
 * Side effects:
 *	Creates and frees boolean objects, and also converts objects to
 *	have boolean type.
 *
 *----------------------------------------------------------------------
 */

static int
TestbooleanobjCmd(
    ClientData clientData,	/* Not used. */
    Tcl_Interp *interp,		/* Current interpreter. */
    int objc,			/* Number of arguments. */
    Tcl_Obj *const objv[])	/* Argument objects. */
{
    int varIndex, boolValue;
    char *index, *subCmd;

    if (objc < 3) {
	wrongNumArgs:
	Tcl_WrongNumArgs(interp, 1, objv, "option arg ?arg ...?");
	return TCL_ERROR;
    }

    index = Tcl_GetString(objv[2]);
    if (GetVariableIndex(interp, index, &varIndex) != TCL_OK) {
	return TCL_ERROR;
    }

    subCmd = Tcl_GetString(objv[1]);
    if (strcmp(subCmd, "set") == 0) {
	if (objc != 4) {
	    goto wrongNumArgs;
	}
	if (Tcl_GetBooleanFromObj(interp, objv[3], &boolValue) != TCL_OK) {
	    return TCL_ERROR;
	}

	/*
	 * If the object currently bound to the variable with index varIndex
	 * has ref count 1 (i.e. the object is unshared) we can modify that
	 * object directly. Otherwise, if RC>1 (i.e. the object is shared),
	 * we must create a new object to modify/set and decrement the old
	 * formerly-shared object's ref count. This is "copy on write".
	 */

	if ((varPtr[varIndex] != NULL) && !Tcl_IsShared(varPtr[varIndex])) {
	    Tcl_SetBooleanObj(varPtr[varIndex], boolValue);
	} else {
	    SetVarToObj(varIndex, Tcl_NewBooleanObj(boolValue));
	}
	Tcl_SetObjResult(interp, varPtr[varIndex]);
    } else if (strcmp(subCmd, "get") == 0) {
	if (objc != 3) {
	    goto wrongNumArgs;
	}
	if (CheckIfVarUnset(interp, varIndex)) {
	    return TCL_ERROR;
	}
	Tcl_SetObjResult(interp, varPtr[varIndex]);
    } else if (strcmp(subCmd, "not") == 0) {
	if (objc != 3) {
	    goto wrongNumArgs;
	}
	if (CheckIfVarUnset(interp, varIndex)) {
	    return TCL_ERROR;
	}
	if (Tcl_GetBooleanFromObj(interp, varPtr[varIndex],
				  &boolValue) != TCL_OK) {
	    return TCL_ERROR;
	}
	if (!Tcl_IsShared(varPtr[varIndex])) {
	    Tcl_SetBooleanObj(varPtr[varIndex], !boolValue);
	} else {
	    SetVarToObj(varIndex, Tcl_NewBooleanObj(!boolValue));
	}
	Tcl_SetObjResult(interp, varPtr[varIndex]);
    } else {
	Tcl_AppendStringsToObj(Tcl_GetObjResult(interp),
		"bad option \"", Tcl_GetString(objv[1]),
		"\": must be set, get, or not", NULL);
	return TCL_ERROR;
    }
    return TCL_OK;
}

/*
 *----------------------------------------------------------------------
 *
 * TestdoubleobjCmd --
 *
 *	This function implements the "testdoubleobj" command.  It is used to
 *	test the double-precision floating point Tcl object type
 *	implementation.
 *
 * Results:
 *	A standard Tcl object result.
 *
 * Side effects:
 *	Creates and frees double objects, and also converts objects to
 *	have double type.
 *
 *----------------------------------------------------------------------
 */

static int
TestdoubleobjCmd(
    ClientData clientData,	/* Not used. */
    Tcl_Interp *interp,		/* Current interpreter. */
    int objc,			/* Number of arguments. */
    Tcl_Obj *const objv[])	/* Argument objects. */
{
    int varIndex;
    double doubleValue;
    char *index, *subCmd, *string;

    if (objc < 3) {
	wrongNumArgs:
	Tcl_WrongNumArgs(interp, 1, objv, "option arg ?arg ...?");
	return TCL_ERROR;
    }

    index = Tcl_GetString(objv[2]);
    if (GetVariableIndex(interp, index, &varIndex) != TCL_OK) {
	return TCL_ERROR;
    }

    subCmd = Tcl_GetString(objv[1]);
    if (strcmp(subCmd, "set") == 0) {
	if (objc != 4) {
	    goto wrongNumArgs;
	}
	string = Tcl_GetString(objv[3]);
	if (Tcl_GetDouble(interp, string, &doubleValue) != TCL_OK) {
	    return TCL_ERROR;
	}

	/*
	 * If the object currently bound to the variable with index varIndex
	 * has ref count 1 (i.e. the object is unshared) we can modify that
	 * object directly. Otherwise, if RC>1 (i.e. the object is shared), we
	 * must create a new object to modify/set and decrement the old
	 * formerly-shared object's ref count. This is "copy on write".
	 */

	if ((varPtr[varIndex] != NULL) && !Tcl_IsShared(varPtr[varIndex])) {
	    Tcl_SetDoubleObj(varPtr[varIndex], doubleValue);
	} else {
	    SetVarToObj(varIndex, Tcl_NewDoubleObj(doubleValue));
	}
	Tcl_SetObjResult(interp, varPtr[varIndex]);
    } else if (strcmp(subCmd, "get") == 0) {
	if (objc != 3) {
	    goto wrongNumArgs;
	}
	if (CheckIfVarUnset(interp, varIndex)) {
	    return TCL_ERROR;
	}
	Tcl_SetObjResult(interp, varPtr[varIndex]);
    } else if (strcmp(subCmd, "mult10") == 0) {
	if (objc != 3) {
	    goto wrongNumArgs;
	}
	if (CheckIfVarUnset(interp, varIndex)) {
	    return TCL_ERROR;
	}
	if (Tcl_GetDoubleFromObj(interp, varPtr[varIndex],
				 &doubleValue) != TCL_OK) {
	    return TCL_ERROR;
	}
	if (!Tcl_IsShared(varPtr[varIndex])) {
	    Tcl_SetDoubleObj(varPtr[varIndex], (doubleValue * 10.0));
	} else {
	    SetVarToObj(varIndex, Tcl_NewDoubleObj( (doubleValue * 10.0) ));
	}
	Tcl_SetObjResult(interp, varPtr[varIndex]);
    } else if (strcmp(subCmd, "div10") == 0) {
	if (objc != 3) {
	    goto wrongNumArgs;
	}
	if (CheckIfVarUnset(interp, varIndex)) {
	    return TCL_ERROR;
	}
	if (Tcl_GetDoubleFromObj(interp, varPtr[varIndex],
				 &doubleValue) != TCL_OK) {
	    return TCL_ERROR;
	}
	if (!Tcl_IsShared(varPtr[varIndex])) {
	    Tcl_SetDoubleObj(varPtr[varIndex], (doubleValue / 10.0));
	} else {
	    SetVarToObj(varIndex, Tcl_NewDoubleObj( (doubleValue / 10.0) ));
	}
	Tcl_SetObjResult(interp, varPtr[varIndex]);
    } else {
	Tcl_AppendStringsToObj(Tcl_GetObjResult(interp),
		"bad option \"", Tcl_GetString(objv[1]),
		"\": must be set, get, mult10, or div10", NULL);
	return TCL_ERROR;
    }
    return TCL_OK;
}

/*
 *----------------------------------------------------------------------
 *
 * TestindexobjCmd --
 *
 *	This function implements the "testindexobj" command. It is used to
 *	test the index Tcl object type implementation.
 *
 * Results:
 *	A standard Tcl object result.
 *
 * Side effects:
 *	Creates and frees int objects, and also converts objects to
 *	have int type.
 *
 *----------------------------------------------------------------------
 */

static int
TestindexobjCmd(
    ClientData clientData,	/* Not used. */
    Tcl_Interp *interp,		/* Current interpreter. */
    int objc,			/* Number of arguments. */
    Tcl_Obj *const objv[])	/* Argument objects. */
{
    int allowAbbrev, index, index2, setError, i, result;
    const char **argv;
    static const char *tablePtr[] = {"a", "b", "check", NULL};
    /*
     * Keep this structure declaration in sync with tclIndexObj.c
     */
    struct IndexRep {
	VOID *tablePtr;			/* Pointer to the table of strings */
	int offset;			/* Offset between table entries */
	int index;			/* Selected index into table. */
    };
    struct IndexRep *indexRep;

    if ((objc == 3) && (strcmp(Tcl_GetString(objv[1]),
	    "check") == 0)) {
	/*
	 * This code checks to be sure that the results of Tcl_GetIndexFromObj
	 * are properly cached in the object and returned on subsequent
	 * lookups.
	 */

	if (Tcl_GetIntFromObj(interp, objv[2], &index2) != TCL_OK) {
	    return TCL_ERROR;
	}

	Tcl_GetIndexFromObj(NULL, objv[1], tablePtr, "token", 0, &index);
	indexRep = (struct IndexRep *) objv[1]->internalRep.otherValuePtr;
	indexRep->index = index2;
	result = Tcl_GetIndexFromObj(NULL, objv[1],
		tablePtr, "token", 0, &index);
	if (result == TCL_OK) {
	    Tcl_SetIntObj(Tcl_GetObjResult(interp), index);
	}
	return result;
    }

    if (objc < 5) {
	Tcl_AppendToObj(Tcl_GetObjResult(interp), "wrong # args", -1);
	return TCL_ERROR;
    }

    if (Tcl_GetBooleanFromObj(interp, objv[1], &setError) != TCL_OK) {
	return TCL_ERROR;
    }
    if (Tcl_GetBooleanFromObj(interp, objv[2], &allowAbbrev) != TCL_OK) {
	return TCL_ERROR;
    }

    argv = (const char **) ckalloc((unsigned) ((objc-3) * sizeof(char *)));
    for (i = 4; i < objc; i++) {
	argv[i-4] = Tcl_GetString(objv[i]);
    }
    argv[objc-4] = NULL;

    /*
     * Tcl_GetIndexFromObj assumes that the table is statically-allocated so
     * that its address is different for each index object. If we accidently
     * allocate a table at the same address as that cached in the index
     * object, clear out the object's cached state.
     */

    if ( objv[3]->typePtr != NULL
	 && !strcmp( "index", objv[3]->typePtr->name ) ) {
	indexRep = (struct IndexRep *) objv[3]->internalRep.otherValuePtr;
	if (indexRep->tablePtr == (VOID *) argv) {
	    objv[3]->typePtr->freeIntRepProc(objv[3]);
	    objv[3]->typePtr = NULL;
	}
    }

    result = Tcl_GetIndexFromObj((setError? interp : NULL), objv[3],
	    argv, "token", (allowAbbrev? 0 : TCL_EXACT), &index);
    ckfree((char *) argv);
    if (result == TCL_OK) {
	Tcl_SetIntObj(Tcl_GetObjResult(interp), index);
    }
    return result;
}

/*
 *----------------------------------------------------------------------
 *
 * TestintobjCmd --
 *
 *	This function implements the "testintobj" command. It is used to
 *	test the int Tcl object type implementation.
 *
 * Results:
 *	A standard Tcl object result.
 *
 * Side effects:
 *	Creates and frees int objects, and also converts objects to
 *	have int type.
 *
 *----------------------------------------------------------------------
 */

static int
TestintobjCmd(
    ClientData clientData,	/* Not used. */
    Tcl_Interp *interp,		/* Current interpreter. */
    int objc,			/* Number of arguments. */
    Tcl_Obj *const objv[])	/* Argument objects. */
{
    int intValue, varIndex, i;
    long longValue;
    char *index, *subCmd, *string;

    if (objc < 3) {
	wrongNumArgs:
	Tcl_WrongNumArgs(interp, 1, objv, "option arg ?arg ...?");
	return TCL_ERROR;
    }

    index = Tcl_GetString(objv[2]);
    if (GetVariableIndex(interp, index, &varIndex) != TCL_OK) {
	return TCL_ERROR;
    }

    subCmd = Tcl_GetString(objv[1]);
    if (strcmp(subCmd, "set") == 0) {
	if (objc != 4) {
	    goto wrongNumArgs;
	}
	string = Tcl_GetString(objv[3]);
	if (Tcl_GetInt(interp, string, &i) != TCL_OK) {
	    return TCL_ERROR;
	}
	intValue = i;

	/*
	 * If the object currently bound to the variable with index varIndex
	 * has ref count 1 (i.e. the object is unshared) we can modify that
	 * object directly. Otherwise, if RC>1 (i.e. the object is shared), we
	 * must create a new object to modify/set and decrement the old
	 * formerly-shared object's ref count. This is "copy on write".
	 */

	if ((varPtr[varIndex] != NULL) && !Tcl_IsShared(varPtr[varIndex])) {
	    Tcl_SetIntObj(varPtr[varIndex], intValue);
	} else {
	    SetVarToObj(varIndex, Tcl_NewIntObj(intValue));
	}
	Tcl_SetObjResult(interp, varPtr[varIndex]);
    } else if (strcmp(subCmd, "set2") == 0) { /* doesn't set result */
	if (objc != 4) {
	    goto wrongNumArgs;
	}
	string = Tcl_GetString(objv[3]);
	if (Tcl_GetInt(interp, string, &i) != TCL_OK) {
	    return TCL_ERROR;
	}
	intValue = i;
	if ((varPtr[varIndex] != NULL) && !Tcl_IsShared(varPtr[varIndex])) {
	    Tcl_SetIntObj(varPtr[varIndex], intValue);
	} else {
	    SetVarToObj(varIndex, Tcl_NewIntObj(intValue));
	}
    } else if (strcmp(subCmd, "setlong") == 0) {
	if (objc != 4) {
	    goto wrongNumArgs;
	}
	string = Tcl_GetString(objv[3]);
	if (Tcl_GetInt(interp, string, &i) != TCL_OK) {
	    return TCL_ERROR;
	}
	intValue = i;
	if ((varPtr[varIndex] != NULL) && !Tcl_IsShared(varPtr[varIndex])) {
	    Tcl_SetLongObj(varPtr[varIndex], intValue);
	} else {
	    SetVarToObj(varIndex, Tcl_NewLongObj(intValue));
	}
	Tcl_SetObjResult(interp, varPtr[varIndex]);
    } else if (strcmp(subCmd, "setmaxlong") == 0) {
	long maxLong = LONG_MAX;
	if (objc != 3) {
	    goto wrongNumArgs;
	}
	if ((varPtr[varIndex] != NULL) && !Tcl_IsShared(varPtr[varIndex])) {
	    Tcl_SetLongObj(varPtr[varIndex], maxLong);
	} else {
	    SetVarToObj(varIndex, Tcl_NewLongObj(maxLong));
	}
    } else if (strcmp(subCmd, "ismaxlong") == 0) {
	if (objc != 3) {
	    goto wrongNumArgs;
	}
	if (CheckIfVarUnset(interp, varIndex)) {
	    return TCL_ERROR;
	}
	if (Tcl_GetLongFromObj(interp, varPtr[varIndex], &longValue) != TCL_OK) {
	    return TCL_ERROR;
	}
	Tcl_AppendToObj(Tcl_GetObjResult(interp),
	        ((longValue == LONG_MAX)? "1" : "0"), -1);
    } else if (strcmp(subCmd, "get") == 0) {
	if (objc != 3) {
	    goto wrongNumArgs;
	}
	if (CheckIfVarUnset(interp, varIndex)) {
	    return TCL_ERROR;
	}
	Tcl_SetObjResult(interp, varPtr[varIndex]);
    } else if (strcmp(subCmd, "get2") == 0) {
	if (objc != 3) {
	    goto wrongNumArgs;
	}
	if (CheckIfVarUnset(interp, varIndex)) {
	    return TCL_ERROR;
	}
	string = Tcl_GetString(varPtr[varIndex]);
	Tcl_AppendToObj(Tcl_GetObjResult(interp), string, -1);
    } else if (strcmp(subCmd, "inttoobigtest") == 0) {
	/*
	 * If long ints have more bits than ints on this platform, verify that
	 * Tcl_GetIntFromObj returns an error if the long int held in an
	 * integer object's internal representation is too large to fit in an
	 * int.
	 */

	if (objc != 3) {
	    goto wrongNumArgs;
	}
#if (INT_MAX == LONG_MAX)   /* int is same size as long int */
	Tcl_AppendToObj(Tcl_GetObjResult(interp), "1", -1);
#else
	if ((varPtr[varIndex] != NULL) && !Tcl_IsShared(varPtr[varIndex])) {
	    Tcl_SetLongObj(varPtr[varIndex], LONG_MAX);
	} else {
	    SetVarToObj(varIndex, Tcl_NewLongObj(LONG_MAX));
	}
	if (Tcl_GetIntFromObj(interp, varPtr[varIndex], &i) != TCL_OK) {
	    Tcl_ResetResult(interp);
	    Tcl_AppendToObj(Tcl_GetObjResult(interp), "1", -1);
	    return TCL_OK;
	}
	Tcl_AppendToObj(Tcl_GetObjResult(interp), "0", -1);
#endif
    } else if (strcmp(subCmd, "mult10") == 0) {
	if (objc != 3) {
	    goto wrongNumArgs;
	}
	if (CheckIfVarUnset(interp, varIndex)) {
	    return TCL_ERROR;
	}
	if (Tcl_GetIntFromObj(interp, varPtr[varIndex],
			      &intValue) != TCL_OK) {
	    return TCL_ERROR;
	}
	if (!Tcl_IsShared(varPtr[varIndex])) {
	    Tcl_SetIntObj(varPtr[varIndex], (intValue * 10));
	} else {
	    SetVarToObj(varIndex, Tcl_NewIntObj( (intValue * 10) ));
	}
	Tcl_SetObjResult(interp, varPtr[varIndex]);
    } else if (strcmp(subCmd, "div10") == 0) {
	if (objc != 3) {
	    goto wrongNumArgs;
	}
	if (CheckIfVarUnset(interp, varIndex)) {
	    return TCL_ERROR;
	}
	if (Tcl_GetIntFromObj(interp, varPtr[varIndex],
			      &intValue) != TCL_OK) {
	    return TCL_ERROR;
	}
	if (!Tcl_IsShared(varPtr[varIndex])) {
	    Tcl_SetIntObj(varPtr[varIndex], (intValue / 10));
	} else {
	    SetVarToObj(varIndex, Tcl_NewIntObj( (intValue / 10) ));
	}
	Tcl_SetObjResult(interp, varPtr[varIndex]);
    } else {
	Tcl_AppendStringsToObj(Tcl_GetObjResult(interp),
		"bad option \"", Tcl_GetString(objv[1]),
		"\": must be set, get, get2, mult10, or div10", NULL);
	return TCL_ERROR;
    }
    return TCL_OK;
}

/*
 *----------------------------------------------------------------------
 *
 * TestobjCmd --
 *
 *	This function implements the "testobj" command. It is used to test
 *	the type-independent portions of the Tcl object type implementation.
 *
 * Results:
 *	A standard Tcl object result.
 *
 * Side effects:
 *	Creates and frees objects.
 *
 *----------------------------------------------------------------------
 */

static int
TestobjCmd(
    ClientData clientData,	/* Not used. */
    Tcl_Interp *interp,		/* Current interpreter. */
    int objc,			/* Number of arguments. */
    Tcl_Obj *const objv[])	/* Argument objects. */
{
    int varIndex, destIndex, i;
    char *index, *subCmd, *string;
    Tcl_ObjType *targetType;

    if (objc < 2) {
	wrongNumArgs:
	Tcl_WrongNumArgs(interp, 1, objv, "option arg ?arg ...?");
	return TCL_ERROR;
    }

    subCmd = Tcl_GetString(objv[1]);
    if (strcmp(subCmd, "assign") == 0) {
        if (objc != 4) {
            goto wrongNumArgs;
        }
        index = Tcl_GetString(objv[2]);
        if (GetVariableIndex(interp, index, &varIndex) != TCL_OK) {
            return TCL_ERROR;
        }
        if (CheckIfVarUnset(interp, varIndex)) {
	    return TCL_ERROR;
	}
	string = Tcl_GetString(objv[3]);
        if (GetVariableIndex(interp, string, &destIndex) != TCL_OK) {
            return TCL_ERROR;
        }
        SetVarToObj(destIndex, varPtr[varIndex]);
	Tcl_SetObjResult(interp, varPtr[destIndex]);
     } else if (strcmp(subCmd, "convert") == 0) {
        char *typeName;
        if (objc != 4) {
            goto wrongNumArgs;
        }
        index = Tcl_GetString(objv[2]);
        if (GetVariableIndex(interp, index, &varIndex) != TCL_OK) {
            return TCL_ERROR;
        }
        if (CheckIfVarUnset(interp, varIndex)) {
	    return TCL_ERROR;
	}
        typeName = Tcl_GetString(objv[3]);
        if ((targetType = Tcl_GetObjType(typeName)) == NULL) {
	    Tcl_AppendStringsToObj(Tcl_GetObjResult(interp),
		    "no type ", typeName, " found", NULL);
            return TCL_ERROR;
        }
        if (Tcl_ConvertToType(interp, varPtr[varIndex], targetType)
            != TCL_OK) {
            return TCL_ERROR;
        }
	Tcl_SetObjResult(interp, varPtr[varIndex]);
    } else if (strcmp(subCmd, "duplicate") == 0) {
        if (objc != 4) {
            goto wrongNumArgs;
        }
        index = Tcl_GetString(objv[2]);
        if (GetVariableIndex(interp, index, &varIndex) != TCL_OK) {
            return TCL_ERROR;
        }
        if (CheckIfVarUnset(interp, varIndex)) {
	    return TCL_ERROR;
	}
	string = Tcl_GetString(objv[3]);
        if (GetVariableIndex(interp, string, &destIndex) != TCL_OK) {
            return TCL_ERROR;
        }
        SetVarToObj(destIndex, Tcl_DuplicateObj(varPtr[varIndex]));
	Tcl_SetObjResult(interp, varPtr[destIndex]);
    } else if (strcmp(subCmd, "freeallvars") == 0) {
        if (objc != 2) {
            goto wrongNumArgs;
        }
        for (i = 0;  i < NUMBER_OF_OBJECT_VARS;  i++) {
            if (varPtr[i] != NULL) {
                Tcl_DecrRefCount(varPtr[i]);
                varPtr[i] = NULL;
            }
        }
    } else if ( strcmp ( subCmd, "invalidateStringRep" ) == 0 ) {
	if ( objc != 3 ) {
	    goto wrongNumArgs;
	}
	index = Tcl_GetString( objv[2] );
	if ( GetVariableIndex( interp, index, &varIndex ) != TCL_OK ) {
	    return TCL_ERROR;
	}
        if (CheckIfVarUnset(interp, varIndex)) {
	    return TCL_ERROR;
	}
	Tcl_InvalidateStringRep( varPtr[varIndex] );
	Tcl_SetObjResult( interp, varPtr[varIndex] );
    } else if (strcmp(subCmd, "newobj") == 0) {
        if (objc != 3) {
            goto wrongNumArgs;
        }
        index = Tcl_GetString(objv[2]);
        if (GetVariableIndex(interp, index, &varIndex) != TCL_OK) {
            return TCL_ERROR;
        }
        SetVarToObj(varIndex, Tcl_NewObj());
	Tcl_SetObjResult(interp, varPtr[varIndex]);
    } else if (strcmp(subCmd, "objtype") == 0) {
	const char *typeName;

	/*
	 * return an object containing the name of the argument's type
	 * of internal rep.  If none exists, return "none".
	 */

        if (objc != 3) {
            goto wrongNumArgs;
        }
	if (objv[2]->typePtr == NULL) {
	    Tcl_SetObjResult(interp, Tcl_NewStringObj("none", -1));
	} else {
	    typeName = objv[2]->typePtr->name;
	    Tcl_SetObjResult(interp, Tcl_NewStringObj(typeName, -1));
	}
    } else if (strcmp(subCmd, "refcount") == 0) {
	char buf[TCL_INTEGER_SPACE];

        if (objc != 3) {
            goto wrongNumArgs;
        }
        index = Tcl_GetString(objv[2]);
        if (GetVariableIndex(interp, index, &varIndex) != TCL_OK) {
            return TCL_ERROR;
        }
        if (CheckIfVarUnset(interp, varIndex)) {
	    return TCL_ERROR;
	}
	TclFormatInt(buf, varPtr[varIndex]->refCount);
        Tcl_SetResult(interp, buf, TCL_VOLATILE);
    } else if (strcmp(subCmd, "type") == 0) {
        if (objc != 3) {
            goto wrongNumArgs;
        }
        index = Tcl_GetString(objv[2]);
        if (GetVariableIndex(interp, index, &varIndex) != TCL_OK) {
            return TCL_ERROR;
        }
        if (CheckIfVarUnset(interp, varIndex)) {
	    return TCL_ERROR;
	}
        if (varPtr[varIndex]->typePtr == NULL) { /* a string! */
	    Tcl_AppendToObj(Tcl_GetObjResult(interp), "string", -1);
        } else {
            Tcl_AppendToObj(Tcl_GetObjResult(interp),
                    varPtr[varIndex]->typePtr->name, -1);
        }
    } else if (strcmp(subCmd, "types") == 0) {
        if (objc != 2) {
            goto wrongNumArgs;
        }
	if (Tcl_AppendAllObjTypes(interp,
		Tcl_GetObjResult(interp)) != TCL_OK) {
	    return TCL_ERROR;
	}
    } else {
	Tcl_AppendStringsToObj(Tcl_GetObjResult(interp),
		"bad option \"", Tcl_GetString(objv[1]),
		"\": must be assign, convert, duplicate, freeallvars, "
		"newobj, objcount, objtype, refcount, type, or types", NULL);
	return TCL_ERROR;
    }
    return TCL_OK;
}

/*
 *----------------------------------------------------------------------
 *
 * TeststringobjCmd --
 *
 *	This function implements the "teststringobj" command. It is used to
 *	test the string Tcl object type implementation.
 *
 * Results:
 *	A standard Tcl object result.
 *
 * Side effects:
 *	Creates and frees string objects, and also converts objects to
 *	have string type.
 *
 *----------------------------------------------------------------------
 */

static int
TeststringobjCmd(
    ClientData clientData,	/* Not used. */
    Tcl_Interp *interp,		/* Current interpreter. */
    int objc,			/* Number of arguments. */
    Tcl_Obj *const objv[])	/* Argument objects. */
{
    int varIndex, option, i, length;
#define MAX_STRINGS 11
    char *index, *string, *strings[MAX_STRINGS+1];
    TestString *strPtr;
    static const char *options[] = {
	"append", "appendstrings", "get", "get2", "length", "length2",
	"set", "set2", "setlength", "ualloc", "getunicode", NULL
    };

    if (objc < 3) {
	wrongNumArgs:
	Tcl_WrongNumArgs(interp, 1, objv, "option arg ?arg ...?");
	return TCL_ERROR;
    }

    index = Tcl_GetString(objv[2]);
    if (GetVariableIndex(interp, index, &varIndex) != TCL_OK) {
	return TCL_ERROR;
    }

    if (Tcl_GetIndexFromObj(interp, objv[1], options, "option", 0, &option)
	    != TCL_OK) {
	return TCL_ERROR;
    }
    switch (option) {
	case 0:				/* append */
	    if (objc != 5) {
		goto wrongNumArgs;
	    }
	    if (Tcl_GetIntFromObj(interp, objv[4], &length) != TCL_OK) {
		return TCL_ERROR;
	    }
	    if (varPtr[varIndex] == NULL) {
		SetVarToObj(varIndex, Tcl_NewObj());
	    }

	    /*
	     * If the object bound to variable "varIndex" is shared, we must
	     * "copy on write" and append to a copy of the object.
	     */

	    if (Tcl_IsShared(varPtr[varIndex])) {
		SetVarToObj(varIndex, Tcl_DuplicateObj(varPtr[varIndex]));
	    }
	    string = Tcl_GetString(objv[3]);
	    Tcl_AppendToObj(varPtr[varIndex], string, length);
	    Tcl_SetObjResult(interp, varPtr[varIndex]);
	    break;
	case 1:				/* appendstrings */
	    if (objc > (MAX_STRINGS+3)) {
		goto wrongNumArgs;
	    }
	    if (varPtr[varIndex] == NULL) {
		SetVarToObj(varIndex, Tcl_NewObj());
	    }

	    /*
	     * If the object bound to variable "varIndex" is shared, we must
	     * "copy on write" and append to a copy of the object.
	     */

	    if (Tcl_IsShared(varPtr[varIndex])) {
		SetVarToObj(varIndex, Tcl_DuplicateObj(varPtr[varIndex]));
	    }
	    for (i = 3;  i < objc;  i++) {
		strings[i-3] = Tcl_GetString(objv[i]);
	    }
	    for ( ; i < 12 + 3; i++) {
		strings[i - 3] = NULL;
	    }
	    Tcl_AppendStringsToObj(varPtr[varIndex], strings[0], strings[1],
		    strings[2], strings[3], strings[4], strings[5],
		    strings[6], strings[7], strings[8], strings[9],
		    strings[10], strings[11]);
	    Tcl_SetObjResult(interp, varPtr[varIndex]);
	    break;
	case 2:				/* get */
	    if (objc != 3) {
		goto wrongNumArgs;
	    }
	    if (CheckIfVarUnset(interp, varIndex)) {
		return TCL_ERROR;
	    }
	    Tcl_SetObjResult(interp, varPtr[varIndex]);
	    break;
	case 3:				/* get2 */
	    if (objc != 3) {
		goto wrongNumArgs;
	    }
	    if (CheckIfVarUnset(interp, varIndex)) {
		return TCL_ERROR;
	    }
	    string = Tcl_GetString(varPtr[varIndex]);
	    Tcl_AppendToObj(Tcl_GetObjResult(interp), string, -1);
	    break;
	case 4:				/* length */
	    if (objc != 3) {
		goto wrongNumArgs;
	    }
	    Tcl_SetIntObj(Tcl_GetObjResult(interp), (varPtr[varIndex] != NULL)
		    ? varPtr[varIndex]->length : -1);
	    break;
	case 5:				/* length2 */
	    if (objc != 3) {
		goto wrongNumArgs;
	    }
	    if (varPtr[varIndex] != NULL) {
		strPtr = (TestString *)
		    (varPtr[varIndex])->internalRep.otherValuePtr;
		length = (int) strPtr->allocated;
	    } else {
		length = -1;
	    }
	    Tcl_SetIntObj(Tcl_GetObjResult(interp), length);
	    break;
	case 6:				/* set */
	    if (objc != 4) {
		goto wrongNumArgs;
	    }

	    /*
	     * If the object currently bound to the variable with index
	     * varIndex has ref count 1 (i.e. the object is unshared) we can
	     * modify that object directly. Otherwise, if RC>1 (i.e. the
	     * object is shared), we must create a new object to modify/set
	     * and decrement the old formerly-shared object's ref count. This
	     * is "copy on write".
	     */

	    string = Tcl_GetStringFromObj(objv[3], &length);
	    if ((varPtr[varIndex] != NULL)
		    && !Tcl_IsShared(varPtr[varIndex])) {
		Tcl_SetStringObj(varPtr[varIndex], string, length);
	    } else {
		SetVarToObj(varIndex, Tcl_NewStringObj(string, length));
	    }
	    Tcl_SetObjResult(interp, varPtr[varIndex]);
	    break;
	case 7:				/* set2 */
	    if (objc != 4) {
		goto wrongNumArgs;
	    }
	    SetVarToObj(varIndex, objv[3]);
	    break;
	case 8:				/* setlength */
	    if (objc != 4) {
		goto wrongNumArgs;
	    }
	    if (Tcl_GetIntFromObj(interp, objv[3], &length) != TCL_OK) {
		return TCL_ERROR;
	    }
	    if (varPtr[varIndex] != NULL) {
		Tcl_SetObjLength(varPtr[varIndex], length);
	    }
	    break;
	case 9:				/* ualloc */
	    if (objc != 3) {
		goto wrongNumArgs;
	    }
	    if (varPtr[varIndex] != NULL) {
		strPtr = (TestString *)
		    (varPtr[varIndex])->internalRep.otherValuePtr;
		length = (int) strPtr->uallocated;
	    } else {
		length = -1;
	    }
	    Tcl_SetIntObj(Tcl_GetObjResult(interp), length);
	    break;
	case 10:			/* getunicode */
	    if (objc != 3) {
		goto wrongNumArgs;
	    }
	    Tcl_GetUnicodeFromObj(varPtr[varIndex], NULL);
	    break;
    }

    return TCL_OK;
}

/*
 *----------------------------------------------------------------------
 *
 * SetVarToObj --
 *
 *	Utility routine to assign a Tcl_Obj* to a test variable. The
 *	Tcl_Obj* can be NULL.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	This routine handles ref counting details for assignment: i.e. the old
 *	value's ref count must be decremented (if not NULL) and the new one
 *	incremented (also if not NULL).
 *
 *----------------------------------------------------------------------
 */

static void
SetVarToObj(
    int varIndex,		/* Designates the assignment variable. */
    Tcl_Obj *objPtr)		/* Points to object to assign to var. */
{
    if (varPtr[varIndex] != NULL) {
	Tcl_DecrRefCount(varPtr[varIndex]);
    }
    varPtr[varIndex] = objPtr;
    if (objPtr != NULL) {
	Tcl_IncrRefCount(objPtr);
    }
}

/*
 *----------------------------------------------------------------------
 *
 * GetVariableIndex --
 *
 *	Utility routine to get a test variable index from the command line.
 *
 * Results:
 *	A standard Tcl object result.
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */

static int
GetVariableIndex(
    Tcl_Interp *interp,		/* Interpreter for error reporting. */
    char *string,		/* String containing a variable index
				 * specified as a nonnegative number less than
				 * NUMBER_OF_OBJECT_VARS. */
    int *indexPtr)		/* Place to store converted result. */
{
    int index;

    if (Tcl_GetInt(interp, string, &index) != TCL_OK) {
	return TCL_ERROR;
    }
    if (index < 0 || index >= NUMBER_OF_OBJECT_VARS) {
	Tcl_ResetResult(interp);
	Tcl_AppendToObj(Tcl_GetObjResult(interp), "bad variable index", -1);
	return TCL_ERROR;
    }

    *indexPtr = index;
    return TCL_OK;
}

/*
 *----------------------------------------------------------------------
 *
 * CheckIfVarUnset --
 *
 *	Utility function that checks whether a test variable is readable:
 *	i.e., that varPtr[varIndex] is non-NULL.
 *
 * Results:
 *	1 if the test variable is unset (NULL); 0 otherwise.
 *
 * Side effects:
 *	Sets the interpreter result to an error message if the variable is
 *	unset (NULL).
 *
 *----------------------------------------------------------------------
 */

static int
CheckIfVarUnset(
    Tcl_Interp *interp,		/* Interpreter for error reporting. */
    int varIndex)		/* Index of the test variable to check. */
{
    if (varPtr[varIndex] == NULL) {
	char buf[32 + TCL_INTEGER_SPACE];

	sprintf(buf, "variable %d is unset (NULL)", varIndex);
	Tcl_ResetResult(interp);
	Tcl_AppendToObj(Tcl_GetObjResult(interp), buf, -1);
	return 1;
    }
    return 0;
}

/*
 * Local Variables:
 * mode: c
 * c-basic-offset: 4
 * fill-column: 78
 * End:
 */
