/*
 * tclCompCmds.c --
 *
 *	This file contains compilation procedures that compile various Tcl
 *	commands into a sequence of instructions ("bytecodes").
 *
 * Copyright (c) 1997-1998 Sun Microsystems, Inc.
 * Copyright (c) 2001 by Kevin B. Kenny.  All rights reserved.
 * Copyright (c) 2002 ActiveState Corporation.
 * Copyright (c) 2004-2006 by Donal K. Fellows.
 *
 * See the file "license.terms" for information on usage and redistribution of
 * this file, and for a DISCLAIMER OF ALL WARRANTIES.
 *
 * RCS: @(#) $Id: tclCompCmds.c,v 1.143.2.1 2008/05/07 10:39:38 dkf Exp $
 */

#include "tclInt.h"
#include "tclCompile.h"

/*
 * Macro that encapsulates an efficiency trick that avoids a function call for
 * the simplest of compiles. The ANSI C "prototype" for this macro is:
 *
 * static void		CompileWord(CompileEnv *envPtr, Tcl_Token *tokenPtr,
 *			    Tcl_Interp *interp, int word);
 */

#define CompileWord(envPtr, tokenPtr, interp, word) \
    if ((tokenPtr)->type == TCL_TOKEN_SIMPLE_WORD) { \
	TclEmitPush(TclRegisterNewLiteral((envPtr), (tokenPtr)[1].start, \
		(tokenPtr)[1].size), (envPtr)); \
    } else { \
        envPtr->line = mapPtr->loc[eclIndex].line[word]; \
	TclCompileTokens((interp), (tokenPtr)+1, (tokenPtr)->numComponents, \
		(envPtr)); \
    }

/*
 * TIP #280: Remember the per-word line information of the current command. An
 * index is used instead of a pointer as recursive compilation may reallocate,
 * i.e. move, the array. This is also the reason to save the nuloc now, it may
 * change during the course of the function.
 *
 * Macro to encapsulate the variable definition and setup.
 */

#define DefineLineInformation \
    ExtCmdLoc *mapPtr = envPtr->extCmdMapPtr; \
    int eclIndex = mapPtr->nuloc - 1

/*
 * Convenience macro for use when compiling bodies of commands. The ANSI C
 * "prototype" for this macro is:
 *
 * static void		CompileBody(CompileEnv *envPtr, Tcl_Token *tokenPtr,
 *			    Tcl_Interp *interp);
 */

#define CompileBody(envPtr, tokenPtr, interp) \
    TclCompileCmdWord((interp), (tokenPtr)+1, (tokenPtr)->numComponents, \
	    (envPtr))

/*
 * Convenience macro for use when compiling tokens to be pushed. The ANSI C
 * "prototype" for this macro is:
 *
 * static void		CompileTokens(CompileEnv *envPtr, Tcl_Token *tokenPtr,
 *			    Tcl_Interp *interp);
 */

#define CompileTokens(envPtr, tokenPtr, interp) \
    TclCompileTokens((interp), (tokenPtr)+1, (tokenPtr)->numComponents, \
            (envPtr));
/*
 * Convenience macro for use when pushing literals. The ANSI C "prototype" for
 * this macro is:
 *
 * static void		PushLiteral(CompileEnv *envPtr,
 *			    const char *string, int length);
 */

#define PushLiteral(envPtr, string, length) \
    TclEmitPush(TclRegisterNewLiteral((envPtr), (string), (length)), (envPtr))

/*
 * Macro to advance to the next token; it is more mnemonic than the address
 * arithmetic that it replaces. The ANSI C "prototype" for this macro is:
 *
 * static Tcl_Token *	TokenAfter(Tcl_Token *tokenPtr);
 */

#define TokenAfter(tokenPtr) \
    ((tokenPtr) + ((tokenPtr)->numComponents + 1))

/*
 * Macro to get the offset to the next instruction to be issued. The ANSI C
 * "prototype" for this macro is:
 *
 * static int	CurrentOffset(CompileEnv *envPtr);
 */

#define CurrentOffset(envPtr) \
    ((envPtr)->codeNext - (envPtr)->codeStart)

/*
 * Note: the exceptDepth is a bit of a misnomer: TEBC only needs the
 * maximal depth of nested CATCH ranges in order to alloc runtime
 * memory. These macros should compute precisely that? OTOH, the nesting depth
 * of LOOP ranges is an interesting datum for debugging purposes, and that is
 * what we compute now.
 *
 * static int	DeclareExceptionRange(CompileEnv *envPtr, int type);
 * static int	ExceptionRangeStarts(CompileEnv *envPtr, int index);
 * static void	ExceptionRangeEnds(CompileEnv *envPtr, int index);
 * static void	ExceptionRangeTarget(CompileEnv *envPtr, int index, LABEL);
 */

#define DeclareExceptionRange(envPtr, type) \
    (TclCreateExceptRange((type), (envPtr)))
#define ExceptionRangeStarts(envPtr, index) \
    (((envPtr)->exceptDepth++), \
    ((envPtr)->maxExceptDepth = \
	    TclMax((envPtr)->exceptDepth, (envPtr)->maxExceptDepth)), \
    ((envPtr)->exceptArrayPtr[(index)].codeOffset = CurrentOffset(envPtr)))
#define ExceptionRangeEnds(envPtr, index) \
    (((envPtr)->exceptDepth--), \
    ((envPtr)->exceptArrayPtr[(index)].numCodeBytes = \
	CurrentOffset(envPtr) - (envPtr)->exceptArrayPtr[(index)].codeOffset))
#define ExceptionRangeTarget(envPtr, index, targetType) \
    ((envPtr)->exceptArrayPtr[(index)].targetType = CurrentOffset(envPtr))

/*
 * Prototypes for procedures defined later in this file:
 */

static ClientData	DupDictUpdateInfo(ClientData clientData);
static void		FreeDictUpdateInfo(ClientData clientData);
static void		PrintDictUpdateInfo(ClientData clientData,
			    Tcl_Obj *appendObj, ByteCode *codePtr,
			    unsigned int pcOffset);
static ClientData	DupForeachInfo(ClientData clientData);
static void		FreeForeachInfo(ClientData clientData);
static void		PrintForeachInfo(ClientData clientData,
			    Tcl_Obj *appendObj, ByteCode *codePtr,
			    unsigned int pcOffset);
static ClientData	DupJumptableInfo(ClientData clientData);
static void		FreeJumptableInfo(ClientData clientData);
static void		PrintJumptableInfo(ClientData clientData,
			    Tcl_Obj *appendObj, ByteCode *codePtr,
			    unsigned int pcOffset);
static int		PushVarName(Tcl_Interp *interp,
			    Tcl_Token *varTokenPtr, CompileEnv *envPtr,
			    int flags, int *localIndexPtr,
			    int *simpleVarNamePtr, int *isScalarPtr, int line);
static int		CompileAssociativeBinaryOpCmd(Tcl_Interp *interp,
			    Tcl_Parse *parsePtr, const char *identity,
			    int instruction, CompileEnv *envPtr);
static int		CompileComparisonOpCmd(Tcl_Interp *interp,
			    Tcl_Parse *parsePtr, int instruction,
			    CompileEnv *envPtr);
static int		CompileStrictlyBinaryOpCmd(Tcl_Interp *interp,
			    Tcl_Parse *parsePtr, int instruction,
			    CompileEnv *envPtr);
static int		CompileUnaryOpCmd(Tcl_Interp *interp,
			    Tcl_Parse *parsePtr, int instruction,
			    CompileEnv *envPtr);
static void		CompileReturnInternal(CompileEnv *envPtr,
			    unsigned char op, int code, int level,
			    Tcl_Obj *returnOpts);

/*
 * Flags bits used by PushVarName.
 */

#define TCL_CREATE_VAR     1	/* Create a compiled local if none is found */
#define TCL_NO_LARGE_INDEX 2	/* Do not return localIndex value > 255 */

/*
 * The structures below define the AuxData types defined in this file.
 */

AuxDataType tclForeachInfoType = {
    "ForeachInfo",		/* name */
    DupForeachInfo,		/* dupProc */
    FreeForeachInfo,		/* freeProc */
    PrintForeachInfo		/* printProc */
};

AuxDataType tclJumptableInfoType = {
    "JumptableInfo",		/* name */
    DupJumptableInfo,		/* dupProc */
    FreeJumptableInfo,		/* freeProc */
    PrintJumptableInfo		/* printProc */
};

AuxDataType tclDictUpdateInfoType = {
    "DictUpdateInfo",		/* name */
    DupDictUpdateInfo,		/* dupProc */
    FreeDictUpdateInfo,		/* freeProc */
    PrintDictUpdateInfo		/* printProc */
};

/*
 *----------------------------------------------------------------------
 *
 * TclCompileAppendCmd --
 *
 *	Procedure called to compile the "append" command.
 *
 * Results:
 * 	Returns TCL_OK for a successful compile. Returns TCL_ERROR to defer
 * 	evaluation to runtime.
 *
 * Side effects:
 *	Instructions are added to envPtr to execute the "append" command at
 *	runtime.
 *
 *----------------------------------------------------------------------
 */

int
TclCompileAppendCmd(
    Tcl_Interp *interp,		/* Used for error reporting. */
    Tcl_Parse *parsePtr,	/* Points to a parse structure for the command
				 * created by Tcl_ParseCommand. */
    Command *cmdPtr,		/* Points to defintion of command being
				 * compiled. */
    CompileEnv *envPtr)		/* Holds resulting instructions. */
{
    Tcl_Token *varTokenPtr, *valueTokenPtr;
    int simpleVarName, isScalar, localIndex, numWords;
    DefineLineInformation;	/* TIP #280 */

    numWords = parsePtr->numWords;
    if (numWords == 1) {
	return TCL_ERROR;
    } else if (numWords == 2) {
	/*
	 * append varName == set varName
	 */

	return TclCompileSetCmd(interp, parsePtr, cmdPtr, envPtr);
    } else if (numWords > 3) {
	/*
	 * APPEND instructions currently only handle one value.
	 */

	return TCL_ERROR;
    }

    /*
     * Decide if we can use a frame slot for the var/array name or if we need
     * to emit code to compute and push the name at runtime. We use a frame
     * slot (entry in the array of local vars) if we are compiling a procedure
     * body and if the name is simple text that does not include namespace
     * qualifiers.
     */

    varTokenPtr = TokenAfter(parsePtr->tokenPtr);

    PushVarName(interp, varTokenPtr, envPtr, TCL_CREATE_VAR,
		&localIndex, &simpleVarName, &isScalar,
		mapPtr->loc[eclIndex].line[1]);

    /*
     * We are doing an assignment, otherwise TclCompileSetCmd was called, so
     * push the new value. This will need to be extended to push a value for
     * each argument.
     */

    if (numWords > 2) {
	valueTokenPtr = TokenAfter(varTokenPtr);
	CompileWord(envPtr, valueTokenPtr, interp, 2);
    }

    /*
     * Emit instructions to set/get the variable.
     */

    if (simpleVarName) {
	if (isScalar) {
	    if (localIndex < 0) {
		TclEmitOpcode(INST_APPEND_STK, envPtr);
	    } else if (localIndex <= 255) {
		TclEmitInstInt1(INST_APPEND_SCALAR1, localIndex, envPtr);
	    } else {
		TclEmitInstInt4(INST_APPEND_SCALAR4, localIndex, envPtr);
	    }
	} else {
	    if (localIndex < 0) {
		TclEmitOpcode(INST_APPEND_ARRAY_STK, envPtr);
	    } else if (localIndex <= 255) {
		TclEmitInstInt1(INST_APPEND_ARRAY1, localIndex, envPtr);
	    } else {
		TclEmitInstInt4(INST_APPEND_ARRAY4, localIndex, envPtr);
	    }
	}
    } else {
	TclEmitOpcode(INST_APPEND_STK, envPtr);
    }

    return TCL_OK;
}

/*
 *----------------------------------------------------------------------
 *
 * TclCompileBreakCmd --
 *
 *	Procedure called to compile the "break" command.
 *
 * Results:
 * 	Returns TCL_OK for a successful compile. Returns TCL_ERROR to defer
 * 	evaluation to runtime.
 *
 * Side effects:
 *	Instructions are added to envPtr to execute the "break" command at
 *	runtime.
 *
 *----------------------------------------------------------------------
 */

int
TclCompileBreakCmd(
    Tcl_Interp *interp,		/* Used for error reporting. */
    Tcl_Parse *parsePtr,	/* Points to a parse structure for the command
				 * created by Tcl_ParseCommand. */
    Command *cmdPtr,		/* Points to defintion of command being
				 * compiled. */
    CompileEnv *envPtr)		/* Holds resulting instructions. */
{
    if (parsePtr->numWords != 1) {
	return TCL_ERROR;
    }

    /*
     * Emit a break instruction.
     */

    TclEmitOpcode(INST_BREAK, envPtr);
    return TCL_OK;
}

/*
 *----------------------------------------------------------------------
 *
 * TclCompileCatchCmd --
 *
 *	Procedure called to compile the "catch" command.
 *
 * Results:
 * 	Returns TCL_OK for a successful compile. Returns TCL_ERROR to defer
 * 	evaluation to runtime.
 *
 * Side effects:
 *	Instructions are added to envPtr to execute the "catch" command at
 *	runtime.
 *
 *----------------------------------------------------------------------
 */

int
TclCompileCatchCmd(
    Tcl_Interp *interp,		/* Used for error reporting. */
    Tcl_Parse *parsePtr,	/* Points to a parse structure for the command
				 * created by Tcl_ParseCommand. */
    Command *cmdPtr,		/* Points to defintion of command being
				 * compiled. */
    CompileEnv *envPtr)		/* Holds resulting instructions. */
{
    JumpFixup jumpFixup;
    Tcl_Token *cmdTokenPtr, *resultNameTokenPtr, *optsNameTokenPtr;
    const char *name;
    int resultIndex, optsIndex, nameChars, range;
    int savedStackDepth = envPtr->currStackDepth;
    DefineLineInformation;	/* TIP #280 */

    /*
     * If syntax does not match what we expect for [catch], do not compile.
     * Let runtime checks determine if syntax has changed.
     */

    if ((parsePtr->numWords < 2) || (parsePtr->numWords > 4)) {
	return TCL_ERROR;
    }

    /*
     * If variables were specified and the catch command is at global level
     * (not in a procedure), don't compile it inline: the payoff is too small.
     */

    if ((parsePtr->numWords >= 3) && (envPtr->procPtr == NULL)) {
	return TCL_ERROR;
    }

    /*
     * Make sure the variable names, if any, have no substitutions and just
     * refer to local scalars.
     */

    resultIndex = optsIndex = -1;
    cmdTokenPtr = TokenAfter(parsePtr->tokenPtr);
    if (parsePtr->numWords >= 3) {
	resultNameTokenPtr = TokenAfter(cmdTokenPtr);
	/* DGP */
	if (resultNameTokenPtr->type != TCL_TOKEN_SIMPLE_WORD) {
	    return TCL_ERROR;
	}

	name = resultNameTokenPtr[1].start;
	nameChars = resultNameTokenPtr[1].size;
	if (!TclIsLocalScalar(name, nameChars)) {
	    return TCL_ERROR;
	}
	resultIndex = TclFindCompiledLocal(resultNameTokenPtr[1].start,
		resultNameTokenPtr[1].size, /*create*/ 1, envPtr->procPtr);

	/* DKF */
	if (parsePtr->numWords == 4) {
	    optsNameTokenPtr = TokenAfter(resultNameTokenPtr);
	    if (optsNameTokenPtr->type != TCL_TOKEN_SIMPLE_WORD) {
		return TCL_ERROR;
	    }
	    name = optsNameTokenPtr[1].start;
	    nameChars = optsNameTokenPtr[1].size;
	    if (!TclIsLocalScalar(name, nameChars)) {
		return TCL_ERROR;
	    }
	    optsIndex = TclFindCompiledLocal(optsNameTokenPtr[1].start,
		    optsNameTokenPtr[1].size, /*create*/ 1, envPtr->procPtr);
	}
    }

    /*
     * We will compile the catch command. Emit a beginCatch instruction at the
     * start of the catch body: the subcommand it controls.
     */

    range = DeclareExceptionRange(envPtr, CATCH_EXCEPTION_RANGE);
    TclEmitInstInt4(INST_BEGIN_CATCH4, range, envPtr);

    /*
     * If the body is a simple word, compile the instructions to eval it.
     * Otherwise, compile instructions to substitute its text without
     * catching, a catch instruction that resets the stack to what it was
     * before substituting the body, and then an instruction to eval the body.
     * Care has to be taken to register the correct startOffset for the catch
     * range so that errors in the substitution are not catched [Bug 219184]
     */

    envPtr->line = mapPtr->loc[eclIndex].line[1];
    if (cmdTokenPtr->type == TCL_TOKEN_SIMPLE_WORD) {
	ExceptionRangeStarts(envPtr, range);
	CompileBody(envPtr, cmdTokenPtr, interp);
	ExceptionRangeEnds(envPtr, range);
    } else {
	CompileTokens(envPtr, cmdTokenPtr, interp);
	ExceptionRangeStarts(envPtr, range);
	TclEmitOpcode(INST_EVAL_STK, envPtr);
	ExceptionRangeEnds(envPtr, range);
    }

    /*
     * The "no errors" epilogue code: store the body's result into the
     * variable (if any), push "0" (TCL_OK) as the catch's "no error" result,
     * and jump around the "error case" code. Note that we issue the push of
     * the return options first so that if alterations happen to the current
     * interpreter state during the writing of the variable, we won't see
     * them; this results in a slightly complex instruction issuing flow
     * (can't exchange, only duplicate and pop).
     */

    if (resultIndex != -1) {
	if (optsIndex != -1) {
	    TclEmitOpcode(INST_PUSH_RETURN_OPTIONS, envPtr);
	    TclEmitInstInt4(INST_OVER, 1, envPtr);
	}
	if (resultIndex <= 255) {
	    TclEmitInstInt1(INST_STORE_SCALAR1, resultIndex, envPtr);
	} else {
	    TclEmitInstInt4(INST_STORE_SCALAR4, resultIndex, envPtr);
	}
	if (optsIndex != -1) {
	    TclEmitOpcode(INST_POP, envPtr);
	    if (optsIndex <= 255) {
		TclEmitInstInt1(INST_STORE_SCALAR1, optsIndex, envPtr);
	    } else {
		TclEmitInstInt4(INST_STORE_SCALAR4, optsIndex, envPtr);
	    }
	    TclEmitOpcode(INST_POP, envPtr);
	}
    }
    TclEmitOpcode(INST_POP, envPtr);
    PushLiteral(envPtr, "0", 1);
    TclEmitForwardJump(envPtr, TCL_UNCONDITIONAL_JUMP, &jumpFixup);

    /*
     * The "error case" code: store the body's result into the variable (if
     * any), then push the error result code. The initial PC offset here is
     * the catch's error target. Note that if we are saving the return
     * options, we do that first so the preservation cannot get affected by
     * any intermediate result handling.
     */

    envPtr->currStackDepth = savedStackDepth;
    ExceptionRangeTarget(envPtr, range, catchOffset);
    if (resultIndex != -1) {
	if (optsIndex != -1) {
	    TclEmitOpcode(INST_PUSH_RETURN_OPTIONS, envPtr);
	}
	TclEmitOpcode(INST_PUSH_RESULT, envPtr);
	if (resultIndex <= 255) {
	    TclEmitInstInt1(INST_STORE_SCALAR1, resultIndex, envPtr);
	} else {
	    TclEmitInstInt4(INST_STORE_SCALAR4, resultIndex, envPtr);
	}
	TclEmitOpcode(INST_POP, envPtr);
	if (optsIndex != -1) {
	    if (optsIndex <= 255) {
		TclEmitInstInt1(INST_STORE_SCALAR1, optsIndex, envPtr);
	    } else {
		TclEmitInstInt4(INST_STORE_SCALAR4, optsIndex, envPtr);
	    }
	    TclEmitOpcode(INST_POP, envPtr);
	}
    }
    TclEmitOpcode(INST_PUSH_RETURN_CODE, envPtr);

    /*
     * Update the target of the jump after the "no errors" code, then emit an
     * endCatch instruction at the end of the catch command.
     */

    if (TclFixupForwardJumpToHere(envPtr, &jumpFixup, 127)) {
	Tcl_Panic("TclCompileCatchCmd: bad jump distance %d",
		CurrentOffset(envPtr) - jumpFixup.codeOffset);
    }
    TclEmitOpcode(INST_END_CATCH, envPtr);

    envPtr->currStackDepth = savedStackDepth + 1;
    return TCL_OK;
}

/*
 *----------------------------------------------------------------------
 *
 * TclCompileContinueCmd --
 *
 *	Procedure called to compile the "continue" command.
 *
 * Results:
 * 	Returns TCL_OK for a successful compile. Returns TCL_ERROR to defer
 * 	evaluation to runtime.
 *
 * Side effects:
 *	Instructions are added to envPtr to execute the "continue" command at
 *	runtime.
 *
 *----------------------------------------------------------------------
 */

int
TclCompileContinueCmd(
    Tcl_Interp *interp,		/* Used for error reporting. */
    Tcl_Parse *parsePtr,	/* Points to a parse structure for the command
				 * created by Tcl_ParseCommand. */
    Command *cmdPtr,		/* Points to defintion of command being
				 * compiled. */
    CompileEnv *envPtr)		/* Holds resulting instructions. */
{
    /*
     * There should be no argument after the "continue".
     */

    if (parsePtr->numWords != 1) {
	return TCL_ERROR;
    }

    /*
     * Emit a continue instruction.
     */

    TclEmitOpcode(INST_CONTINUE, envPtr);
    return TCL_OK;
}

/*
 *----------------------------------------------------------------------
 *
 * TclCompileDict*Cmd --
 *
 *	Functions called to compile "dict" sucommands.
 *
 * Results:
 * 	All return TCL_OK for a successful compile, and TCL_ERROR to defer
 * 	evaluation to runtime.
 *
 * Side effects:
 *	Instructions are added to envPtr to execute the "dict" subcommand at
 *	runtime.
 *
 * Notes:
 *	The following commands are in fairly common use and are possibly worth
 *	bytecoding:
 *		dict append
 *		dict create	[*]
 *		dict exists	[*]
 *		dict for
 *		dict get	[*]
 *		dict incr
 *		dict keys	[*]
 *		dict lappend
 *		dict set
 *		dict unset
 *
 *	In practice, those that are pure-value operators (marked with [*]) can
 *	probably be left alone (except perhaps [dict get] which is very very
 *	common) and [dict update] should be considered instead (really big
 *	win!)
 *
 *----------------------------------------------------------------------
 */

int
TclCompileDictSetCmd(
    Tcl_Interp *interp,		/* Used for looking up stuff. */
    Tcl_Parse *parsePtr,	/* Points to a parse structure for the command
				 * created by Tcl_ParseCommand. */
    Command *cmdPtr,		/* Points to defintion of command being
				 * compiled. */
    CompileEnv *envPtr)		/* Holds resulting instructions. */
{
    Tcl_Token *tokenPtr;
    int numWords, i;
    Proc *procPtr = envPtr->procPtr;
    DefineLineInformation;	/* TIP #280 */
    Tcl_Token *varTokenPtr;
    int dictVarIndex, nameChars;
    const char *name;

    /*
     * There must be at least one argument after the command.
     */

    if (parsePtr->numWords < 4 || procPtr == NULL) {
	return TCL_ERROR;
    }

    /*
     * The dictionary variable must be a local scalar that is knowable at
     * compile time; anything else exceeds the complexity of the opcode. So
     * discover what the index is.
     */

    varTokenPtr = TokenAfter(parsePtr->tokenPtr);
    if (varTokenPtr->type != TCL_TOKEN_SIMPLE_WORD) {
	return TCL_ERROR;
    }
    name = varTokenPtr[1].start;
    nameChars = varTokenPtr[1].size;
    if (!TclIsLocalScalar(name, nameChars)) {
	return TCL_ERROR;
    }
    dictVarIndex = TclFindCompiledLocal(name, nameChars, 1, procPtr);

    /*
     * Remaining words (key path and value to set) can be handled normally.
     */

    tokenPtr = TokenAfter(varTokenPtr);
    numWords = parsePtr->numWords-1;
    for (i=1 ; i<numWords ; i++) {
	CompileWord(envPtr, tokenPtr, interp, i);
	tokenPtr = TokenAfter(tokenPtr);
    }

    /*
     * Now emit the instruction to do the dict manipulation.
     */

    TclEmitInstInt4( INST_DICT_SET, numWords-2,		envPtr);
    TclEmitInt4(     dictVarIndex,			envPtr);
    return TCL_OK;
}

int
TclCompileDictIncrCmd(
    Tcl_Interp *interp,		/* Used for looking up stuff. */
    Tcl_Parse *parsePtr,	/* Points to a parse structure for the command
				 * created by Tcl_ParseCommand. */
    Command *cmdPtr,		/* Points to defintion of command being
				 * compiled. */
    CompileEnv *envPtr)		/* Holds resulting instructions. */
{
    Proc *procPtr = envPtr->procPtr;
    DefineLineInformation;	/* TIP #280 */
    Tcl_Token *varTokenPtr, *keyTokenPtr;
    int dictVarIndex, nameChars, incrAmount;
    const char *name;

    /*
     * There must be at least two arguments after the command.
     */

    if (parsePtr->numWords < 3 || parsePtr->numWords > 4 || procPtr == NULL) {
	return TCL_ERROR;
    }
    varTokenPtr = TokenAfter(parsePtr->tokenPtr);
    keyTokenPtr = TokenAfter(varTokenPtr);

    /*
     * Parse the increment amount, if present.
     */

    if (parsePtr->numWords == 4) {
	const char *word;
	int numBytes, code;
	Tcl_Token *incrTokenPtr;
	Tcl_Obj *intObj;

	incrTokenPtr = TokenAfter(keyTokenPtr);
	if (incrTokenPtr->type != TCL_TOKEN_SIMPLE_WORD) {
	    return TCL_ERROR;
	}
	word = incrTokenPtr[1].start;
	numBytes = incrTokenPtr[1].size;

	intObj = Tcl_NewStringObj(word, numBytes);
	Tcl_IncrRefCount(intObj);
	code = TclGetIntFromObj(NULL, intObj, &incrAmount);
	TclDecrRefCount(intObj);
	if (code != TCL_OK) {
	    return TCL_ERROR;
	}
    } else {
	incrAmount = 1;
    }

    /*
     * The dictionary variable must be a local scalar that is knowable at
     * compile time; anything else exceeds the complexity of the opcode. So
     * discover what the index is.
     */

    if (varTokenPtr->type != TCL_TOKEN_SIMPLE_WORD) {
	return TCL_ERROR;
    }
    name = varTokenPtr[1].start;
    nameChars = varTokenPtr[1].size;
    if (!TclIsLocalScalar(name, nameChars)) {
	return TCL_ERROR;
    }
    dictVarIndex = TclFindCompiledLocal(name, nameChars, 1, procPtr);

    /*
     * Emit the key and the code to actually do the increment.
     */

    CompileWord(envPtr, keyTokenPtr, interp, 3);
    TclEmitInstInt4( INST_DICT_INCR_IMM, incrAmount,	envPtr);
    TclEmitInt4(     dictVarIndex,			envPtr);
    return TCL_OK;
}

int
TclCompileDictGetCmd(
    Tcl_Interp *interp,		/* Used for looking up stuff. */
    Tcl_Parse *parsePtr,	/* Points to a parse structure for the command
				 * created by Tcl_ParseCommand. */
    Command *cmdPtr,		/* Points to defintion of command being
				 * compiled. */
    CompileEnv *envPtr)		/* Holds resulting instructions. */
{
    Tcl_Token *tokenPtr;
    int numWords, i;
    DefineLineInformation;	/* TIP #280 */

    /*
     * There must be at least two arguments after the command (the single-arg
     * case is legal, but too special and magic for us to deal with here).
     */

    if (parsePtr->numWords < 3) {
	return TCL_ERROR;
    }
    tokenPtr = TokenAfter(parsePtr->tokenPtr);
    numWords = parsePtr->numWords-1;

    /*
     * Only compile this because we need INST_DICT_GET anyway.
     */

    for (i=0 ; i<numWords ; i++) {
	CompileWord(envPtr, tokenPtr, interp, i);
	tokenPtr = TokenAfter(tokenPtr);
    }
    TclEmitInstInt4(INST_DICT_GET, numWords-1, envPtr);
    return TCL_OK;
}

int
TclCompileDictForCmd(
    Tcl_Interp *interp,		/* Used for looking up stuff. */
    Tcl_Parse *parsePtr,	/* Points to a parse structure for the command
				 * created by Tcl_ParseCommand. */
    Command *cmdPtr,		/* Points to defintion of command being
				 * compiled. */
    CompileEnv *envPtr)		/* Holds resulting instructions. */
{
    Proc *procPtr = envPtr->procPtr;
    DefineLineInformation;	/* TIP #280 */
    Tcl_Token *varsTokenPtr, *dictTokenPtr, *bodyTokenPtr;
    int keyVarIndex, valueVarIndex, nameChars, loopRange, catchRange;
    int infoIndex, jumpDisplacement, bodyTargetOffset, emptyTargetOffset;
    int numVars, endTargetOffset;
    int savedStackDepth = envPtr->currStackDepth;
				/* Needed because jumps confuse the stack
				 * space calculator. */
    const char **argv;
    Tcl_DString buffer;

    /*
     * There must be at least three argument after the command.
     */

    if (parsePtr->numWords != 4 || procPtr == NULL) {
	return TCL_ERROR;
    }

    varsTokenPtr = TokenAfter(parsePtr->tokenPtr);
    dictTokenPtr = TokenAfter(varsTokenPtr);
    bodyTokenPtr = TokenAfter(dictTokenPtr);
    if (varsTokenPtr->type != TCL_TOKEN_SIMPLE_WORD ||
	    bodyTokenPtr->type != TCL_TOKEN_SIMPLE_WORD) {
	return TCL_ERROR;
    }

    /*
     * Check we've got a pair of variables and that they are local variables.
     * Then extract their indices in the LVT.
     */

    Tcl_DStringInit(&buffer);
    Tcl_DStringAppend(&buffer, varsTokenPtr[1].start, varsTokenPtr[1].size);
    if (Tcl_SplitList(NULL, Tcl_DStringValue(&buffer), &numVars,
	    &argv) != TCL_OK) {
	Tcl_DStringFree(&buffer);
	return TCL_ERROR;
    }
    Tcl_DStringFree(&buffer);
    if (numVars != 2) {
	ckfree((char *) argv);
	return TCL_ERROR;
    }

    nameChars = strlen(argv[0]);
    if (!TclIsLocalScalar(argv[0], nameChars)) {
	ckfree((char *) argv);
	return TCL_ERROR;
    }
    keyVarIndex = TclFindCompiledLocal(argv[0], nameChars, 1, procPtr);

    nameChars = strlen(argv[1]);
    if (!TclIsLocalScalar(argv[1], nameChars)) {
	ckfree((char *) argv);
	return TCL_ERROR;
    }
    valueVarIndex = TclFindCompiledLocal(argv[1], nameChars, 1, procPtr);
    ckfree((char *) argv);

    /*
     * Allocate a temporary variable to store the iterator reference. The
     * variable will contain a Tcl_DictSearch reference which will be
     * allocated by INST_DICT_FIRST and disposed when the variable is unset
     * (at which point it should also have been finished with).
     */

    infoIndex = TclFindCompiledLocal(NULL, 0, 1, procPtr);

    /*
     * Preparation complete; issue instructions. Note that this code issues
     * fixed-sized jumps. That simplifies things a lot!
     *
     * First up, get the dictionary and start the iteration. No catching of
     * errors at this point.
     */

    CompileWord(envPtr, dictTokenPtr, interp, 3);
    TclEmitInstInt4( INST_DICT_FIRST, infoIndex,		envPtr);
    emptyTargetOffset = CurrentOffset(envPtr);
    TclEmitInstInt4( INST_JUMP_TRUE4, 0,			envPtr);

    /*
     * Now we catch errors from here on so that we can finalize the search
     * started by Tcl_DictObjFirst above.
     */

    catchRange = DeclareExceptionRange(envPtr, CATCH_EXCEPTION_RANGE);
    TclEmitInstInt4( INST_BEGIN_CATCH4, catchRange,		envPtr);
    ExceptionRangeStarts(envPtr, catchRange);

    /*
     * Inside the iteration, write the loop variables.
     */

    bodyTargetOffset = CurrentOffset(envPtr);
    TclEmitInstInt4( INST_STORE_SCALAR4, keyVarIndex,		envPtr);
    TclEmitOpcode(   INST_POP,					envPtr);
    TclEmitInstInt4( INST_STORE_SCALAR4, valueVarIndex,		envPtr);
    TclEmitOpcode(   INST_POP,					envPtr);

    /*
     * Set up the loop exception targets.
     */

    loopRange = DeclareExceptionRange(envPtr, LOOP_EXCEPTION_RANGE);
    ExceptionRangeStarts(envPtr, loopRange);

    /*
     * Compile the loop body itself. It should be stack-neutral.
     */

    envPtr->line = mapPtr->loc[eclIndex].line[4];
    CompileBody(envPtr, bodyTokenPtr, interp);
    TclEmitOpcode(   INST_POP,					envPtr);

    /*
     * Both exception target ranges (error and loop) end here.
     */

    ExceptionRangeEnds(envPtr, loopRange);
    ExceptionRangeEnds(envPtr, catchRange);

    /*
     * Continue (or just normally process) by getting the next pair of items
     * from the dictionary and jumping back to the code to write them into
     * variables if there is another pair.
     */

    ExceptionRangeTarget(envPtr, loopRange, continueOffset);
    TclEmitInstInt4( INST_DICT_NEXT, infoIndex,			envPtr);
    jumpDisplacement = bodyTargetOffset - CurrentOffset(envPtr);
    TclEmitInstInt4( INST_JUMP_FALSE4, jumpDisplacement,	envPtr);
    TclEmitOpcode(   INST_POP,					envPtr);
    TclEmitOpcode(   INST_POP,					envPtr);

    /*
     * Now do the final cleanup for the no-error case (this is where we break
     * out of the loop to) by force-terminating the iteration (if not already
     * terminated), ditching the exception info and jumping to the last
     * instruction for this command. In theory, this could be done using the
     * "finally" clause (next generated) but this is faster.
     */

    ExceptionRangeTarget(envPtr, loopRange, breakOffset);
    TclEmitInstInt4( INST_DICT_DONE, infoIndex,			envPtr);
    TclEmitOpcode(   INST_END_CATCH,				envPtr);
    endTargetOffset = CurrentOffset(envPtr);
    TclEmitInstInt4( INST_JUMP4, 0,				envPtr);

    /*
     * Error handler "finally" clause, which force-terminates the iteration
     * and rethrows the error.
     */

    ExceptionRangeTarget(envPtr, catchRange, catchOffset);
    TclEmitOpcode(   INST_PUSH_RETURN_OPTIONS,			envPtr);
    TclEmitOpcode(   INST_PUSH_RESULT,				envPtr);
    TclEmitInstInt4( INST_DICT_DONE, infoIndex,			envPtr);
    TclEmitOpcode(   INST_END_CATCH,				envPtr);
    TclEmitOpcode(   INST_RETURN_STK,				envPtr);

    /*
     * Otherwise we're done (the jump after the DICT_FIRST points here) and we
     * need to pop the bogus key/value pair (pushed to keep stack calculations
     * easy!) Note that we skip the END_CATCH. [Bug 1382528]
     */

    envPtr->currStackDepth = savedStackDepth+2;
    jumpDisplacement = CurrentOffset(envPtr) - emptyTargetOffset;
    TclUpdateInstInt4AtPc(INST_JUMP_TRUE4, jumpDisplacement,
	    envPtr->codeStart + emptyTargetOffset);
    TclEmitOpcode(   INST_POP,					envPtr);
    TclEmitOpcode(   INST_POP,					envPtr);
    TclEmitInstInt4( INST_DICT_DONE, infoIndex,			envPtr);

    /*
     * Final stage of the command (normal case) is that we push an empty
     * object. This is done last to promote peephole optimization when it's
     * dropped immediately.
     */

    jumpDisplacement = CurrentOffset(envPtr) - endTargetOffset;
    TclUpdateInstInt4AtPc(INST_JUMP4, jumpDisplacement,
	    envPtr->codeStart + endTargetOffset);
    PushLiteral(envPtr, "", 0);
    return TCL_OK;
}

int
TclCompileDictUpdateCmd(
    Tcl_Interp *interp,		/* Used for looking up stuff. */
    Tcl_Parse *parsePtr,	/* Points to a parse structure for the command
				 * created by Tcl_ParseCommand. */
    Command *cmdPtr,		/* Points to defintion of command being
				 * compiled. */
    CompileEnv *envPtr)		/* Holds resulting instructions. */
{
    Proc *procPtr = envPtr->procPtr;
    DefineLineInformation;	/* TIP #280 */
    const char *name;
    int i, nameChars, dictIndex, numVars, range, infoIndex;
    Tcl_Token **keyTokenPtrs, *dictVarTokenPtr, *bodyTokenPtr, *tokenPtr;
    DictUpdateInfo *duiPtr;
    JumpFixup jumpFixup;

    /*
     * There must be at least one argument after the command.
     */

    if (parsePtr->numWords < 5 || procPtr == NULL) {
	return TCL_ERROR;
    }

    /*
     * Parse the command. Expect the following:
     *   dict update <lit(eral)> <any> <lit> ?<any> <lit> ...? <lit>
     */

    if ((parsePtr->numWords - 1) & 1) {
	return TCL_ERROR;
    }
    numVars = (parsePtr->numWords - 3) / 2;

    /*
     * The dictionary variable must be a local scalar that is knowable at
     * compile time; anything else exceeds the complexity of the opcode. So
     * discover what the index is.
     */

    dictVarTokenPtr = TokenAfter(parsePtr->tokenPtr);
    if (dictVarTokenPtr->type != TCL_TOKEN_SIMPLE_WORD) {
	return TCL_ERROR;
    }
    name = dictVarTokenPtr[1].start;
    nameChars = dictVarTokenPtr[1].size;
    if (!TclIsLocalScalar(name, nameChars)) {
	return TCL_ERROR;
    }
    dictIndex = TclFindCompiledLocal(name, nameChars, 1, procPtr);

    /*
     * Assemble the instruction metadata. This is complex enough that it is
     * represented as auxData; it holds an ordered list of variable indices
     * that are to be used.
     */

    duiPtr = (DictUpdateInfo *)
	    ckalloc(sizeof(DictUpdateInfo) + sizeof(int) * (numVars - 1));
    duiPtr->length = numVars;
    keyTokenPtrs = (Tcl_Token **) TclStackAlloc(interp,
	    sizeof(Tcl_Token *) * numVars);
    tokenPtr = TokenAfter(dictVarTokenPtr);

    for (i=0 ; i<numVars ; i++) {
	/*
	 * Put keys to one side for later compilation to bytecode.
	 */

	keyTokenPtrs[i] = tokenPtr;

	/*
	 * Variables first need to be checked for sanity.
	 */

	tokenPtr = TokenAfter(tokenPtr);
	if (tokenPtr->type != TCL_TOKEN_SIMPLE_WORD) {
	    ckfree((char *) duiPtr);
	    TclStackFree(interp, keyTokenPtrs);
	    return TCL_ERROR;
	}
	name = tokenPtr[1].start;
	nameChars = tokenPtr[1].size;
	if (!TclIsLocalScalar(name, nameChars)) {
	    ckfree((char *) duiPtr);
	    TclStackFree(interp, keyTokenPtrs);
	    return TCL_ERROR;
	}

	/*
	 * Stash the index in the auxiliary data.
	 */

	duiPtr->varIndices[i] =
		TclFindCompiledLocal(name, nameChars, 1, procPtr);
	tokenPtr = TokenAfter(tokenPtr);
    }
    if (tokenPtr->type != TCL_TOKEN_SIMPLE_WORD) {
	ckfree((char *) duiPtr);
	TclStackFree(interp, keyTokenPtrs);
	return TCL_ERROR;
    }
    bodyTokenPtr = tokenPtr;

    /*
     * The list of variables to bind is stored in auxiliary data so that it
     * can't be snagged by literal sharing and forced to shimmer dangerously.
     */

    infoIndex = TclCreateAuxData(duiPtr, &tclDictUpdateInfoType, envPtr);

    for (i=0 ; i<numVars ; i++) {
	CompileWord(envPtr, keyTokenPtrs[i], interp, i);
    }
    TclEmitInstInt4( INST_LIST, numVars,			envPtr);
    TclEmitInstInt4( INST_DICT_UPDATE_START, dictIndex,		envPtr);
    TclEmitInt4(     infoIndex,					envPtr);

    range = DeclareExceptionRange(envPtr, CATCH_EXCEPTION_RANGE);
    TclEmitInstInt4( INST_BEGIN_CATCH4, range,			envPtr);

    ExceptionRangeStarts(envPtr, range);
    CompileBody(envPtr, bodyTokenPtr, interp);
    ExceptionRangeEnds(envPtr, range);

    /*
     * Normal termination code: the stack has the key list below the result of
     * the body evaluation: swap them and finish the update code.
     */

    TclEmitOpcode(   INST_END_CATCH,				envPtr);
    TclEmitInstInt4( INST_REVERSE, 2,				envPtr);
    TclEmitInstInt4( INST_DICT_UPDATE_END, dictIndex,		envPtr);
    TclEmitInt4(     infoIndex,					envPtr);

    /*
     * Jump around the exceptional termination code.
     */

    TclEmitForwardJump(envPtr, TCL_UNCONDITIONAL_JUMP, &jumpFixup);

    /*
     * Termination code for non-ok returns: stash the result and return
     * options in the stack, bring up the key list, finish the update code,
     * and finally return with the catched return data
     */

    ExceptionRangeTarget(envPtr, range, catchOffset);
    TclEmitOpcode(   INST_PUSH_RESULT,				envPtr);
    TclEmitOpcode(   INST_PUSH_RETURN_OPTIONS,			envPtr);
    TclEmitOpcode(   INST_END_CATCH,				envPtr);
    TclEmitInstInt4( INST_REVERSE, 3,				envPtr);

    TclEmitInstInt4( INST_DICT_UPDATE_END, dictIndex,		envPtr);
    TclEmitInt4(     infoIndex,					envPtr);
    TclEmitOpcode(   INST_RETURN_STK,				envPtr);

    if (TclFixupForwardJumpToHere(envPtr, &jumpFixup, 127)) {
	Tcl_Panic("TclCompileDictCmd(update): bad jump distance %d",
		CurrentOffset(envPtr) - jumpFixup.codeOffset);
    }
    TclStackFree(interp, keyTokenPtrs);
    return TCL_OK;
}

int
TclCompileDictAppendCmd(
    Tcl_Interp *interp,		/* Used for looking up stuff. */
    Tcl_Parse *parsePtr,	/* Points to a parse structure for the command
				 * created by Tcl_ParseCommand. */
    Command *cmdPtr,		/* Points to defintion of command being
				 * compiled. */
    CompileEnv *envPtr)		/* Holds resulting instructions. */
{
    Proc *procPtr = envPtr->procPtr;
    DefineLineInformation;	/* TIP #280 */
    Tcl_Token *tokenPtr;
    int i, dictVarIndex;

    /*
     * There must be at least two argument after the command. And we impose an
     * (arbirary) safe limit; anyone exceeding it should stop worrying about
     * speed quite so much. ;-)
     */

    if (parsePtr->numWords<4 || parsePtr->numWords>100 || procPtr==NULL) {
	return TCL_ERROR;
    }

    /*
     * Get the index of the local variable that we will be working with.
     */

    tokenPtr = TokenAfter(parsePtr->tokenPtr);
    if (tokenPtr->type != TCL_TOKEN_SIMPLE_WORD) {
	return TCL_ERROR;
    } else {
	register const char *name = tokenPtr[1].start;
	register int nameChars = tokenPtr[1].size;

	if (!TclIsLocalScalar(name, nameChars)) {
	    return TCL_ERROR;
	}
	dictVarIndex = TclFindCompiledLocal(name, nameChars, 1, procPtr);
    }

    /*
     * Produce the string to concatenate onto the dictionary entry.
     */

    tokenPtr = TokenAfter(tokenPtr);
    for (i=2 ; i<parsePtr->numWords ; i++) {
	CompileWord(envPtr, tokenPtr, interp, i);
	tokenPtr = TokenAfter(tokenPtr);
    }
    if (parsePtr->numWords > 4) {
	TclEmitInstInt1(INST_CONCAT1, parsePtr->numWords-3, envPtr);
    }

    /*
     * Do the concatenation.
     */

    TclEmitInstInt4(INST_DICT_APPEND, dictVarIndex, envPtr);
    return TCL_OK;
}

int
TclCompileDictLappendCmd(
    Tcl_Interp *interp,		/* Used for looking up stuff. */
    Tcl_Parse *parsePtr,	/* Points to a parse structure for the command
				 * created by Tcl_ParseCommand. */
    Command *cmdPtr,		/* Points to defintion of command being
				 * compiled. */
    CompileEnv *envPtr)		/* Holds resulting instructions. */
{
    Proc *procPtr = envPtr->procPtr;
    DefineLineInformation;	/* TIP #280 */
    Tcl_Token *varTokenPtr, *keyTokenPtr, *valueTokenPtr;
    int dictVarIndex, nameChars;
    const char *name;

    /*
     * There must be three arguments after the command.
     */

    if (parsePtr->numWords != 4 || procPtr == NULL) {
	return TCL_ERROR;
    }

    varTokenPtr = TokenAfter(parsePtr->tokenPtr);
    keyTokenPtr = TokenAfter(varTokenPtr);
    valueTokenPtr = TokenAfter(keyTokenPtr);
    if (varTokenPtr->type != TCL_TOKEN_SIMPLE_WORD) {
	return TCL_ERROR;
    }
    name = varTokenPtr[1].start;
    nameChars = varTokenPtr[1].size;
    if (!TclIsLocalScalar(name, nameChars)) {
	return TCL_ERROR;
    }
    dictVarIndex = TclFindCompiledLocal(name, nameChars, 1, procPtr);
    CompileWord(envPtr, keyTokenPtr, interp, 3);
    CompileWord(envPtr, valueTokenPtr, interp, 4);
    TclEmitInstInt4( INST_DICT_LAPPEND, dictVarIndex, envPtr);
    return TCL_OK;
}

/*
 *----------------------------------------------------------------------
 *
 * DupDictUpdateInfo, FreeDictUpdateInfo --
 *
 *	Functions to duplicate, release and print the aux data created for use
 *	with the INST_DICT_UPDATE_START and INST_DICT_UPDATE_END instructions.
 *
 * Results:
 *	DupDictUpdateInfo: a copy of the auxiliary data
 *	FreeDictUpdateInfo: none
 *	PrintDictUpdateInfo: none
 *
 * Side effects:
 *	DupDictUpdateInfo: allocates memory
 *	FreeDictUpdateInfo: releases memory
 *	PrintDictUpdateInfo: none
 *
 *----------------------------------------------------------------------
 */

static ClientData
DupDictUpdateInfo(
    ClientData clientData)
{
    DictUpdateInfo *dui1Ptr, *dui2Ptr;
    unsigned len;

    dui1Ptr = clientData;
    len = sizeof(DictUpdateInfo) + sizeof(int) * (dui1Ptr->length - 1);
    dui2Ptr = (DictUpdateInfo *) ckalloc(len);
    memcpy(dui2Ptr, dui1Ptr, len);
    return dui2Ptr;
}

static void
FreeDictUpdateInfo(
    ClientData clientData)
{
    ckfree(clientData);
}

static void
PrintDictUpdateInfo(
    ClientData clientData,
    Tcl_Obj *appendObj,
    ByteCode *codePtr,
    unsigned int pcOffset)
{
    DictUpdateInfo *duiPtr = clientData;
    int i;

    for (i=0 ; i<duiPtr->length ; i++) {
	if (i) {
	    Tcl_AppendToObj(appendObj, ", ", -1);
	}
	Tcl_AppendPrintfToObj(appendObj, "%%v%u", duiPtr->varIndices[i]);
    }
}

/*
 *----------------------------------------------------------------------
 *
 * TclCompileExprCmd --
 *
 *	Procedure called to compile the "expr" command.
 *
 * Results:
 * 	Returns TCL_OK for a successful compile. Returns TCL_ERROR to defer
 * 	evaluation to runtime.
 *
 * Side effects:
 *	Instructions are added to envPtr to execute the "expr" command at
 *	runtime.
 *
 *----------------------------------------------------------------------
 */

int
TclCompileExprCmd(
    Tcl_Interp *interp,		/* Used for error reporting. */
    Tcl_Parse *parsePtr,	/* Points to a parse structure for the command
				 * created by Tcl_ParseCommand. */
    Command *cmdPtr,		/* Points to defintion of command being
				 * compiled. */
    CompileEnv *envPtr)		/* Holds resulting instructions. */
{
    Tcl_Token *firstWordPtr;

    if (parsePtr->numWords == 1) {
	return TCL_ERROR;
    }

    /*
     * TIP #280: Use the per-word line information of the current command.
     */

    envPtr->line = envPtr->extCmdMapPtr->loc[
	    envPtr->extCmdMapPtr->nuloc-1].line[1];

    firstWordPtr = TokenAfter(parsePtr->tokenPtr);
    TclCompileExprWords(interp, firstWordPtr, parsePtr->numWords-1, envPtr);
    return TCL_OK;
}

/*
 *----------------------------------------------------------------------
 *
 * TclCompileForCmd --
 *
 *	Procedure called to compile the "for" command.
 *
 * Results:
 * 	Returns TCL_OK for a successful compile. Returns TCL_ERROR to defer
 * 	evaluation to runtime.
 *
 * Side effects:
 *	Instructions are added to envPtr to execute the "for" command at
 *	runtime.
 *
 *----------------------------------------------------------------------
 */

int
TclCompileForCmd(
    Tcl_Interp *interp,		/* Used for error reporting. */
    Tcl_Parse *parsePtr,	/* Points to a parse structure for the command
				 * created by Tcl_ParseCommand. */
    Command *cmdPtr,		/* Points to defintion of command being
				 * compiled. */
    CompileEnv *envPtr)		/* Holds resulting instructions. */
{
    Tcl_Token *startTokenPtr, *testTokenPtr, *nextTokenPtr, *bodyTokenPtr;
    JumpFixup jumpEvalCondFixup;
    int testCodeOffset, bodyCodeOffset, nextCodeOffset, jumpDist;
    int bodyRange, nextRange;
    int savedStackDepth = envPtr->currStackDepth;
    DefineLineInformation;	/* TIP #280 */

    if (parsePtr->numWords != 5) {
	return TCL_ERROR;
    }

    /*
     * If the test expression requires substitutions, don't compile the for
     * command inline. E.g., the expression might cause the loop to never
     * execute or execute forever, as in "for {} "$x > 5" {incr x} {}".
     */

    startTokenPtr = TokenAfter(parsePtr->tokenPtr);
    testTokenPtr = TokenAfter(startTokenPtr);
    if (testTokenPtr->type != TCL_TOKEN_SIMPLE_WORD) {
	return TCL_ERROR;
    }

    /*
     * Bail out also if the body or the next expression require substitutions
     * in order to insure correct behaviour [Bug 219166]
     */

    nextTokenPtr = TokenAfter(testTokenPtr);
    bodyTokenPtr = TokenAfter(nextTokenPtr);
    if ((nextTokenPtr->type != TCL_TOKEN_SIMPLE_WORD)
	    || (bodyTokenPtr->type != TCL_TOKEN_SIMPLE_WORD)) {
	return TCL_ERROR;
    }

    /*
     * Create ExceptionRange records for the body and the "next" command. The
     * "next" command's ExceptionRange supports break but not continue (and
     * has a -1 continueOffset).
     */

    bodyRange = DeclareExceptionRange(envPtr, LOOP_EXCEPTION_RANGE);
    nextRange = TclCreateExceptRange(LOOP_EXCEPTION_RANGE, envPtr);

    /*
     * Inline compile the initial command.
     */

    envPtr->line = mapPtr->loc[eclIndex].line[1];
    CompileBody(envPtr, startTokenPtr, interp);
    TclEmitOpcode(INST_POP, envPtr);

    /*
     * Jump to the evaluation of the condition. This code uses the "loop
     * rotation" optimisation (which eliminates one branch from the loop).
     * "for start cond next body" produces then:
     *       start
     *       goto A
     *    B: body                : bodyCodeOffset
     *       next                : nextCodeOffset, continueOffset
     *    A: cond -> result      : testCodeOffset
     *       if (result) goto B
     */

    TclEmitForwardJump(envPtr, TCL_UNCONDITIONAL_JUMP, &jumpEvalCondFixup);

    /*
     * Compile the loop body.
     */

    bodyCodeOffset = ExceptionRangeStarts(envPtr, bodyRange);
    envPtr->line = mapPtr->loc[eclIndex].line[4];
    CompileBody(envPtr, bodyTokenPtr, interp);
    ExceptionRangeEnds(envPtr, bodyRange);
    envPtr->currStackDepth = savedStackDepth + 1;
    TclEmitOpcode(INST_POP, envPtr);

    /*
     * Compile the "next" subcommand.
     */

    envPtr->currStackDepth = savedStackDepth;
    nextCodeOffset = ExceptionRangeStarts(envPtr, nextRange);
    envPtr->line = mapPtr->loc[eclIndex].line[3];
    CompileBody(envPtr, nextTokenPtr, interp);
    ExceptionRangeEnds(envPtr, nextRange);
    envPtr->currStackDepth = savedStackDepth + 1;
    TclEmitOpcode(INST_POP, envPtr);
    envPtr->currStackDepth = savedStackDepth;

    /*
     * Compile the test expression then emit the conditional jump that
     * terminates the for.
     */

    testCodeOffset = CurrentOffset(envPtr);

    jumpDist = testCodeOffset - jumpEvalCondFixup.codeOffset;
    if (TclFixupForwardJump(envPtr, &jumpEvalCondFixup, jumpDist, 127)) {
	bodyCodeOffset += 3;
	nextCodeOffset += 3;
	testCodeOffset += 3;
    }

    envPtr->line = mapPtr->loc[eclIndex].line[2];
    envPtr->currStackDepth = savedStackDepth;
    TclCompileExprWords(interp, testTokenPtr, 1, envPtr);
    envPtr->currStackDepth = savedStackDepth + 1;

    jumpDist = CurrentOffset(envPtr) - bodyCodeOffset;
    if (jumpDist > 127) {
	TclEmitInstInt4(INST_JUMP_TRUE4, -jumpDist, envPtr);
    } else {
	TclEmitInstInt1(INST_JUMP_TRUE1, -jumpDist, envPtr);
    }

    /*
     * Fix the starting points of the exception ranges (may have moved due to
     * jump type modification) and set where the exceptions target.
     */

    envPtr->exceptArrayPtr[bodyRange].codeOffset = bodyCodeOffset;
    envPtr->exceptArrayPtr[bodyRange].continueOffset = nextCodeOffset;

    envPtr->exceptArrayPtr[nextRange].codeOffset = nextCodeOffset;

    ExceptionRangeTarget(envPtr, bodyRange, breakOffset);
    ExceptionRangeTarget(envPtr, nextRange, breakOffset);

    /*
     * The for command's result is an empty string.
     */

    envPtr->currStackDepth = savedStackDepth;
    PushLiteral(envPtr, "", 0);

    return TCL_OK;
}

/*
 *----------------------------------------------------------------------
 *
 * TclCompileForeachCmd --
 *
 *	Procedure called to compile the "foreach" command.
 *
 * Results:
 * 	Returns TCL_OK for a successful compile. Returns TCL_ERROR to defer
 * 	evaluation to runtime.
 *
 * Side effects:
 *	Instructions are added to envPtr to execute the "foreach" command at
 *	runtime.
 *
 *----------------------------------------------------------------------
 */

int
TclCompileForeachCmd(
    Tcl_Interp *interp,		/* Used for error reporting. */
    Tcl_Parse *parsePtr,	/* Points to a parse structure for the command
				 * created by Tcl_ParseCommand. */
    Command *cmdPtr,		/* Points to defintion of command being
				 * compiled. */
    CompileEnv *envPtr)		/* Holds resulting instructions. */
{
    Proc *procPtr = envPtr->procPtr;
    ForeachInfo *infoPtr;	/* Points to the structure describing this
				 * foreach command. Stored in a AuxData
				 * record in the ByteCode. */
    int firstValueTemp;		/* Index of the first temp var in the frame
				 * used to point to a value list. */
    int loopCtTemp;		/* Index of temp var holding the loop's
				 * iteration count. */
    Tcl_Token *tokenPtr, *bodyTokenPtr;
    unsigned char *jumpPc;
    JumpFixup jumpFalseFixup;
    int jumpBackDist, jumpBackOffset, infoIndex, range, bodyIndex;
    int numWords, numLists, numVars, loopIndex, tempVar, i, j, code;
    int savedStackDepth = envPtr->currStackDepth;
    DefineLineInformation;	/* TIP #280 */

    /*
     * We parse the variable list argument words and create two arrays:
     *    varcList[i] is number of variables in i-th var list.
     *    varvList[i] points to array of var names in i-th var list.
     */

    int *varcList;
    const char ***varvList;

    /*
     * If the foreach command isn't in a procedure, don't compile it inline:
     * the payoff is too small.
     */

    if (procPtr == NULL) {
	return TCL_ERROR;
    }

    numWords = parsePtr->numWords;
    if ((numWords < 4) || (numWords%2 != 0)) {
	return TCL_ERROR;
    }

    /*
     * Bail out if the body requires substitutions in order to insure correct
     * behaviour. [Bug 219166]
     */

    for (i = 0, tokenPtr = parsePtr->tokenPtr; i < numWords-1; i++) {
	tokenPtr = TokenAfter(tokenPtr);
    }
    bodyTokenPtr = tokenPtr;
    if (bodyTokenPtr->type != TCL_TOKEN_SIMPLE_WORD) {
	return TCL_ERROR;
    }

    bodyIndex = i-1;

    /*
     * Allocate storage for the varcList and varvList arrays if necessary.
     */

    numLists = (numWords - 2)/2;
    varcList = (int *) TclStackAlloc(interp, numLists * sizeof(int));
    memset(varcList, 0, numLists * sizeof(int));
    varvList = (const char ***) TclStackAlloc(interp,
	    numLists * sizeof(const char **));
    memset((char*) varvList, 0, numLists * sizeof(const char **));

    /*
     * Break up each var list and set the varcList and varvList arrays. Don't
     * compile the foreach inline if any var name needs substitutions or isn't
     * a scalar, or if any var list needs substitutions.
     */

    loopIndex = 0;
    for (i = 0, tokenPtr = parsePtr->tokenPtr;
	    i < numWords-1;
	    i++, tokenPtr = TokenAfter(tokenPtr)) {
	Tcl_DString varList;

	if (i%2 != 1) {
	    continue;
	}
	if (tokenPtr->type != TCL_TOKEN_SIMPLE_WORD) {
	    code = TCL_ERROR;
	    goto done;
	}

	/*
	 * Lots of copying going on here. Need a ListObj wizard to show a
	 * better way.
	 */

	Tcl_DStringInit(&varList);
	Tcl_DStringAppend(&varList, tokenPtr[1].start, tokenPtr[1].size);
	code = Tcl_SplitList(interp, Tcl_DStringValue(&varList),
		&varcList[loopIndex], &varvList[loopIndex]);
	Tcl_DStringFree(&varList);
	if (code != TCL_OK) {
	    code = TCL_ERROR;
	    goto done;
	}
	numVars = varcList[loopIndex];

	/*
	 * If the variable list is empty, we can enter an infinite loop when
	 * the interpreted version would not. Take care to ensure this does
	 * not happen. [Bug 1671138]
	 */

	if (numVars == 0) {
	    code = TCL_ERROR;
	    goto done;
	}

	for (j = 0;  j < numVars;  j++) {
	    const char *varName = varvList[loopIndex][j];

	    if (!TclIsLocalScalar(varName, (int) strlen(varName))) {
		code = TCL_ERROR;
		goto done;
	    }
	}
	loopIndex++;
    }

    /*
     * We will compile the foreach command. Reserve (numLists + 1) temporary
     * variables:
     *    - numLists temps to hold each value list
     *    - 1 temp for the loop counter (index of next element in each list)
     *
     * At this time we don't try to reuse temporaries; if there are two
     * nonoverlapping foreach loops, they don't share any temps.
     */

    code = TCL_OK;
    firstValueTemp = -1;
    for (loopIndex = 0;  loopIndex < numLists;  loopIndex++) {
	tempVar = TclFindCompiledLocal(NULL, /*nameChars*/ 0,
		/*create*/ 1, procPtr);
	if (loopIndex == 0) {
	    firstValueTemp = tempVar;
	}
    }
    loopCtTemp = TclFindCompiledLocal(NULL, /*nameChars*/ 0,
	    /*create*/ 1, procPtr);

    /*
     * Create and initialize the ForeachInfo and ForeachVarList data
     * structures describing this command. Then create a AuxData record
     * pointing to the ForeachInfo structure.
     */

    infoPtr = (ForeachInfo *) ckalloc((unsigned)
	    sizeof(ForeachInfo) + numLists*sizeof(ForeachVarList *));
    infoPtr->numLists = numLists;
    infoPtr->firstValueTemp = firstValueTemp;
    infoPtr->loopCtTemp = loopCtTemp;
    for (loopIndex = 0;  loopIndex < numLists;  loopIndex++) {
	ForeachVarList *varListPtr;
	numVars = varcList[loopIndex];
	varListPtr = (ForeachVarList *) ckalloc((unsigned)
		sizeof(ForeachVarList) + numVars*sizeof(int));
	varListPtr->numVars = numVars;
	for (j = 0;  j < numVars;  j++) {
	    const char *varName = varvList[loopIndex][j];
	    int nameChars = strlen(varName);

	    varListPtr->varIndexes[j] = TclFindCompiledLocal(varName,
		    nameChars, /*create*/ 1, procPtr);
	}
	infoPtr->varLists[loopIndex] = varListPtr;
    }
    infoIndex = TclCreateAuxData(infoPtr, &tclForeachInfoType, envPtr);

    /*
     * Create an exception record to handle [break] and [continue].
     */

    range = DeclareExceptionRange(envPtr, LOOP_EXCEPTION_RANGE);

    /*
     * Evaluate then store each value list in the associated temporary.
     */

    loopIndex = 0;
    for (i = 0, tokenPtr = parsePtr->tokenPtr;
	    i < numWords-1;
	    i++, tokenPtr = TokenAfter(tokenPtr)) {
	if ((i%2 == 0) && (i > 0)) {
	    envPtr->line = mapPtr->loc[eclIndex].line[i];
	    CompileTokens(envPtr, tokenPtr, interp);
	    tempVar = (firstValueTemp + loopIndex);
	    if (tempVar <= 255) {
		TclEmitInstInt1(INST_STORE_SCALAR1, tempVar, envPtr);
	    } else {
		TclEmitInstInt4(INST_STORE_SCALAR4, tempVar, envPtr);
	    }
	    TclEmitOpcode(INST_POP, envPtr);
	    loopIndex++;
	}
    }

    /*
     * Initialize the temporary var that holds the count of loop iterations.
     */

    TclEmitInstInt4(INST_FOREACH_START4, infoIndex, envPtr);

    /*
     * Top of loop code: assign each loop variable and check whether
     * to terminate the loop.
     */

    ExceptionRangeTarget(envPtr, range, continueOffset);
    TclEmitInstInt4(INST_FOREACH_STEP4, infoIndex, envPtr);
    TclEmitForwardJump(envPtr, TCL_FALSE_JUMP, &jumpFalseFixup);

    /*
     * Inline compile the loop body.
     */

    envPtr->line = mapPtr->loc[eclIndex].line[bodyIndex];
    ExceptionRangeStarts(envPtr, range);
    CompileBody(envPtr, bodyTokenPtr, interp);
    ExceptionRangeEnds(envPtr, range);
    envPtr->currStackDepth = savedStackDepth + 1;
    TclEmitOpcode(INST_POP, envPtr);

    /*
     * Jump back to the test at the top of the loop. Generate a 4 byte jump if
     * the distance to the test is > 120 bytes. This is conservative and
     * ensures that we won't have to replace this jump if we later need to
     * replace the ifFalse jump with a 4 byte jump.
     */

    jumpBackOffset = CurrentOffset(envPtr);
    jumpBackDist = jumpBackOffset-envPtr->exceptArrayPtr[range].continueOffset;
    if (jumpBackDist > 120) {
	TclEmitInstInt4(INST_JUMP4, -jumpBackDist, envPtr);
    } else {
	TclEmitInstInt1(INST_JUMP1, -jumpBackDist, envPtr);
    }

    /*
     * Fix the target of the jump after the foreach_step test.
     */

    if (TclFixupForwardJumpToHere(envPtr, &jumpFalseFixup, 127)) {
	/*
	 * Update the loop body's starting PC offset since it moved down.
	 */

	envPtr->exceptArrayPtr[range].codeOffset += 3;

	/*
	 * Update the jump back to the test at the top of the loop since it
	 * also moved down 3 bytes.
	 */

	jumpBackOffset += 3;
	jumpPc = (envPtr->codeStart + jumpBackOffset);
	jumpBackDist += 3;
	if (jumpBackDist > 120) {
	    TclUpdateInstInt4AtPc(INST_JUMP4, -jumpBackDist, jumpPc);
	} else {
	    TclUpdateInstInt1AtPc(INST_JUMP1, -jumpBackDist, jumpPc);
	}
    }

    /*
     * Set the loop's break target.
     */

    ExceptionRangeTarget(envPtr, range, breakOffset);

    /*
     * The foreach command's result is an empty string.
     */

    envPtr->currStackDepth = savedStackDepth;
    PushLiteral(envPtr, "", 0);
    envPtr->currStackDepth = savedStackDepth + 1;

  done:
    for (loopIndex = 0;  loopIndex < numLists;  loopIndex++) {
	if (varvList[loopIndex] != NULL) {
	    ckfree((char *) varvList[loopIndex]);
	}
    }
    TclStackFree(interp, (void *)varvList);
    TclStackFree(interp, varcList);
    return code;
}

/*
 *----------------------------------------------------------------------
 *
 * DupForeachInfo --
 *
 *	This procedure duplicates a ForeachInfo structure created as auxiliary
 *	data during the compilation of a foreach command.
 *
 * Results:
 *	A pointer to a newly allocated copy of the existing ForeachInfo
 *	structure is returned.
 *
 * Side effects:
 *	Storage for the copied ForeachInfo record is allocated. If the
 *	original ForeachInfo structure pointed to any ForeachVarList records,
 *	these structures are also copied and pointers to them are stored in
 *	the new ForeachInfo record.
 *
 *----------------------------------------------------------------------
 */

static ClientData
DupForeachInfo(
    ClientData clientData)	/* The foreach command's compilation auxiliary
				 * data to duplicate. */
{
    register ForeachInfo *srcPtr = clientData;
    ForeachInfo *dupPtr;
    register ForeachVarList *srcListPtr, *dupListPtr;
    int numVars, i, j, numLists = srcPtr->numLists;

    dupPtr = (ForeachInfo *) ckalloc((unsigned)
	    sizeof(ForeachInfo) + numLists*sizeof(ForeachVarList *));
    dupPtr->numLists = numLists;
    dupPtr->firstValueTemp = srcPtr->firstValueTemp;
    dupPtr->loopCtTemp = srcPtr->loopCtTemp;

    for (i = 0;  i < numLists;  i++) {
	srcListPtr = srcPtr->varLists[i];
	numVars = srcListPtr->numVars;
	dupListPtr = (ForeachVarList *) ckalloc((unsigned)
		sizeof(ForeachVarList) + numVars*sizeof(int));
	dupListPtr->numVars = numVars;
	for (j = 0;  j < numVars;  j++) {
	    dupListPtr->varIndexes[j] =	srcListPtr->varIndexes[j];
	}
	dupPtr->varLists[i] = dupListPtr;
    }
    return dupPtr;
}

/*
 *----------------------------------------------------------------------
 *
 * FreeForeachInfo --
 *
 *	Procedure to free a ForeachInfo structure created as auxiliary data
 *	during the compilation of a foreach command.
 *
 * Results:
 *	None.
 *
 * Side effects:
 *	Storage for the ForeachInfo structure pointed to by the ClientData
 *	argument is freed as is any ForeachVarList record pointed to by the
 *	ForeachInfo structure.
 *
 *----------------------------------------------------------------------
 */

static void
FreeForeachInfo(
    ClientData clientData)	/* The foreach command's compilation auxiliary
				 * data to free. */
{
    register ForeachInfo *infoPtr = clientData;
    register ForeachVarList *listPtr;
    int numLists = infoPtr->numLists;
    register int i;

    for (i = 0;  i < numLists;  i++) {
	listPtr = infoPtr->varLists[i];
	ckfree((char *) listPtr);
    }
    ckfree((char *) infoPtr);
}

/*
 *----------------------------------------------------------------------
 *
 * PrintForeachInfo --
 *
 *	Function to write a human-readable representation of a ForeachInfo
 *	structure to stdout for debugging.
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
PrintForeachInfo(
    ClientData clientData,
    Tcl_Obj *appendObj,
    ByteCode *codePtr,
    unsigned int pcOffset)
{
    register ForeachInfo *infoPtr = clientData;
    register ForeachVarList *varsPtr;
    int i, j;

    Tcl_AppendToObj(appendObj, "data=[", -1);

    for (i=0 ; i<infoPtr->numLists ; i++) {
	if (i) {
	    Tcl_AppendToObj(appendObj, ", ", -1);
	}
	Tcl_AppendPrintfToObj(appendObj, "%%v%u",
		(unsigned) (infoPtr->firstValueTemp + i));
    }
    Tcl_AppendPrintfToObj(appendObj, "], loop=%%v%u",
	    (unsigned) infoPtr->loopCtTemp);
    for (i=0 ; i<infoPtr->numLists ; i++) {
	if (i) {
	    Tcl_AppendToObj(appendObj, ",", -1);
	}
	Tcl_AppendPrintfToObj(appendObj, "\n\t\t it%%v%u\t[",
		(unsigned) (infoPtr->firstValueTemp + i));
	varsPtr = infoPtr->varLists[i];
	for (j=0 ; j<varsPtr->numVars ; j++) {
	    if (j) {
		Tcl_AppendToObj(appendObj, ", ", -1);
	    }
	    Tcl_AppendPrintfToObj(appendObj, "%%v%u",
		    (unsigned) varsPtr->varIndexes[j]);
	}
	Tcl_AppendToObj(appendObj, "]", -1);
    }
}

/*
 *----------------------------------------------------------------------
 *
 * TclCompileIfCmd --
 *
 *	Procedure called to compile the "if" command.
 *
 * Results:
 * 	Returns TCL_OK for a successful compile. Returns TCL_ERROR to defer
 * 	evaluation to runtime.
 *
 * Side effects:
 *	Instructions are added to envPtr to execute the "if" command at
 *	runtime.
 *
 *----------------------------------------------------------------------
 */

int
TclCompileIfCmd(
    Tcl_Interp *interp,		/* Used for error reporting. */
    Tcl_Parse *parsePtr,	/* Points to a parse structure for the command
				 * created by Tcl_ParseCommand. */
    Command *cmdPtr,		/* Points to defintion of command being
				 * compiled. */
    CompileEnv *envPtr)		/* Holds resulting instructions. */
{
    JumpFixupArray jumpFalseFixupArray;
    				/* Used to fix the ifFalse jump after each
				 * test when its target PC is determined. */
    JumpFixupArray jumpEndFixupArray;
				/* Used to fix the jump after each "then" body
				 * to the end of the "if" when that PC is
				 * determined. */
    Tcl_Token *tokenPtr, *testTokenPtr;
    int jumpIndex = 0;		/* Avoid compiler warning. */
    int jumpFalseDist, numWords, wordIdx, numBytes, j, code;
    const char *word;
    int savedStackDepth = envPtr->currStackDepth;
				/* Saved stack depth at the start of the first
				 * test; the envPtr current depth is restored
				 * to this value at the start of each test. */
    int realCond = 1;		/* Set to 0 for static conditions:
				 * "if 0 {..}" */
    int boolVal;		/* Value of static condition. */
    int compileScripts = 1;
    DefineLineInformation;	/* TIP #280 */

    /*
     * Only compile the "if" command if all arguments are simple words, in
     * order to insure correct substitution [Bug 219166]
     */

    tokenPtr = parsePtr->tokenPtr;
    wordIdx = 0;
    numWords = parsePtr->numWords;

    for (wordIdx = 0; wordIdx < numWords; wordIdx++) {
	if (tokenPtr->type != TCL_TOKEN_SIMPLE_WORD) {
	    return TCL_ERROR;
	}
	tokenPtr = TokenAfter(tokenPtr);
    }

    TclInitJumpFixupArray(&jumpFalseFixupArray);
    TclInitJumpFixupArray(&jumpEndFixupArray);
    code = TCL_OK;

    /*
     * Each iteration of this loop compiles one "if expr ?then? body" or
     * "elseif expr ?then? body" clause.
     */

    tokenPtr = parsePtr->tokenPtr;
    wordIdx = 0;
    while (wordIdx < numWords) {
	/*
	 * Stop looping if the token isn't "if" or "elseif".
	 */

	word = tokenPtr[1].start;
	numBytes = tokenPtr[1].size;
	if ((tokenPtr == parsePtr->tokenPtr)
		|| ((numBytes == 6) && (strncmp(word, "elseif", 6) == 0))) {
	    tokenPtr = TokenAfter(tokenPtr);
	    wordIdx++;
	} else {
	    break;
	}
	if (wordIdx >= numWords) {
	    code = TCL_ERROR;
	    goto done;
	}

	/*
	 * Compile the test expression then emit the conditional jump around
	 * the "then" part.
	 */

	envPtr->currStackDepth = savedStackDepth;
	testTokenPtr = tokenPtr;

	if (realCond) {
	    /*
	     * Find out if the condition is a constant.
	     */

	    Tcl_Obj *boolObj = Tcl_NewStringObj(testTokenPtr[1].start,
		    testTokenPtr[1].size);
	    Tcl_IncrRefCount(boolObj);
	    code = Tcl_GetBooleanFromObj(NULL, boolObj, &boolVal);
	    TclDecrRefCount(boolObj);
	    if (code == TCL_OK) {
		/*
		 * A static condition.
		 */

		realCond = 0;
		if (!boolVal) {
		    compileScripts = 0;
		}
	    } else {
		envPtr->line = mapPtr->loc[eclIndex].line[wordIdx];
		Tcl_ResetResult(interp);
		TclCompileExprWords(interp, testTokenPtr, 1, envPtr);
		if (jumpFalseFixupArray.next >= jumpFalseFixupArray.end) {
		    TclExpandJumpFixupArray(&jumpFalseFixupArray);
		}
		jumpIndex = jumpFalseFixupArray.next;
		jumpFalseFixupArray.next++;
		TclEmitForwardJump(envPtr, TCL_FALSE_JUMP,
			jumpFalseFixupArray.fixup+jumpIndex);
	    }
	    code = TCL_OK;
	}

	/*
	 * Skip over the optional "then" before the then clause.
	 */

	tokenPtr = TokenAfter(testTokenPtr);
	wordIdx++;
	if (wordIdx >= numWords) {
	    code = TCL_ERROR;
	    goto done;
	}
	if (tokenPtr->type == TCL_TOKEN_SIMPLE_WORD) {
	    word = tokenPtr[1].start;
	    numBytes = tokenPtr[1].size;
	    if ((numBytes == 4) && (strncmp(word, "then", 4) == 0)) {
		tokenPtr = TokenAfter(tokenPtr);
		wordIdx++;
		if (wordIdx >= numWords) {
		    code = TCL_ERROR;
		    goto done;
		}
	    }
	}

	/*
	 * Compile the "then" command body.
	 */

	if (compileScripts) {
	    envPtr->line = mapPtr->loc[eclIndex].line[wordIdx];
	    envPtr->currStackDepth = savedStackDepth;
	    CompileBody(envPtr, tokenPtr, interp);
	}

	if (realCond) {
	    /*
	     * Jump to the end of the "if" command. Both jumpFalseFixupArray
	     * and jumpEndFixupArray are indexed by "jumpIndex".
	     */

	    if (jumpEndFixupArray.next >= jumpEndFixupArray.end) {
		TclExpandJumpFixupArray(&jumpEndFixupArray);
	    }
	    jumpEndFixupArray.next++;
	    TclEmitForwardJump(envPtr, TCL_UNCONDITIONAL_JUMP,
		    jumpEndFixupArray.fixup+jumpIndex);

	    /*
	     * Fix the target of the jumpFalse after the test. Generate a 4
	     * byte jump if the distance is > 120 bytes. This is conservative,
	     * and ensures that we won't have to replace this jump if we later
	     * also need to replace the proceeding jump to the end of the "if"
	     * with a 4 byte jump.
	     */

	    if (TclFixupForwardJumpToHere(envPtr,
		    jumpFalseFixupArray.fixup+jumpIndex, 120)) {
		/*
		 * Adjust the code offset for the proceeding jump to the end
		 * of the "if" command.
		 */

		jumpEndFixupArray.fixup[jumpIndex].codeOffset += 3;
	    }
	} else if (boolVal) {
	    /*
	     * We were processing an "if 1 {...}"; stop compiling scripts.
	     */

	    compileScripts = 0;
	} else {
	    /*
	     * We were processing an "if 0 {...}"; reset so that the rest
	     * (elseif, else) is compiled correctly.
	     */

	    realCond = 1;
	    compileScripts = 1;
	}

	tokenPtr = TokenAfter(tokenPtr);
	wordIdx++;
    }

    /*
     * Restore the current stack depth in the environment; the "else" clause
     * (or its default) will add 1 to this.
     */

    envPtr->currStackDepth = savedStackDepth;

    /*
     * Check for the optional else clause. Do not compile anything if this was
     * an "if 1 {...}" case.
     */

    if ((wordIdx < numWords) && (tokenPtr->type == TCL_TOKEN_SIMPLE_WORD)) {
	/*
	 * There is an else clause. Skip over the optional "else" word.
	 */

	word = tokenPtr[1].start;
	numBytes = tokenPtr[1].size;
	if ((numBytes == 4) && (strncmp(word, "else", 4) == 0)) {
	    tokenPtr = TokenAfter(tokenPtr);
	    wordIdx++;
	    if (wordIdx >= numWords) {
		code = TCL_ERROR;
		goto done;
	    }
	}

	if (compileScripts) {
	    /*
	     * Compile the else command body.
	     */

	    envPtr->line = mapPtr->loc[eclIndex].line[wordIdx];
	    CompileBody(envPtr, tokenPtr, interp);
	}

	/*
	 * Make sure there are no words after the else clause.
	 */

	wordIdx++;
	if (wordIdx < numWords) {
	    code = TCL_ERROR;
	    goto done;
	}
    } else {
	/*
	 * No else clause: the "if" command's result is an empty string.
	 */

	if (compileScripts) {
	    PushLiteral(envPtr, "", 0);
	}
    }

    /*
     * Fix the unconditional jumps to the end of the "if" command.
     */

    for (j = jumpEndFixupArray.next;  j > 0;  j--) {
	jumpIndex = (j - 1);	/* i.e. process the closest jump first. */
	if (TclFixupForwardJumpToHere(envPtr,
		jumpEndFixupArray.fixup+jumpIndex, 127)) {
	    /*
	     * Adjust the immediately preceeding "ifFalse" jump. We moved it's
	     * target (just after this jump) down three bytes.
	     */

	    unsigned char *ifFalsePc = envPtr->codeStart
		    + jumpFalseFixupArray.fixup[jumpIndex].codeOffset;
	    unsigned char opCode = *ifFalsePc;

	    if (opCode == INST_JUMP_FALSE1) {
		jumpFalseDist = TclGetInt1AtPtr(ifFalsePc + 1);
		jumpFalseDist += 3;
		TclStoreInt1AtPtr(jumpFalseDist, (ifFalsePc + 1));
	    } else if (opCode == INST_JUMP_FALSE4) {
		jumpFalseDist = TclGetInt4AtPtr(ifFalsePc + 1);
		jumpFalseDist += 3;
		TclStoreInt4AtPtr(jumpFalseDist, (ifFalsePc + 1));
	    } else {
		Tcl_Panic("TclCompileIfCmd: unexpected opcode \"%d\" updating ifFalse jump", (int) opCode);
	    }
	}
    }

    /*
     * Free the jumpFixupArray array if malloc'ed storage was used.
     */

  done:
    envPtr->currStackDepth = savedStackDepth + 1;
    TclFreeJumpFixupArray(&jumpFalseFixupArray);
    TclFreeJumpFixupArray(&jumpEndFixupArray);
    return code;
}

/*
 *----------------------------------------------------------------------
 *
 * TclCompileIncrCmd --
 *
 *	Procedure called to compile the "incr" command.
 *
 * Results:
 * 	Returns TCL_OK for a successful compile. Returns TCL_ERROR to defer
 * 	evaluation to runtime.
 *
 * Side effects:
 *	Instructions are added to envPtr to execute the "incr" command at
 *	runtime.
 *
 *----------------------------------------------------------------------
 */

int
TclCompileIncrCmd(
    Tcl_Interp *interp,		/* Used for error reporting. */
    Tcl_Parse *parsePtr,	/* Points to a parse structure for the command
				 * created by Tcl_ParseCommand. */
    Command *cmdPtr,		/* Points to defintion of command being
				 * compiled. */
    CompileEnv *envPtr)		/* Holds resulting instructions. */
{
    Tcl_Token *varTokenPtr, *incrTokenPtr;
    int simpleVarName, isScalar, localIndex, haveImmValue, immValue;
    DefineLineInformation;	/* TIP #280 */

    if ((parsePtr->numWords != 2) && (parsePtr->numWords != 3)) {
	return TCL_ERROR;
    }

    varTokenPtr = TokenAfter(parsePtr->tokenPtr);

    PushVarName(interp, varTokenPtr, envPtr, TCL_NO_LARGE_INDEX|TCL_CREATE_VAR,
		&localIndex, &simpleVarName, &isScalar,
		mapPtr->loc[eclIndex].line[1]);

    /*
     * If an increment is given, push it, but see first if it's a small
     * integer.
     */

    haveImmValue = 0;
    immValue = 1;
    if (parsePtr->numWords == 3) {
	incrTokenPtr = TokenAfter(varTokenPtr);
	if (incrTokenPtr->type == TCL_TOKEN_SIMPLE_WORD) {
	    const char *word = incrTokenPtr[1].start;
	    int numBytes = incrTokenPtr[1].size;
	    int code;
	    Tcl_Obj *intObj = Tcl_NewStringObj(word, numBytes);
	    Tcl_IncrRefCount(intObj);
	    code = TclGetIntFromObj(NULL, intObj, &immValue);
	    TclDecrRefCount(intObj);
	    if ((code == TCL_OK) && (-127 <= immValue) && (immValue <= 127)) {
		haveImmValue = 1;
	    }
	    if (!haveImmValue) {
		PushLiteral(envPtr, word, numBytes);
	    }
	} else {
	    envPtr->line = mapPtr->loc[eclIndex].line[2];
	    CompileTokens(envPtr, incrTokenPtr, interp);
	}
    } else {			/* No incr amount given so use 1. */
	haveImmValue = 1;
    }

    /*
     * Emit the instruction to increment the variable.
     */

    if (simpleVarName) {
	if (isScalar) {
	    if (localIndex >= 0) {
		if (haveImmValue) {
		    TclEmitInstInt1(INST_INCR_SCALAR1_IMM, localIndex, envPtr);
		    TclEmitInt1(immValue, envPtr);
		} else {
		    TclEmitInstInt1(INST_INCR_SCALAR1, localIndex, envPtr);
		}
	    } else {
		if (haveImmValue) {
		    TclEmitInstInt1(INST_INCR_SCALAR_STK_IMM, immValue, envPtr);
		} else {
		    TclEmitOpcode(INST_INCR_SCALAR_STK, envPtr);
		}
	    }
	} else {
	    if (localIndex >= 0) {
		if (haveImmValue) {
		    TclEmitInstInt1(INST_INCR_ARRAY1_IMM, localIndex, envPtr);
		    TclEmitInt1(immValue, envPtr);
		} else {
		    TclEmitInstInt1(INST_INCR_ARRAY1, localIndex, envPtr);
		}
	    } else {
		if (haveImmValue) {
		    TclEmitInstInt1(INST_INCR_ARRAY_STK_IMM, immValue, envPtr);
		} else {
		    TclEmitOpcode(INST_INCR_ARRAY_STK, envPtr);
		}
	    }
	}
    } else {			/* Non-simple variable name. */
	if (haveImmValue) {
	    TclEmitInstInt1(INST_INCR_STK_IMM, immValue, envPtr);
	} else {
	    TclEmitOpcode(INST_INCR_STK, envPtr);
	}
    }

    return TCL_OK;
}

/*
 *----------------------------------------------------------------------
 *
 * TclCompileLappendCmd --
 *
 *	Procedure called to compile the "lappend" command.
 *
 * Results:
 * 	Returns TCL_OK for a successful compile. Returns TCL_ERROR to defer
 * 	evaluation to runtime.
 *
 * Side effects:
 *	Instructions are added to envPtr to execute the "lappend" command at
 *	runtime.
 *
 *----------------------------------------------------------------------
 */

int
TclCompileLappendCmd(
    Tcl_Interp *interp,		/* Used for error reporting. */
    Tcl_Parse *parsePtr,	/* Points to a parse structure for the command
				 * created by Tcl_ParseCommand. */
    Command *cmdPtr,		/* Points to defintion of command being
				 * compiled. */
    CompileEnv *envPtr)		/* Holds resulting instructions. */
{
    Tcl_Token *varTokenPtr;
    int simpleVarName, isScalar, localIndex, numWords;
    DefineLineInformation;	/* TIP #280 */

    /*
     * If we're not in a procedure, don't compile.
     */

    if (envPtr->procPtr == NULL) {
	return TCL_ERROR;
    }

    numWords = parsePtr->numWords;
    if (numWords == 1) {
	return TCL_ERROR;
    }
    if (numWords != 3) {
	/*
	 * LAPPEND instructions currently only handle one value appends.
	 */

	return TCL_ERROR;
    }

    /*
     * Decide if we can use a frame slot for the var/array name or if we
     * need to emit code to compute and push the name at runtime. We use a
     * frame slot (entry in the array of local vars) if we are compiling a
     * procedure body and if the name is simple text that does not include
     * namespace qualifiers.
     */

    varTokenPtr = TokenAfter(parsePtr->tokenPtr);

    PushVarName(interp, varTokenPtr, envPtr, TCL_CREATE_VAR,
		&localIndex, &simpleVarName, &isScalar,
		mapPtr->loc[eclIndex].line[1]);

    /*
     * If we are doing an assignment, push the new value. In the no values
     * case, create an empty object.
     */

    if (numWords > 2) {
	Tcl_Token *valueTokenPtr = TokenAfter(varTokenPtr);
	CompileWord(envPtr, valueTokenPtr, interp, 2);
    }

    /*
     * Emit instructions to set/get the variable.
     */

    /*
     * The *_STK opcodes should be refactored to make better use of existing
     * LOAD/STORE instructions.
     */

    if (simpleVarName) {
	if (isScalar) {
	    if (localIndex < 0) {
		TclEmitOpcode(INST_LAPPEND_STK, envPtr);
	    } else if (localIndex <= 255) {
		TclEmitInstInt1(INST_LAPPEND_SCALAR1, localIndex, envPtr);
	    } else {
		TclEmitInstInt4(INST_LAPPEND_SCALAR4, localIndex, envPtr);
	    }
	} else {
	    if (localIndex < 0) {
		TclEmitOpcode(INST_LAPPEND_ARRAY_STK, envPtr);
	    } else if (localIndex <= 255) {
		TclEmitInstInt1(INST_LAPPEND_ARRAY1, localIndex, envPtr);
	    } else {
		TclEmitInstInt4(INST_LAPPEND_ARRAY4, localIndex, envPtr);
	    }
	}
    } else {
	TclEmitOpcode(INST_LAPPEND_STK, envPtr);
    }

    return TCL_OK;
}

/*
 *----------------------------------------------------------------------
 *
 * TclCompileLassignCmd --
 *
 *	Procedure called to compile the "lassign" command.
 *
 * Results:
 * 	Returns TCL_OK for a successful compile. Returns TCL_ERROR to defer
 * 	evaluation to runtime.
 *
 * Side effects:
 *	Instructions are added to envPtr to execute the "lassign" command at
 *	runtime.
 *
 *----------------------------------------------------------------------
 */

int
TclCompileLassignCmd(
    Tcl_Interp *interp,		/* Used for error reporting. */
    Tcl_Parse *parsePtr,	/* Points to a parse structure for the command
				 * created by Tcl_ParseCommand. */
    Command *cmdPtr,		/* Points to defintion of command being
				 * compiled. */
    CompileEnv *envPtr)		/* Holds resulting instructions. */
{
    Tcl_Token *tokenPtr;
    int simpleVarName, isScalar, localIndex, numWords, idx;
    DefineLineInformation;	/* TIP #280 */

    numWords = parsePtr->numWords;

    /*
     * Check for command syntax error, but we'll punt that to runtime.
     */

    if (numWords < 3) {
	return TCL_ERROR;
    }

    /*
     * Generate code to push list being taken apart by [lassign].
     */

    tokenPtr = TokenAfter(parsePtr->tokenPtr);
    CompileWord(envPtr, tokenPtr, interp, 1);

    /*
     * Generate code to assign values from the list to variables.
     */

    for (idx=0 ; idx<numWords-2 ; idx++) {
	tokenPtr = TokenAfter(tokenPtr);

	/*
	 * Generate the next variable name.
	 */

	PushVarName(interp, tokenPtr, envPtr, TCL_CREATE_VAR, &localIndex,
		&simpleVarName, &isScalar, mapPtr->loc[eclIndex].line[idx+2]);

	/*
	 * Emit instructions to get the idx'th item out of the list value on
	 * the stack and assign it to the variable.
	 */

	if (simpleVarName) {
	    if (isScalar) {
		if (localIndex >= 0) {
		    TclEmitOpcode(INST_DUP, envPtr);
		    TclEmitInstInt4(INST_LIST_INDEX_IMM, idx, envPtr);
		    if (localIndex <= 255) {
			TclEmitInstInt1(INST_STORE_SCALAR1,localIndex,envPtr);
		    } else {
			TclEmitInstInt4(INST_STORE_SCALAR4,localIndex,envPtr);
		    }
		} else {
		    TclEmitInstInt4(INST_OVER, 1, envPtr);
		    TclEmitInstInt4(INST_LIST_INDEX_IMM, idx, envPtr);
		    TclEmitOpcode(INST_STORE_SCALAR_STK, envPtr);
		}
	    } else {
		if (localIndex >= 0) {
		    TclEmitInstInt4(INST_OVER, 1, envPtr);
		    TclEmitInstInt4(INST_LIST_INDEX_IMM, idx, envPtr);
		    if (localIndex <= 255) {
			TclEmitInstInt1(INST_STORE_ARRAY1, localIndex, envPtr);
		    } else {
			TclEmitInstInt4(INST_STORE_ARRAY4, localIndex, envPtr);
		    }
		} else {
		    TclEmitInstInt4(INST_OVER, 2, envPtr);
		    TclEmitInstInt4(INST_LIST_INDEX_IMM, idx, envPtr);
		    TclEmitOpcode(INST_STORE_ARRAY_STK, envPtr);
		}
	    }
	} else {
	    TclEmitInstInt4(INST_OVER, 1, envPtr);
	    TclEmitInstInt4(INST_LIST_INDEX_IMM, idx, envPtr);
	    TclEmitOpcode(INST_STORE_STK, envPtr);
	}
	TclEmitOpcode(INST_POP, envPtr);
    }

    /*
     * Generate code to leave the rest of the list on the stack.
     */

    TclEmitInstInt4(INST_LIST_RANGE_IMM, idx, envPtr);
    TclEmitInt4(-2, envPtr);	/* -2 == "end" */

    return TCL_OK;
}

/*
 *----------------------------------------------------------------------
 *
 * TclCompileLindexCmd --
 *
 *	Procedure called to compile the "lindex" command.
 *
 * Results:
 * 	Returns TCL_OK for a successful compile. Returns TCL_ERROR to defer
 * 	evaluation to runtime.
 *
 * Side effects:
 *	Instructions are added to envPtr to execute the "lindex" command at
 *	runtime.
 *
 *----------------------------------------------------------------------
 */

int
TclCompileLindexCmd(
    Tcl_Interp *interp,		/* Used for error reporting. */
    Tcl_Parse *parsePtr,	/* Points to a parse structure for the command
				 * created by Tcl_ParseCommand. */
    Command *cmdPtr,		/* Points to defintion of command being
				 * compiled. */
    CompileEnv *envPtr)		/* Holds resulting instructions. */
{
    Tcl_Token *idxTokenPtr, *valTokenPtr;
    int i, numWords = parsePtr->numWords;
    DefineLineInformation;	/* TIP #280 */

    /*
     * Quit if too few args.
     */

    if (numWords <= 1) {
	return TCL_ERROR;
    }

    valTokenPtr = TokenAfter(parsePtr->tokenPtr);
    if (numWords != 3) {
	goto emitComplexLindex;
    }

    idxTokenPtr = TokenAfter(valTokenPtr);
    if (idxTokenPtr->type == TCL_TOKEN_SIMPLE_WORD) {
	Tcl_Obj *tmpObj;
	int idx, result;

	tmpObj = Tcl_NewStringObj(idxTokenPtr[1].start, idxTokenPtr[1].size);
	result = TclGetIntFromObj(NULL, tmpObj, &idx);
	TclDecrRefCount(tmpObj);

	if (result == TCL_OK && idx >= 0) {
	    /*
	     * All checks have been completed, and we have exactly this
	     * construct:
	     *	 lindex <arbitraryValue> <posInt>
	     * This is best compiled as a push of the arbitrary value followed
	     * by an "immediate lindex" which is the most efficient variety.
	     */

	    CompileWord(envPtr, valTokenPtr, interp, 1);
	    TclEmitInstInt4(INST_LIST_INDEX_IMM, idx, envPtr);
	    return TCL_OK;
	}

	/*
	 * If the conversion failed or the value was negative, we just keep on
	 * going with the more complex compilation.
	 */
    }

    /*
     * Push the operands onto the stack.
     */

  emitComplexLindex:
    for (i=1 ; i<numWords ; i++) {
	CompileWord(envPtr, valTokenPtr, interp, i);
	valTokenPtr = TokenAfter(valTokenPtr);
    }

    /*
     * Emit INST_LIST_INDEX if objc==3, or INST_LIST_INDEX_MULTI if there are
     * multiple index args.
     */

    if (numWords == 3) {
	TclEmitOpcode(INST_LIST_INDEX, envPtr);
    } else {
 	TclEmitInstInt4(INST_LIST_INDEX_MULTI, numWords-1, envPtr);
    }

    return TCL_OK;
}

/*
 *----------------------------------------------------------------------
 *
 * TclCompileListCmd --
 *
 *	Procedure called to compile the "list" command.
 *
 * Results:
 * 	Returns TCL_OK for a successful compile. Returns TCL_ERROR to defer
 * 	evaluation to runtime.
 *
 * Side effects:
 *	Instructions are added to envPtr to execute the "list" command at
 *	runtime.
 *
 *----------------------------------------------------------------------
 */

int
TclCompileListCmd(
    Tcl_Interp *interp,		/* Used for error reporting. */
    Tcl_Parse *parsePtr,	/* Points to a parse structure for the command
				 * created by Tcl_ParseCommand. */
    Command *cmdPtr,		/* Points to defintion of command being
				 * compiled. */
    CompileEnv *envPtr)		/* Holds resulting instructions. */
{
    DefineLineInformation;	/* TIP #280 */

    /*
     * If we're not in a procedure, don't compile.
     */

    if (envPtr->procPtr == NULL) {
	return TCL_ERROR;
    }

    if (parsePtr->numWords == 1) {
	/*
	 * [list] without arguments just pushes an empty object.
	 */

	PushLiteral(envPtr, "", 0);
    } else {
	/*
	 * Push the all values onto the stack.
	 */

	Tcl_Token *valueTokenPtr;
	int i, numWords;

	numWords = parsePtr->numWords;

	valueTokenPtr = TokenAfter(parsePtr->tokenPtr);
	for (i = 1; i < numWords; i++) {
	    CompileWord(envPtr, valueTokenPtr, interp, i);
	    valueTokenPtr = TokenAfter(valueTokenPtr);
	}
	TclEmitInstInt4(INST_LIST, numWords - 1, envPtr);
    }

    return TCL_OK;
}

/*
 *----------------------------------------------------------------------
 *
 * TclCompileLlengthCmd --
 *
 *	Procedure called to compile the "llength" command.
 *
 * Results:
 * 	Returns TCL_OK for a successful compile. Returns TCL_ERROR to defer
 * 	evaluation to runtime.
 *
 * Side effects:
 *	Instructions are added to envPtr to execute the "llength" command at
 *	runtime.
 *
 *----------------------------------------------------------------------
 */

int
TclCompileLlengthCmd(
    Tcl_Interp *interp,		/* Used for error reporting. */
    Tcl_Parse *parsePtr,	/* Points to a parse structure for the command
				 * created by Tcl_ParseCommand. */
    Command *cmdPtr,		/* Points to defintion of command being
				 * compiled. */
    CompileEnv *envPtr)		/* Holds resulting instructions. */
{
    Tcl_Token *varTokenPtr;
    DefineLineInformation;	/* TIP #280 */

    if (parsePtr->numWords != 2) {
	return TCL_ERROR;
    }
    varTokenPtr = TokenAfter(parsePtr->tokenPtr);

    CompileWord(envPtr, varTokenPtr, interp, 1);
    TclEmitOpcode(INST_LIST_LENGTH, envPtr);
    return TCL_OK;
}

/*
 *----------------------------------------------------------------------
 *
 * TclCompileLsetCmd --
 *
 *	Procedure called to compile the "lset" command.
 *
 * Results:
 * 	Returns TCL_OK for a successful compile. Returns TCL_ERROR to defer
 * 	evaluation to runtime.
 *
 * Side effects:
 *	Instructions are added to envPtr to execute the "lset" command at
 *	runtime.
 *
 * The general template for execution of the "lset" command is:
 *	(1) Instructions to push the variable name, unless the variable is
 *	    local to the stack frame.
 *	(2) If the variable is an array element, instructions to push the
 *	    array element name.
 *	(3) Instructions to push each of zero or more "index" arguments to the
 *	    stack, followed with the "newValue" element.
 *	(4) Instructions to duplicate the variable name and/or array element
 *	    name onto the top of the stack, if either was pushed at steps (1)
 *	    and (2).
 *	(5) The appropriate INST_LOAD_* instruction to place the original
 *	    value of the list variable at top of stack.
 *	(6) At this point, the stack contains:
 *		varName? arrayElementName? index1 index2 ... newValue oldList
 *	    The compiler emits one of INST_LSET_FLAT or INST_LSET_LIST
 *	    according as whether there is exactly one index element (LIST) or
 *	    either zero or else two or more (FLAT). This instruction removes
 *	    everything from the stack except for the two names and pushes the
 *	    new value of the variable.
 *	(7) Finally, INST_STORE_* stores the new value in the variable and
 *	    cleans up the stack.
 *
 *----------------------------------------------------------------------
 */

int
TclCompileLsetCmd(
    Tcl_Interp *interp,		/* Tcl interpreter for error reporting. */
    Tcl_Parse *parsePtr,	/* Points to a parse structure for the
				 * command. */
    Command *cmdPtr,		/* Points to defintion of command being
				 * compiled. */
    CompileEnv *envPtr)		/* Holds the resulting instructions. */
{
    int tempDepth;		/* Depth used for emitting one part of the
				 * code burst. */
    Tcl_Token *varTokenPtr;	/* Pointer to the Tcl_Token representing the
				 * parse of the variable name. */
    int localIndex;		/* Index of var in local var table. */
    int simpleVarName;		/* Flag == 1 if var name is simple. */
    int isScalar;		/* Flag == 1 if scalar, 0 if array. */
    int i;
    DefineLineInformation;	/* TIP #280 */

    /*
     * Check argument count.
     */

    if (parsePtr->numWords < 3) {
	/*
	 * Fail at run time, not in compilation.
	 */

	return TCL_ERROR;
    }

    /*
     * Decide if we can use a frame slot for the var/array name or if we need
     * to emit code to compute and push the name at runtime. We use a frame
     * slot (entry in the array of local vars) if we are compiling a procedure
     * body and if the name is simple text that does not include namespace
     * qualifiers.
     */

    varTokenPtr = TokenAfter(parsePtr->tokenPtr);
    PushVarName(interp, varTokenPtr, envPtr, TCL_CREATE_VAR,
		&localIndex, &simpleVarName, &isScalar,
		mapPtr->loc[eclIndex].line[1]);

    /*
     * Push the "index" args and the new element value.
     */

    for (i=2 ; i<parsePtr->numWords ; ++i) {
	varTokenPtr = TokenAfter(varTokenPtr);
	CompileWord(envPtr, varTokenPtr, interp, i);
    }

    /*
     * Duplicate the variable name if it's been pushed.
     */

    if (!simpleVarName || localIndex < 0) {
	if (!simpleVarName || isScalar) {
	    tempDepth = parsePtr->numWords - 2;
	} else {
	    tempDepth = parsePtr->numWords - 1;
	}
	TclEmitInstInt4(INST_OVER, tempDepth, envPtr);
    }

    /*
     * Duplicate an array index if one's been pushed.
     */

    if (simpleVarName && !isScalar) {
	if (localIndex < 0) {
	    tempDepth = parsePtr->numWords - 1;
	} else {
	    tempDepth = parsePtr->numWords - 2;
	}
	TclEmitInstInt4(INST_OVER, tempDepth, envPtr);
    }

    /*
     * Emit code to load the variable's value.
     */

    if (!simpleVarName) {
	TclEmitOpcode(INST_LOAD_STK, envPtr);
    } else if (isScalar) {
	if (localIndex < 0) {
	    TclEmitOpcode(INST_LOAD_SCALAR_STK, envPtr);
	} else if (localIndex < 0x100) {
	    TclEmitInstInt1(INST_LOAD_SCALAR1, localIndex, envPtr);
	} else {
	    TclEmitInstInt4(INST_LOAD_SCALAR4, localIndex, envPtr);
	}
    } else {
	if (localIndex < 0) {
	    TclEmitOpcode(INST_LOAD_ARRAY_STK, envPtr);
	} else if (localIndex < 0x100) {
	    TclEmitInstInt1(INST_LOAD_ARRAY1, localIndex, envPtr);
	} else {
	    TclEmitInstInt4(INST_LOAD_ARRAY4, localIndex, envPtr);
	}
    }

    /*
     * Emit the correct variety of 'lset' instruction.
     */

    if (parsePtr->numWords == 4) {
	TclEmitOpcode(INST_LSET_LIST, envPtr);
    } else {
	TclEmitInstInt4(INST_LSET_FLAT, parsePtr->numWords-1, envPtr);
    }

    /*
     * Emit code to put the value back in the variable.
     */

    if (!simpleVarName) {
	TclEmitOpcode(INST_STORE_STK, envPtr);
    } else if (isScalar) {
	if (localIndex < 0) {
	    TclEmitOpcode(INST_STORE_SCALAR_STK, envPtr);
	} else if (localIndex < 0x100) {
	    TclEmitInstInt1(INST_STORE_SCALAR1, localIndex, envPtr);
	} else {
	    TclEmitInstInt4(INST_STORE_SCALAR4, localIndex, envPtr);
	}
    } else {
	if (localIndex < 0) {
	    TclEmitOpcode(INST_STORE_ARRAY_STK, envPtr);
	} else if (localIndex < 0x100) {
	    TclEmitInstInt1(INST_STORE_ARRAY1, localIndex, envPtr);
	} else {
	    TclEmitInstInt4(INST_STORE_ARRAY4, localIndex, envPtr);
	}
    }

    return TCL_OK;
}

/*
 *----------------------------------------------------------------------
 *
 * TclCompileRegexpCmd --
 *
 *	Procedure called to compile the "regexp" command.
 *
 * Results:
 * 	Returns TCL_OK for a successful compile. Returns TCL_ERROR to defer
 * 	evaluation to runtime.
 *
 * Side effects:
 *	Instructions are added to envPtr to execute the "regexp" command at
 *	runtime.
 *
 *----------------------------------------------------------------------
 */

int
TclCompileRegexpCmd(
    Tcl_Interp *interp,		/* Tcl interpreter for error reporting. */
    Tcl_Parse *parsePtr,	/* Points to a parse structure for the
				 * command. */
    Command *cmdPtr,		/* Points to defintion of command being
				 * compiled. */
    CompileEnv *envPtr)		/* Holds the resulting instructions. */
{
    Tcl_Token *varTokenPtr;	/* Pointer to the Tcl_Token representing the
				 * parse of the RE or string. */
    int i, len, nocase, exact, sawLast, simple;
    char *str;
    DefineLineInformation;	/* TIP #280 */

    /*
     * We are only interested in compiling simple regexp cases. Currently
     * supported compile cases are:
     *   regexp ?-nocase? ?--? staticString $var
     *   regexp ?-nocase? ?--? {^staticString$} $var
     */

    if (parsePtr->numWords < 3) {
	return TCL_ERROR;
    }

    simple = 0;
    nocase = 0;
    sawLast = 0;
    varTokenPtr = parsePtr->tokenPtr;

    /*
     * We only look for -nocase and -- as options. Everything else gets pushed
     * to runtime execution. This is different than regexp's runtime option
     * handling, but satisfies our stricter needs.
     */

    for (i = 1; i < parsePtr->numWords - 2; i++) {
	varTokenPtr = TokenAfter(varTokenPtr);
	if (varTokenPtr->type != TCL_TOKEN_SIMPLE_WORD) {
	    /*
	     * Not a simple string, so punt to runtime.
	     */

	    return TCL_ERROR;
	}
	str = (char *) varTokenPtr[1].start;
	len = varTokenPtr[1].size;
	if ((len == 2) && (str[0] == '-') && (str[1] == '-')) {
	    sawLast++;
	    i++;
	    break;
	} else if ((len > 1) && (strncmp(str,"-nocase",(unsigned)len) == 0)) {
	    nocase = 1;
	} else {
	    /*
	     * Not an option we recognize.
	     */

	    return TCL_ERROR;
	}
    }

    if ((parsePtr->numWords - i) != 2) {
	/*
	 * We don't support capturing to variables.
	 */

	return TCL_ERROR;
    }

    /*
     * Get the regexp string. If it is not a simple string or can't be
     * converted to a glob pattern, push the word for the INST_REGEXP.
     * Keep changes here in sync with TclCompileSwitchCmd Switch_Regexp.
     */

    varTokenPtr = TokenAfter(varTokenPtr);

    if (varTokenPtr->type == TCL_TOKEN_SIMPLE_WORD) {
	Tcl_DString ds;

	str = (char *) varTokenPtr[1].start;
	len = varTokenPtr[1].size;
	/*
	 * If it has a '-', it could be an incorrectly formed regexp command.
	 */

	if ((*str == '-') && !sawLast) {
	    return TCL_ERROR;
	}

	if (len == 0) {
	    /*
	     * The semantics of regexp are always match on re == "".
	     */

	    PushLiteral(envPtr, "1", 1);
	    return TCL_OK;
	}

	/*
	 * Attempt to convert pattern to glob.  If successful, push the
	 * converted pattern as a literal.
	 */

	if (TclReToGlob(NULL, varTokenPtr[1].start, len, &ds, &exact)
		== TCL_OK) {
	    simple = 1;
	    PushLiteral(envPtr, Tcl_DStringValue(&ds),Tcl_DStringLength(&ds));
	    Tcl_DStringFree(&ds);
	}
    }

    if (!simple) {
	CompileWord(envPtr, varTokenPtr, interp, parsePtr->numWords-2);
    }

    /*
     * Push the string arg.
     */

    varTokenPtr = TokenAfter(varTokenPtr);
    CompileWord(envPtr, varTokenPtr, interp, parsePtr->numWords-1);

    if (simple) {
	if (exact && !nocase) {
	    TclEmitOpcode(INST_STR_EQ, envPtr);
	} else {
	    TclEmitInstInt1(INST_STR_MATCH, nocase, envPtr);
	}
    } else {
	/*
	 * Pass correct RE compile flags.  We use only Int1 (8-bit), but
	 * that handles all the flags we want to pass.
	 * Don't use TCL_REG_NOSUB as we may have backrefs.
	 */
	int cflags = TCL_REG_ADVANCED | (nocase ? TCL_REG_NOCASE : 0);
	TclEmitInstInt1(INST_REGEXP, cflags, envPtr);
    }

    return TCL_OK;
}

/*
 *----------------------------------------------------------------------
 *
 * TclCompileReturnCmd --
 *
 *	Procedure called to compile the "return" command.
 *
 * Results:
 * 	Returns TCL_OK for a successful compile. Returns TCL_ERROR to defer
 * 	evaluation to runtime.
 *
 * Side effects:
 *	Instructions are added to envPtr to execute the "return" command at
 *	runtime.
 *
 *----------------------------------------------------------------------
 */

int
TclCompileReturnCmd(
    Tcl_Interp *interp,		/* Used for error reporting. */
    Tcl_Parse *parsePtr,	/* Points to a parse structure for the command
				 * created by Tcl_ParseCommand. */
    Command *cmdPtr,		/* Points to defintion of command being
				 * compiled. */
    CompileEnv *envPtr)		/* Holds resulting instructions. */
{
    /*
     * General syntax: [return ?-option value ...? ?result?]
     * An even number of words means an explicit result argument is present.
     */
    int level, code, objc, size, status = TCL_OK;
    int numWords = parsePtr->numWords;
    int explicitResult = (0 == (numWords % 2));
    int numOptionWords = numWords - 1 - explicitResult;
    Tcl_Obj *returnOpts, **objv;
    Tcl_Token *wordTokenPtr = TokenAfter(parsePtr->tokenPtr);
    DefineLineInformation;	/* TIP #280 */

    /*
     * Check for special case which can always be compiled:
     *	    return -options <opts> <msg>
     * Unlike the normal [return] compilation, this version does everything at
     * runtime so it can handle arbitrary words and not just literals. Note
     * that if INST_RETURN_STK wasn't already needed for something else
     * ('finally' clause processing) this piece of code would not be present.
     */

    if ((numWords == 4) && (wordTokenPtr->type == TCL_TOKEN_SIMPLE_WORD)
	    && (wordTokenPtr[1].size == 8)
	    && (strncmp(wordTokenPtr[1].start, "-options", 8) == 0)) {
	Tcl_Token *optsTokenPtr = TokenAfter(wordTokenPtr);
	Tcl_Token *msgTokenPtr = TokenAfter(optsTokenPtr);

	CompileWord(envPtr, optsTokenPtr, interp, 2);
	CompileWord(envPtr, msgTokenPtr,  interp, 3);
	TclEmitOpcode(INST_RETURN_STK, envPtr);
	return TCL_OK;
    }

    /*
     * Allocate some working space.
     */

    objv = (Tcl_Obj **) TclStackAlloc(interp,
	    numOptionWords * sizeof(Tcl_Obj *));

    /*
     * Scan through the return options. If any are unknown at compile time,
     * there is no value in bytecompiling. Save the option values known in an
     * objv array for merging into a return options dictionary.
     */

    for (objc = 0; objc < numOptionWords; objc++) {
	objv[objc] = Tcl_NewObj();
	Tcl_IncrRefCount(objv[objc]);
	if (!TclWordKnownAtCompileTime(wordTokenPtr, objv[objc])) {
	    objc++;
	    status = TCL_ERROR;
	    goto cleanup;
	}
	wordTokenPtr = TokenAfter(wordTokenPtr);
    }
    status = TclMergeReturnOptions(interp, objc, objv,
	    &returnOpts, &code, &level);
  cleanup:
    while (--objc >= 0) {
	TclDecrRefCount(objv[objc]);
    }
    TclStackFree(interp, objv);
    if (TCL_ERROR == status) {
	/*
	 * Something was bogus in the return options. Clear the error message,
	 * and report back to the compiler that this must be interpreted at
	 * runtime.
	 */

	Tcl_ResetResult(interp);
	return TCL_ERROR;
    }

    /*
     * All options are known at compile time, so we're going to bytecompile.
     * Emit instructions to push the result on the stack.
     */

    if (explicitResult) {
	 CompileWord(envPtr, wordTokenPtr, interp, numWords-1);
    } else {
	/*
	 * No explict result argument, so default result is empty string.
	 */

	PushLiteral(envPtr, "", 0);
    }

    /*
     * Check for optimization: When [return] is in a proc, and there's no
     * enclosing [catch], and there are no return options, then the INST_DONE
     * instruction is equivalent, and may be more efficient.
     */

    if (numOptionWords == 0 && envPtr->procPtr != NULL) {
	/*
	 * We have default return options and we're in a proc ...
	 */

	int index = envPtr->exceptArrayNext - 1;
	int enclosingCatch = 0;

	while (index >= 0) {
	    ExceptionRange range = envPtr->exceptArrayPtr[index];
	    if ((range.type == CATCH_EXCEPTION_RANGE)
		    && (range.catchOffset == -1)) {
		enclosingCatch = 1;
		break;
	    }
	    index--;
	}
	if (!enclosingCatch) {
	    /*
	     * ... and there is no enclosing catch. Issue the maximally
	     * efficient exit instruction.
	     */

	    Tcl_DecrRefCount(returnOpts);
	    TclEmitOpcode(INST_DONE, envPtr);
	    return TCL_OK;
	}
    }

    /* Optimize [return -level 0 $x]. */
    Tcl_DictObjSize(NULL, returnOpts, &size);
    if (size == 0 && level == 0 && code == TCL_OK) {
	Tcl_DecrRefCount(returnOpts);
	return TCL_OK;
    }

    /*
     * Could not use the optimization, so we push the return options dict, and
     * emit the INST_RETURN_IMM instruction with code and level as operands.
     */

    CompileReturnInternal(envPtr, INST_RETURN_IMM, code, level, returnOpts);
    return TCL_OK;
}

static void
CompileReturnInternal(
    CompileEnv *envPtr,
    unsigned char op,
    int code,
    int level,
    Tcl_Obj *returnOpts)
{
    TclEmitPush(TclAddLiteralObj(envPtr, returnOpts, NULL), envPtr);
    TclEmitInstInt4(op, code, envPtr);
    TclEmitInt4(level, envPtr);
}

void
TclCompileSyntaxError(
    Tcl_Interp *interp,
    CompileEnv *envPtr)
{
    Tcl_Obj *msg = Tcl_GetObjResult(interp);
    int numBytes;
    const char *bytes = TclGetStringFromObj(msg, &numBytes);

    TclEmitPush(TclRegisterNewLiteral(envPtr, bytes, numBytes), envPtr);
    CompileReturnInternal(envPtr, INST_SYNTAX, TCL_ERROR, 0,
	    Tcl_GetReturnOptions(interp, TCL_ERROR));
}

/*
 *----------------------------------------------------------------------
 *
 * TclCompileSetCmd --
 *
 *	Procedure called to compile the "set" command.
 *
 * Results:
 * 	Returns TCL_OK for a successful compile. Returns TCL_ERROR to defer
 * 	evaluation to runtime.
 *
 * Side effects:
 *	Instructions are added to envPtr to execute the "set" command at
 *	runtime.
 *
 *----------------------------------------------------------------------
 */

int
TclCompileSetCmd(
    Tcl_Interp *interp,		/* Used for error reporting. */
    Tcl_Parse *parsePtr,	/* Points to a parse structure for the command
				 * created by Tcl_ParseCommand. */
    Command *cmdPtr,		/* Points to defintion of command being
				 * compiled. */
    CompileEnv *envPtr)		/* Holds resulting instructions. */
{
    Tcl_Token *varTokenPtr, *valueTokenPtr;
    int isAssignment, isScalar, simpleVarName, localIndex, numWords;
    DefineLineInformation;	/* TIP #280 */

    numWords = parsePtr->numWords;
    if ((numWords != 2) && (numWords != 3)) {
	return TCL_ERROR;
    }
    isAssignment = (numWords == 3);

    /*
     * Decide if we can use a frame slot for the var/array name or if we need
     * to emit code to compute and push the name at runtime. We use a frame
     * slot (entry in the array of local vars) if we are compiling a procedure
     * body and if the name is simple text that does not include namespace
     * qualifiers.
     */

    varTokenPtr = TokenAfter(parsePtr->tokenPtr);
    PushVarName(interp, varTokenPtr, envPtr, TCL_CREATE_VAR,
		&localIndex, &simpleVarName, &isScalar,
		mapPtr->loc[eclIndex].line[1]);

    /*
     * If we are doing an assignment, push the new value.
     */

    if (isAssignment) {
	valueTokenPtr = TokenAfter(varTokenPtr);
	CompileWord(envPtr, valueTokenPtr, interp, 2);
    }

    /*
     * Emit instructions to set/get the variable.
     */

    if (simpleVarName) {
	if (isScalar) {
	    if (localIndex < 0) {
		TclEmitOpcode((isAssignment?
			INST_STORE_SCALAR_STK : INST_LOAD_SCALAR_STK), envPtr);
	    } else if (localIndex <= 255) {
		TclEmitInstInt1((isAssignment?
			INST_STORE_SCALAR1 : INST_LOAD_SCALAR1),
			localIndex, envPtr);
	    } else {
		TclEmitInstInt4((isAssignment?
			INST_STORE_SCALAR4 : INST_LOAD_SCALAR4),
			localIndex, envPtr);
	    }
	} else {
	    if (localIndex < 0) {
		TclEmitOpcode((isAssignment?
			INST_STORE_ARRAY_STK : INST_LOAD_ARRAY_STK), envPtr);
	    } else if (localIndex <= 255) {
		TclEmitInstInt1((isAssignment?
			INST_STORE_ARRAY1 : INST_LOAD_ARRAY1),
			localIndex, envPtr);
	    } else {
		TclEmitInstInt4((isAssignment?
			INST_STORE_ARRAY4 : INST_LOAD_ARRAY4),
			localIndex, envPtr);
	    }
	}
    } else {
	TclEmitOpcode((isAssignment? INST_STORE_STK : INST_LOAD_STK), envPtr);
    }

    return TCL_OK;
}

/*
 *----------------------------------------------------------------------
 *
 * TclCompileStringCmpCmd --
 *
 *	Procedure called to compile the simplest and most common form of the
 *	"string compare" command.
 *
 * Results:
 * 	Returns TCL_OK for a successful compile. Returns TCL_ERROR to defer
 * 	evaluation to runtime.
 *
 * Side effects:
 *	Instructions are added to envPtr to execute the "string compare"
 *	command at runtime.
 *
 *----------------------------------------------------------------------
 */

int
TclCompileStringCmpCmd(
    Tcl_Interp *interp,		/* Used for error reporting. */
    Tcl_Parse *parsePtr,	/* Points to a parse structure for the command
				 * created by Tcl_ParseCommand. */
    Command *cmdPtr,		/* Points to defintion of command being
				 * compiled. */
    CompileEnv *envPtr)		/* Holds resulting instructions. */
{
    DefineLineInformation;	/* TIP #280 */
    Tcl_Token *tokenPtr;

    /*
     * We don't support any flags; the bytecode isn't that sophisticated.
     */

    if (parsePtr->numWords != 3) {
	return TCL_ERROR;
    }

    /*
     * Push the two operands onto the stack and then the test.
     */

    tokenPtr = TokenAfter(parsePtr->tokenPtr);
    CompileWord(envPtr, tokenPtr, interp, 1);
    tokenPtr = TokenAfter(tokenPtr);
    CompileWord(envPtr, tokenPtr, interp, 2);
    TclEmitOpcode(INST_STR_CMP, envPtr);
    return TCL_OK;
}

/*
 *----------------------------------------------------------------------
 *
 * TclCompileStringEqualCmd --
 *
 *	Procedure called to compile the simplest and most common form of the
 *	"string equal" command.
 *
 * Results:
 * 	Returns TCL_OK for a successful compile. Returns TCL_ERROR to defer
 * 	evaluation to runtime.
 *
 * Side effects:
 *	Instructions are added to envPtr to execute the "string equal" command
 *	at runtime.
 *
 *----------------------------------------------------------------------
 */

int
TclCompileStringEqualCmd(
    Tcl_Interp *interp,		/* Used for error reporting. */
    Tcl_Parse *parsePtr,	/* Points to a parse structure for the command
				 * created by Tcl_ParseCommand. */
    Command *cmdPtr,		/* Points to defintion of command being
				 * compiled. */
    CompileEnv *envPtr)		/* Holds resulting instructions. */
{
    DefineLineInformation;	/* TIP #280 */
    Tcl_Token *tokenPtr;

    /*
     * We don't support any flags; the bytecode isn't that sophisticated.
     */

    if (parsePtr->numWords != 3) {
	return TCL_ERROR;
    }

    /*
     * Push the two operands onto the stack and then the test.
     */

    tokenPtr = TokenAfter(parsePtr->tokenPtr);
    CompileWord(envPtr, tokenPtr, interp, 1);
    tokenPtr = TokenAfter(tokenPtr);
    CompileWord(envPtr, tokenPtr, interp, 2);
    TclEmitOpcode(INST_STR_EQ, envPtr);
    return TCL_OK;
}

/*
 *----------------------------------------------------------------------
 *
 * TclCompileStringIndexCmd --
 *
 *	Procedure called to compile the simplest and most common form of the
 *	"string index" command.
 *
 * Results:
 * 	Returns TCL_OK for a successful compile. Returns TCL_ERROR to defer
 * 	evaluation to runtime.
 *
 * Side effects:
 *	Instructions are added to envPtr to execute the "string index" command
 *	at runtime.
 *
 *----------------------------------------------------------------------
 */

int
TclCompileStringIndexCmd(
    Tcl_Interp *interp,		/* Used for error reporting. */
    Tcl_Parse *parsePtr,	/* Points to a parse structure for the command
				 * created by Tcl_ParseCommand. */
    Command *cmdPtr,		/* Points to defintion of command being
				 * compiled. */
    CompileEnv *envPtr)		/* Holds resulting instructions. */
{
    DefineLineInformation;	/* TIP #280 */
    Tcl_Token *tokenPtr;

    if (parsePtr->numWords != 3) {
	return TCL_ERROR;
    }

    /*
     * Push the two operands onto the stack and then the index operation.
     */

    tokenPtr = TokenAfter(parsePtr->tokenPtr);
    CompileWord(envPtr, tokenPtr, interp, 1);
    tokenPtr = TokenAfter(tokenPtr);
    CompileWord(envPtr, tokenPtr, interp, 2);
    TclEmitOpcode(INST_STR_INDEX, envPtr);
    return TCL_OK;
}

/*
 *----------------------------------------------------------------------
 *
 * TclCompileStringMatchCmd --
 *
 *	Procedure called to compile the simplest and most common form of the
 *	"string match" command.
 *
 * Results:
 * 	Returns TCL_OK for a successful compile. Returns TCL_ERROR to defer
 * 	evaluation to runtime.
 *
 * Side effects:
 *	Instructions are added to envPtr to execute the "string match" command
 *	at runtime.
 *
 *----------------------------------------------------------------------
 */

int
TclCompileStringMatchCmd(
    Tcl_Interp *interp,		/* Used for error reporting. */
    Tcl_Parse *parsePtr,	/* Points to a parse structure for the command
				 * created by Tcl_ParseCommand. */
    Command *cmdPtr,		/* Points to defintion of command being
				 * compiled. */
    CompileEnv *envPtr)		/* Holds resulting instructions. */
{
    DefineLineInformation;	/* TIP #280 */
    Tcl_Token *tokenPtr;
    int i, length, exactMatch = 0, nocase = 0;
    const char *str;

    if (parsePtr->numWords < 3 || parsePtr->numWords > 4) {
	return TCL_ERROR;
    }
    tokenPtr = TokenAfter(parsePtr->tokenPtr);

    /*
     * Check if we have a -nocase flag.
     */

    if (parsePtr->numWords == 4) {
	if (tokenPtr->type != TCL_TOKEN_SIMPLE_WORD) {
	    return TCL_ERROR;
	}
	str = tokenPtr[1].start;
	length = tokenPtr[1].size;
	if ((length <= 1) || strncmp(str, "-nocase", (size_t) length)) {
	    /*
	     * Fail at run time, not in compilation.
	     */

	    return TCL_ERROR;
	}
	nocase = 1;
	tokenPtr = TokenAfter(tokenPtr);
    }

    /*
     * Push the strings to match against each other.
     */

    for (i = 0; i < 2; i++) {
	if (tokenPtr->type == TCL_TOKEN_SIMPLE_WORD) {
	    str = tokenPtr[1].start;
	    length = tokenPtr[1].size;
	    if (!nocase && (i == 0)) {
		/*
		 * Trivial matches can be done by 'string equal'. If -nocase
		 * was specified, we can't do this because INST_STR_EQ has no
		 * support for nocase.
		 */

		Tcl_Obj *copy = Tcl_NewStringObj(str, length);

		Tcl_IncrRefCount(copy);
		exactMatch = TclMatchIsTrivial(TclGetString(copy));
		TclDecrRefCount(copy);
	    }
	    PushLiteral(envPtr, str, length);
	} else {
	    envPtr->line = mapPtr->loc[eclIndex].line[i+1+nocase];
	    CompileTokens(envPtr, tokenPtr, interp);
	}
	tokenPtr = TokenAfter(tokenPtr);
    }

    /*
     * Push the matcher.
     */

    if (exactMatch) {
	TclEmitOpcode(INST_STR_EQ, envPtr);
    } else {
	TclEmitInstInt1(INST_STR_MATCH, nocase, envPtr);
    }
    return TCL_OK;
}

/*
 *----------------------------------------------------------------------
 *
 * TclCompileStringLenCmd --
 *
 *	Procedure called to compile the simplest and most common form of the
 *	"string length" command.
 *
 * Results:
 * 	Returns TCL_OK for a successful compile. Returns TCL_ERROR to defer
 * 	evaluation to runtime.
 *
 * Side effects:
 *	Instructions are added to envPtr to execute the "string length"
 *	command at runtime.
 *
 *----------------------------------------------------------------------
 */

int
TclCompileStringLenCmd(
    Tcl_Interp *interp,		/* Used for error reporting. */
    Tcl_Parse *parsePtr,	/* Points to a parse structure for the command
				 * created by Tcl_ParseCommand. */
    Command *cmdPtr,		/* Points to defintion of command being
				 * compiled. */
    CompileEnv *envPtr)		/* Holds resulting instructions. */
{
    DefineLineInformation;	/* TIP #280 */
    Tcl_Token *tokenPtr;

    if (parsePtr->numWords != 2) {
	return TCL_ERROR;
    }

    tokenPtr = TokenAfter(parsePtr->tokenPtr);
    if (tokenPtr->type == TCL_TOKEN_SIMPLE_WORD) {
	/*
	 * Here someone is asking for the length of a static string. Just push
	 * the actual character (not byte) length.
	 */

	char buf[TCL_INTEGER_SPACE];
	int len = Tcl_NumUtfChars(tokenPtr[1].start, tokenPtr[1].size);

	len = sprintf(buf, "%d", len);
	PushLiteral(envPtr, buf, len);
    } else {
	envPtr->line = mapPtr->loc[eclIndex].line[1];
	CompileTokens(envPtr, tokenPtr, interp);
	TclEmitOpcode(INST_STR_LEN, envPtr);
    }
    return TCL_OK;
}

/*
 *----------------------------------------------------------------------
 *
 * TclCompileSwitchCmd --
 *
 *	Procedure called to compile the "switch" command.
 *
 * Results:
 * 	Returns TCL_OK for successful compile, or TCL_ERROR to defer
 * 	evaluation to runtime (either when it is too complex to get the
 * 	semantics right, or when we know for sure that it is an error but need
 * 	the error to happen at the right time).
 *
 * Side effects:
 *	Instructions are added to envPtr to execute the "switch" command at
 *	runtime.
 *
 * FIXME:
 *	Stack depths are probably not calculated correctly.
 *
 *----------------------------------------------------------------------
 */

int
TclCompileSwitchCmd(
    Tcl_Interp *interp,		/* Used for error reporting. */
    Tcl_Parse *parsePtr,	/* Points to a parse structure for the command
				 * created by Tcl_ParseCommand. */
    Command *cmdPtr,		/* Points to defintion of command being
				 * compiled. */
    CompileEnv *envPtr)		/* Holds resulting instructions. */
{
    Tcl_Token *tokenPtr;	/* Pointer to tokens in command. */
    int numWords;		/* Number of words in command. */

    Tcl_Token *valueTokenPtr;	/* Token for the value to switch on. */
    enum {Switch_Exact, Switch_Glob, Switch_Regexp} mode;
				/* What kind of switch are we doing? */

    Tcl_Token *bodyTokenArray;	/* Array of real pattern list items. */
    Tcl_Token **bodyToken;	/* Array of pointers to pattern list items. */
    int *bodyLines;		/* Array of line numbers for body list
				 * items. */
    int foundDefault;		/* Flag to indicate whether a "default" clause
				 * is present. */

    JumpFixup *fixupArray;	/* Array of forward-jump fixup records. */
    int *fixupTargetArray;	/* Array of places for fixups to point at. */
    int fixupCount;		/* Number of places to fix up. */
    int contFixIndex;		/* Where the first of the jumps due to a group
				 * of continuation bodies starts, or -1 if
				 * there aren't any. */
    int contFixCount;		/* Number of continuation bodies pointing to
				 * the current (or next) real body. */

    int savedStackDepth = envPtr->currStackDepth;
    int noCase;			/* Has the -nocase flag been given? */
    int foundMode = 0;		/* Have we seen a mode flag yet? */
    int isListedArms = 0;
    int i, valueIndex;
    DefineLineInformation;	/* TIP #280 */

    /*
     * Only handle the following versions:
     *   switch         ?--? word {pattern body ...}
     *   switch -exact  ?--? word {pattern body ...}
     *   switch -glob   ?--? word {pattern body ...}
     *   switch -regexp ?--? word {pattern body ...}
     *   switch         --   word simpleWordPattern simpleWordBody ...
     *   switch -exact  --   word simpleWordPattern simpleWordBody ...
     *   switch -glob   --   word simpleWordPattern simpleWordBody ...
     *   switch -regexp --   word simpleWordPattern simpleWordBody ...
     * When the mode is -glob, can also handle a -nocase flag.
     *
     * First off, we don't care how the command's word was generated; we're
     * compiling it anyway! So skip it...
     */

    tokenPtr = TokenAfter(parsePtr->tokenPtr);
    valueIndex = 1;
    numWords = parsePtr->numWords-1;

    /*
     * Check for options.
     */

    noCase = 0;
    mode = Switch_Exact;
    if (numWords == 2) {
	/*
	 * There's just the switch value and the bodies list. In that case, we
	 * can skip all option parsing and move on to consider switch values
	 * and the body list.
	 */

	goto finishedOptionParse;
    }

    /*
     * There must be at least one option, --, because without that there is no
     * way to statically avoid the problems you get from strings-to-be-matched
     * that start with a - (the interpreted code falls apart if it encounters
     * them, so we punt if we *might* encounter them as that is the easiest
     * way of emulating the behaviour).
     */

    for (; numWords>=3 ; tokenPtr=TokenAfter(tokenPtr),numWords--) {
	register unsigned size = tokenPtr[1].size;
	register const char *chrs = tokenPtr[1].start;

	/*
	 * We only process literal options, and we assume that -e, -g and -n
	 * are unique prefixes of -exact, -glob and -nocase respectively (true
	 * at time of writing). Note that -exact and -glob may only be given
	 * at most once or we bail out (error case).
	 */

	if (tokenPtr->type != TCL_TOKEN_SIMPLE_WORD || size < 2) {
	    return TCL_ERROR;
	}

	if ((size <= 6) && !memcmp(chrs, "-exact", size)) {
	    if (foundMode) {
		return TCL_ERROR;
	    }
	    mode = Switch_Exact;
	    foundMode = 1;
	    valueIndex++;
	    continue;
	} else if ((size <= 5) && !memcmp(chrs, "-glob", size)) {
	    if (foundMode) {
		return TCL_ERROR;
	    }
	    mode = Switch_Glob;
	    foundMode = 1;
	    valueIndex++;
	    continue;
	} else if ((size <= 7) && !memcmp(chrs, "-regexp", size)) {
	    if (foundMode) {
		return TCL_ERROR;
	    }
	    mode = Switch_Regexp;
	    foundMode = 1;
	    valueIndex++;
	    continue;
	} else if ((size <= 7) && !memcmp(chrs, "-nocase", size)) {
	    noCase = 1;
	    valueIndex++;
	    continue;
	} else if ((size == 2) && !memcmp(chrs, "--", 2)) {
	    valueIndex++;
	    break;
	}

	/*
	 * The switch command has many flags we cannot compile at all (e.g.
	 * all the RE-related ones) which we must have encountered. Either
	 * that or we have run off the end. The action here is the same: punt
	 * to interpreted version.
	 */

	return TCL_ERROR;
    }
    if (numWords < 3) {
	return TCL_ERROR;
    }
    tokenPtr = TokenAfter(tokenPtr);
    numWords--;
    if (noCase && (mode == Switch_Exact)) {
	/*
	 * Can't compile this case; no opcode for case-insensitive equality!
	 */

	return TCL_ERROR;
    }

    /*
     * The value to test against is going to always get pushed on the stack.
     * But not yet; we need to verify that the rest of the command is
     * compilable too.
     */

  finishedOptionParse:
    valueTokenPtr = tokenPtr;
    /* For valueIndex, see previous loop. */
    tokenPtr = TokenAfter(tokenPtr);
    numWords--;

    /*
     * Build an array of tokens for the matcher terms and script bodies. Note
     * that in the case of the quoted bodies, this is tricky as we cannot use
     * copies of the string from the input token for the generated tokens (it
     * causes a crash during exception handling). When multiple tokens are
     * available at this point, this is pretty easy.
     */

    if (numWords == 1) {
	Tcl_DString bodyList;
	const char **argv = NULL, *tokenStartPtr, *p;
	int bline;		/* TIP #280: line of the pattern/action list,
				 * and start of list for when tracking the
				 * location. This list comes immediately after
				 * the value we switch on. */
	int isTokenBraced;

	/*
	 * Test that we've got a suitable body list as a simple (i.e. braced)
	 * word, and that the elements of the body are simple words too. This
	 * is really rather nasty indeed.
	 */

	if (tokenPtr->type != TCL_TOKEN_SIMPLE_WORD) {
	    return TCL_ERROR;
	}

	Tcl_DStringInit(&bodyList);
	Tcl_DStringAppend(&bodyList, tokenPtr[1].start, tokenPtr[1].size);
	if (Tcl_SplitList(NULL, Tcl_DStringValue(&bodyList), &numWords,
		&argv) != TCL_OK) {
	    Tcl_DStringFree(&bodyList);
	    return TCL_ERROR;
	}
	Tcl_DStringFree(&bodyList);

	/*
	 * Now we know what the switch arms are, we've got to see whether we
	 * can synthesize tokens for the arms. First check whether we've got a
	 * valid number of arms since we can do that now.
	 */

	if (numWords == 0 || numWords % 2) {
	    ckfree((char *) argv);
	    return TCL_ERROR;
	}

	isListedArms = 1;
	bodyTokenArray = (Tcl_Token *) ckalloc(sizeof(Tcl_Token) * numWords);
	bodyToken = (Tcl_Token **) ckalloc(sizeof(Tcl_Token *) * numWords);
	bodyLines = (int *) ckalloc(sizeof(int) * numWords);

	/*
	 * Locate the start of the arms within the overall word.
	 */

	bline = mapPtr->loc[eclIndex].line[valueIndex+1];
	p = tokenStartPtr = tokenPtr[1].start;
	while (isspace(UCHAR(*tokenStartPtr))) {
	    tokenStartPtr++;
	}
	if (*tokenStartPtr == '{') {
	    tokenStartPtr++;
	    isTokenBraced = 1;
	} else {
	    isTokenBraced = 0;
	}

	/*
	 * TIP #280: Count lines within the literal list.
	 */

	for (i=0 ; i<numWords ; i++) {
	    bodyTokenArray[i].type = TCL_TOKEN_TEXT;
	    bodyTokenArray[i].start = tokenStartPtr;
	    bodyTokenArray[i].size = strlen(argv[i]);
	    bodyTokenArray[i].numComponents = 0;
	    bodyToken[i] = bodyTokenArray+i;
	    tokenStartPtr += bodyTokenArray[i].size;

	    /*
	     * Test to see if we have guessed the end of the word correctly;
	     * if not, we can't feed the real string to the sub-compilation
	     * engine, and we're then stuck and so have to punt out to doing
	     * everything at runtime.
	     */

	    if ((isTokenBraced && *(tokenStartPtr++) != '}') ||
		    (tokenStartPtr < tokenPtr[1].start+tokenPtr[1].size
		    && !isspace(UCHAR(*tokenStartPtr)))) {
		ckfree((char *) argv);
		ckfree((char *) bodyToken);
		ckfree((char *) bodyTokenArray);
		ckfree((char *) bodyLines);
		return TCL_ERROR;
	    }

	    /*
	     * TIP #280: Now determine the line the list element starts on
	     * (there is no need to do it earlier, due to the possibility of
	     * aborting, see above).
	     */

	    TclAdvanceLines(&bline, p, bodyTokenArray[i].start);
	    bodyLines[i] = bline;
	    p = bodyTokenArray[i].start;

	    while (isspace(UCHAR(*tokenStartPtr))) {
		tokenStartPtr++;
		if (tokenStartPtr >= tokenPtr[1].start+tokenPtr[1].size) {
		    break;
		}
	    }
	    if (*tokenStartPtr == '{') {
		tokenStartPtr++;
		isTokenBraced = 1;
	    } else {
		isTokenBraced = 0;
	    }
	}
	ckfree((char *) argv);

	/*
	 * Check that we've parsed everything we thought we were going to
	 * parse. If not, something odd is going on (I believe it is possible
	 * to defeat the code above) and we should bail out.
	 */

	if (tokenStartPtr != tokenPtr[1].start+tokenPtr[1].size) {
	    ckfree((char *) bodyToken);
	    ckfree((char *) bodyTokenArray);
	    ckfree((char *) bodyLines);
	    return TCL_ERROR;
	}

    } else if (numWords % 2 || numWords == 0) {
	/*
	 * Odd number of words (>1) available, or no words at all available.
	 * Both are error cases, so punt and let the interpreted-version
	 * generate the error message. Note that the second case probably
	 * should get caught earlier, but it's easy to check here again anyway
	 * because it'd cause a nasty crash otherwise.
	 */

	return TCL_ERROR;
    } else {
	/*
	 * Multi-word definition of patterns & actions.
	 */

	bodyToken = (Tcl_Token **) ckalloc(sizeof(Tcl_Token *) * numWords);
	bodyLines = (int *) ckalloc(sizeof(int) * numWords);
	bodyTokenArray = NULL;
	for (i=0 ; i<numWords ; i++) {
	    /*
	     * We only handle the very simplest case. Anything more complex is
	     * a good reason to go to the interpreted case anyway due to
	     * traces, etc.
	     */

	    if (tokenPtr->type != TCL_TOKEN_SIMPLE_WORD ||
		    tokenPtr->numComponents != 1) {
		ckfree((char *) bodyToken);
		ckfree((char *) bodyLines);
		return TCL_ERROR;
	    }
	    bodyToken[i] = tokenPtr+1;

	    /*
	     * TIP #280: Copy line information from regular cmd info.
	     */

	    bodyLines[i] = mapPtr->loc[eclIndex].line[valueIndex+1+i];
	    tokenPtr = TokenAfter(tokenPtr);
	}
    }

    /*
     * Fall back to interpreted if the last body is a continuation (it's
     * illegal, but this makes the error happen at the right time).
     */

    if (bodyToken[numWords-1]->size == 1 &&
	    bodyToken[numWords-1]->start[0] == '-') {
	ckfree((char *) bodyToken);
	ckfree((char *) bodyLines);
	if (bodyTokenArray != NULL) {
	    ckfree((char *) bodyTokenArray);
	}
	return TCL_ERROR;
    }

    /*
     * Now we commit to generating code; the parsing stage per se is done.
     * First, we push the value we're matching against on the stack.
     */

    envPtr->line = mapPtr->loc[eclIndex].line[valueIndex];
    CompileTokens(envPtr, valueTokenPtr, interp);

    /*
     * Check if we can generate a jump table, since if so that's faster than
     * doing an explicit compare with each body. Note that we're definitely
     * over-conservative with determining whether we can do the jump table,
     * but it handles the most common case well enough.
     */

    if (isListedArms && mode == Switch_Exact && !noCase) {
	JumptableInfo *jtPtr;
	int infoIndex, isNew, *finalFixups, numRealBodies = 0, jumpLocation;
	int mustGenerate, jumpToDefault;
	Tcl_DString buffer;
	Tcl_HashEntry *hPtr;

	/*
	 * Compile the switch by using a jump table, which is basically a
	 * hashtable that maps from literal values to match against to the
	 * offset (relative to the INST_JUMP_TABLE instruction) to jump to.
	 * The jump table itself is independent of any invokation of the
	 * bytecode, and as such is stored in an auxData block.
	 *
	 * Start by allocating the jump table itself, plus some workspace.
	 */

	jtPtr = (JumptableInfo *) ckalloc(sizeof(JumptableInfo));
	Tcl_InitHashTable(&jtPtr->hashTable, TCL_STRING_KEYS);
	infoIndex = TclCreateAuxData(jtPtr, &tclJumptableInfoType, envPtr);
	finalFixups = (int *) ckalloc(sizeof(int) * (numWords/2));
	foundDefault = 0;
	mustGenerate = 1;

	/*
	 * Next, issue the instruction to do the jump, together with what we
	 * want to do if things do not work out (jump to either the default
	 * clause or the "default" default, which just sets the result to
	 * empty). Note that we will come back and rewrite the jump's offset
	 * parameter when we know what it should be, and that all jumps we
	 * issue are of the wide kind because that makes the code much easier
	 * to debug!
	 */

	jumpLocation = CurrentOffset(envPtr);
	TclEmitInstInt4(INST_JUMP_TABLE, infoIndex, envPtr);
	jumpToDefault = CurrentOffset(envPtr);
	TclEmitInstInt4(INST_JUMP4, 0, envPtr);

	for (i=0 ; i<numWords ; i+=2) {
	    /*
	     * For each arm, we must first work out what to do with the match
	     * term.
	     */

	    if (i!=numWords-2 || bodyToken[numWords-2]->size != 7 ||
		    memcmp(bodyToken[numWords-2]->start, "default", 7)) {
		/*
		 * This is not a default clause, so insert the current
		 * location as a target in the jump table (assuming it isn't
		 * already there, which would indicate that this clause is
		 * probably masked by an earlier one). Note that we use a
		 * Tcl_DString here simply because the hash API does not let
		 * us specify the string length.
		 */

		Tcl_DStringInit(&buffer);
		Tcl_DStringAppend(&buffer, bodyToken[i]->start,
			bodyToken[i]->size);
		hPtr = Tcl_CreateHashEntry(&jtPtr->hashTable,
			Tcl_DStringValue(&buffer), &isNew);
		if (isNew) {
		    /*
		     * First time we've encountered this match clause, so it
		     * must point to here.
		     */

		    Tcl_SetHashValue(hPtr, (ClientData)
			    (CurrentOffset(envPtr) - jumpLocation));
		}
		Tcl_DStringFree(&buffer);
	    } else {
		/*
		 * This is a default clause, so patch up the fallthrough from
		 * the INST_JUMP_TABLE instruction to here.
		 */

		foundDefault = 1;
		isNew = 1;
		TclStoreInt4AtPtr(CurrentOffset(envPtr)-jumpToDefault,
			envPtr->codeStart+jumpToDefault+1);
	    }

	    /*
	     * Now, for each arm we must deal with the body of the clause.
	     *
	     * If this is a continuation body (never true of a final clause,
	     * whether default or not) we're done because the next jump target
	     * will also point here, so we advance to the next clause.
	     */

	    if (bodyToken[i+1]->size == 1 && bodyToken[i+1]->start[0] == '-') {
		mustGenerate = 1;
		continue;
	    }

	    /*
	     * Also skip this arm if its only match clause is masked. (We
	     * could probably be more aggressive about this, but that would be
	     * much more difficult to get right.)
	     */

	    if (!isNew && !mustGenerate) {
		continue;
	    }
	    mustGenerate = 0;

	    /*
	     * Compile the body of the arm.
	     */

	    envPtr->line = bodyLines[i+1];	/* TIP #280 */
	    TclCompileCmdWord(interp, bodyToken[i+1], 1, envPtr);

	    /*
	     * Compile a jump in to the end of the command if this body is
	     * anything other than a user-supplied default arm (to either skip
	     * over the remaining bodies or the code that generates an empty
	     * result).
	     */

	    if (i+2 < numWords || !foundDefault) {
		finalFixups[numRealBodies++] = CurrentOffset(envPtr);

		/*
		 * Easier by far to issue this jump as a fixed-width jump.
		 * Otherwise we'd need to do a lot more (and more awkward)
		 * rewriting when we fixed this all up.
		 */

		TclEmitInstInt4(INST_JUMP4, 0, envPtr);
	    }
	}

	/*
	 * We're at the end. If we've not already done so through the
	 * processing of a user-supplied default clause, add in a "default"
	 * default clause now.
	 */

	if (!foundDefault) {
	    TclStoreInt4AtPtr(CurrentOffset(envPtr)-jumpToDefault,
		    envPtr->codeStart+jumpToDefault+1);
	    PushLiteral(envPtr, "", 0);
	}

	/*
	 * No more instructions to be issued; everything that needs to jump to
	 * the end of the command is fixed up at this point.
	 */

	for (i=0 ; i<numRealBodies ; i++) {
	    TclStoreInt4AtPtr(CurrentOffset(envPtr)-finalFixups[i],
		    envPtr->codeStart+finalFixups[i]+1);
	}

	/*
	 * Clean up all our temporary space and return.
	 */

	ckfree((char *) finalFixups);
	ckfree((char *) bodyToken);
	ckfree((char *) bodyLines);
	if (bodyTokenArray != NULL) {
	    ckfree((char *) bodyTokenArray);
	}
	return TCL_OK;
    }

    /*
     * Generate a test for each arm.
     */

    contFixIndex = -1;
    contFixCount = 0;
    fixupArray = (JumpFixup *) ckalloc(sizeof(JumpFixup) * numWords);
    fixupTargetArray = (int *) ckalloc(sizeof(int) * numWords);
    memset(fixupTargetArray, 0, numWords * sizeof(int));
    fixupCount = 0;
    foundDefault = 0;
    for (i=0 ; i<numWords ; i+=2) {
	int nextArmFixupIndex = -1;

	envPtr->currStackDepth = savedStackDepth + 1;
	if (i!=numWords-2 || bodyToken[numWords-2]->size != 7 ||
		memcmp(bodyToken[numWords-2]->start, "default", 7)) {
	    /*
	     * Generate the test for the arm.
	     */

	    switch (mode) {
	    case Switch_Exact:
		TclEmitOpcode(INST_DUP, envPtr);
		TclCompileTokens(interp, bodyToken[i], 1, envPtr);
		TclEmitOpcode(INST_STR_EQ, envPtr);
		break;
	    case Switch_Glob:
		TclCompileTokens(interp, bodyToken[i], 1, envPtr);
		TclEmitInstInt4(INST_OVER, 1, envPtr);
		TclEmitInstInt1(INST_STR_MATCH, noCase, envPtr);
		break;
	    case Switch_Regexp: {
		int simple = 0, exact = 0;

		/*
		 * Keep in sync with TclCompileRegexpCmd.
		 */

		if (bodyToken[i]->type == TCL_TOKEN_TEXT) {
		    Tcl_DString ds;

		    if (bodyToken[i]->size == 0) {
			/*
			 * The semantics of regexps are that they always match
			 * when the RE == "".
			 */

			PushLiteral(envPtr, "1", 1);
			break;
		    }

		    /*
		     * Attempt to convert pattern to glob. If successful, push
		     * the converted pattern.
		     */

		    if (TclReToGlob(NULL, bodyToken[i]->start,
			    bodyToken[i]->size, &ds, &exact) == TCL_OK) {
			simple = 1;
			PushLiteral(envPtr, Tcl_DStringValue(&ds),
				Tcl_DStringLength(&ds));
			Tcl_DStringFree(&ds);
		    }
		}
		if (!simple) {
		    TclCompileTokens(interp, bodyToken[i], 1, envPtr);
		}

		TclEmitInstInt4(INST_OVER, 1, envPtr);
		if (simple) {
		    if (exact && !noCase) {
			TclEmitOpcode(INST_STR_EQ, envPtr);
		    } else {
			TclEmitInstInt1(INST_STR_MATCH, noCase, envPtr);
		    }
		} else {
		    /*
		     * Pass correct RE compile flags. We use only Int1
		     * (8-bit), but that handles all the flags we want to
		     * pass. Don't use TCL_REG_NOSUB as we may have backrefs
		     * or capture vars.
		     */

		    int cflags = TCL_REG_ADVANCED
			    | (noCase ? TCL_REG_NOCASE : 0);

		    TclEmitInstInt1(INST_REGEXP, cflags, envPtr);
		}
		break;
	    }
	    default:
		Tcl_Panic("unknown switch mode: %d", mode);
	    }

	    /*
	     * In a fall-through case, we will jump on _true_ to the place
	     * where the body starts (generated later, with guarantee of this
	     * ensured earlier; the final body is never a fall-through).
	     */

	    if (bodyToken[i+1]->size==1 && bodyToken[i+1]->start[0]=='-') {
		if (contFixIndex == -1) {
		    contFixIndex = fixupCount;
		    contFixCount = 0;
		}
		TclEmitForwardJump(envPtr, TCL_TRUE_JUMP,
			fixupArray+contFixIndex+contFixCount);
		fixupCount++;
		contFixCount++;
		continue;
	    }

	    TclEmitForwardJump(envPtr, TCL_FALSE_JUMP, fixupArray+fixupCount);
	    nextArmFixupIndex = fixupCount;
	    fixupCount++;
	} else {
	    /*
	     * Got a default clause; set a flag to inhibit the generation of
	     * the jump after the body and the cleanup of the intermediate
	     * value that we are switching against.
	     *
	     * Note that default clauses (which are always terminal clauses)
	     * cannot be fall-through clauses as well, since the last clause
	     * is never a fall-through clause (which we have already
	     * verified).
	     */

	    foundDefault = 1;
	}

	/*
	 * Generate the body for the arm. This is guaranteed not to be a
	 * fall-through case, but it might have preceding fall-through cases,
	 * so we must process those first.
	 */

	if (contFixIndex != -1) {
	    int j;

	    for (j=0 ; j<contFixCount ; j++) {
		fixupTargetArray[contFixIndex+j] = CurrentOffset(envPtr);
	    }
	    contFixIndex = -1;
	}

	/*
	 * Now do the actual compilation. Note that we do not use CompileBody
	 * because we may have synthesized the tokens in a non-standard
	 * pattern.
	 */

	TclEmitOpcode(INST_POP, envPtr);
	envPtr->currStackDepth = savedStackDepth + 1;
	envPtr->line = bodyLines[i+1];		/* TIP #280 */
	TclCompileCmdWord(interp, bodyToken[i+1], 1, envPtr);

	if (!foundDefault) {
	    TclEmitForwardJump(envPtr, TCL_UNCONDITIONAL_JUMP,
		    fixupArray+fixupCount);
	    fixupCount++;
	    fixupTargetArray[nextArmFixupIndex] = CurrentOffset(envPtr);
	}
    }

    /*
     * Clean up all our temporary space and return.
     */

    ckfree((char *) bodyToken);
    ckfree((char *) bodyLines);
    if (bodyTokenArray != NULL) {
	ckfree((char *) bodyTokenArray);
    }

    /*
     * Discard the value we are matching against unless we've had a default
     * clause (in which case it will already be gone due to the code at the
     * start of processing an arm, guaranteed) and make the result of the
     * command an empty string.
     */

    if (!foundDefault) {
	TclEmitOpcode(INST_POP, envPtr);
	PushLiteral(envPtr, "", 0);
    }

    /*
     * Do jump fixups for arms that were executed. First, fill in the jumps of
     * all jumps that don't point elsewhere to point to here.
     */

    for (i=0 ; i<fixupCount ; i++) {
	if (fixupTargetArray[i] == 0) {
	    fixupTargetArray[i] = envPtr->codeNext-envPtr->codeStart;
	}
    }

    /*
     * Now scan backwards over all the jumps (all of which are forward jumps)
     * doing each one. When we do one and there is a size changes, we must
     * scan back over all the previous ones and see if they need adjusting
     * before proceeding with further jump fixups (the interleaved nature of
     * all the jumps makes this impossible to do without nested loops).
     */

    for (i=fixupCount-1 ; i>=0 ; i--) {
	if (TclFixupForwardJump(envPtr, &fixupArray[i],
		fixupTargetArray[i] - fixupArray[i].codeOffset, 127)) {
	    int j;

	    for (j=i-1 ; j>=0 ; j--) {
		if (fixupTargetArray[j] > fixupArray[i].codeOffset) {
		    fixupTargetArray[j] += 3;
		}
	    }
	}
    }
    ckfree((char *) fixupArray);
    ckfree((char *) fixupTargetArray);

    envPtr->currStackDepth = savedStackDepth + 1;
    return TCL_OK;
}

/*
 *----------------------------------------------------------------------
 *
 * DupJumptableInfo, FreeJumptableInfo --
 *
 *	Functions to duplicate, release and print a jump-table created for use
 *	with the INST_JUMP_TABLE instruction.
 *
 * Results:
 *	DupJumptableInfo: a copy of the jump-table
 *	FreeJumptableInfo: none
 *	PrintJumptableInfo: none
 *
 * Side effects:
 *	DupJumptableInfo: allocates memory
 *	FreeJumptableInfo: releases memory
 *	PrintJumptableInfo: none
 *
 *----------------------------------------------------------------------
 */

static ClientData
DupJumptableInfo(
    ClientData clientData)
{
    JumptableInfo *jtPtr = clientData;
    JumptableInfo *newJtPtr = (JumptableInfo *)
	    ckalloc(sizeof(JumptableInfo));
    Tcl_HashEntry *hPtr, *newHPtr;
    Tcl_HashSearch search;
    int isNew;

    Tcl_InitHashTable(&newJtPtr->hashTable, TCL_STRING_KEYS);
    hPtr = Tcl_FirstHashEntry(&jtPtr->hashTable, &search);
    while (hPtr != NULL) {
	newHPtr = Tcl_CreateHashEntry(&newJtPtr->hashTable,
		Tcl_GetHashKey(&jtPtr->hashTable, hPtr), &isNew);
	Tcl_SetHashValue(newHPtr, Tcl_GetHashValue(hPtr));
    }
    return newJtPtr;
}

static void
FreeJumptableInfo(
    ClientData clientData)
{
    JumptableInfo *jtPtr = clientData;

    Tcl_DeleteHashTable(&jtPtr->hashTable);
    ckfree((char *) jtPtr);
}

static void
PrintJumptableInfo(
    ClientData clientData,
    Tcl_Obj *appendObj,
    ByteCode *codePtr,
    unsigned int pcOffset)
{
    register JumptableInfo *jtPtr = clientData;
    Tcl_HashEntry *hPtr;
    Tcl_HashSearch search;
    const char *keyPtr;
    int offset, i = 0;

    hPtr = Tcl_FirstHashEntry(&jtPtr->hashTable, &search);
    for (; hPtr ; hPtr = Tcl_NextHashEntry(&search)) {
	keyPtr = Tcl_GetHashKey(&jtPtr->hashTable, hPtr);
	offset = PTR2INT(Tcl_GetHashValue(hPtr));

	if (i++) {
	    Tcl_AppendToObj(appendObj, ", ", -1);
	    if (i%4==0) {
		Tcl_AppendToObj(appendObj, "\n\t\t", -1);
	    }
	}
	Tcl_AppendPrintfToObj(appendObj, "\"%s\"->pc %d",
		keyPtr, pcOffset + offset);
    }
}

/*
 *----------------------------------------------------------------------
 *
 * TclCompileWhileCmd --
 *
 *	Procedure called to compile the "while" command.
 *
 * Results:
 * 	Returns TCL_OK for a successful compile. Returns TCL_ERROR to defer
 * 	evaluation to runtime.
 *
 * Side effects:
 *	Instructions are added to envPtr to execute the "while" command at
 *	runtime.
 *
 *----------------------------------------------------------------------
 */

int
TclCompileWhileCmd(
    Tcl_Interp *interp,		/* Used for error reporting. */
    Tcl_Parse *parsePtr,	/* Points to a parse structure for the command
				 * created by Tcl_ParseCommand. */
    Command *cmdPtr,		/* Points to defintion of command being
				 * compiled. */
    CompileEnv *envPtr)		/* Holds resulting instructions. */
{
    Tcl_Token *testTokenPtr, *bodyTokenPtr;
    JumpFixup jumpEvalCondFixup;
    int testCodeOffset, bodyCodeOffset, jumpDist, range, code, boolVal;
    int savedStackDepth = envPtr->currStackDepth;
    int loopMayEnd = 1;		/* This is set to 0 if it is recognized as an
				 * infinite loop. */
    Tcl_Obj *boolObj;
    DefineLineInformation;	/* TIP #280 */

    if (parsePtr->numWords != 3) {
	return TCL_ERROR;
    }

    /*
     * If the test expression requires substitutions, don't compile the while
     * command inline. E.g., the expression might cause the loop to never
     * execute or execute forever, as in "while "$x < 5" {}".
     *
     * Bail out also if the body expression requires substitutions in order to
     * insure correct behaviour [Bug 219166]
     */

    testTokenPtr = TokenAfter(parsePtr->tokenPtr);
    bodyTokenPtr = TokenAfter(testTokenPtr);

    if ((testTokenPtr->type != TCL_TOKEN_SIMPLE_WORD)
	    || (bodyTokenPtr->type != TCL_TOKEN_SIMPLE_WORD)) {
	return TCL_ERROR;
    }

    /*
     * Find out if the condition is a constant.
     */

    boolObj = Tcl_NewStringObj(testTokenPtr[1].start, testTokenPtr[1].size);
    Tcl_IncrRefCount(boolObj);
    code = Tcl_GetBooleanFromObj(NULL, boolObj, &boolVal);
    TclDecrRefCount(boolObj);
    if (code == TCL_OK) {
	if (boolVal) {
	    /*
	     * It is an infinite loop; flag it so that we generate a more
	     * efficient body.
	     */

	    loopMayEnd = 0;
	} else {
	    /*
	     * This is an empty loop: "while 0 {...}" or such. Compile no
	     * bytecodes.
	     */

	    goto pushResult;
	}
    }

    /*
     * Create a ExceptionRange record for the loop body. This is used to
     * implement break and continue.
     */

    range = DeclareExceptionRange(envPtr, LOOP_EXCEPTION_RANGE);

    /*
     * Jump to the evaluation of the condition. This code uses the "loop
     * rotation" optimisation (which eliminates one branch from the loop).
     * "while cond body" produces then:
     *       goto A
     *    B: body                : bodyCodeOffset
     *    A: cond -> result      : testCodeOffset, continueOffset
     *       if (result) goto B
     *
     * The infinite loop "while 1 body" produces:
     *    B: body                : all three offsets here
     *       goto B
     */

    if (loopMayEnd) {
	TclEmitForwardJump(envPtr, TCL_UNCONDITIONAL_JUMP, &jumpEvalCondFixup);
	testCodeOffset = 0;	/* Avoid compiler warning. */
    } else {
	/*
	 * Make sure that the first command in the body is preceded by an
	 * INST_START_CMD, and hence counted properly. [Bug 1752146]
	 */

	envPtr->atCmdStart = 0;
	testCodeOffset = CurrentOffset(envPtr);
    }

    /*
     * Compile the loop body.
     */

    envPtr->line = mapPtr->loc[eclIndex].line[2];
    bodyCodeOffset = ExceptionRangeStarts(envPtr, range);
    CompileBody(envPtr, bodyTokenPtr, interp);
    ExceptionRangeEnds(envPtr, range);
    envPtr->currStackDepth = savedStackDepth + 1;
    TclEmitOpcode(INST_POP, envPtr);

    /*
     * Compile the test expression then emit the conditional jump that
     * terminates the while. We already know it's a simple word.
     */

    if (loopMayEnd) {
	testCodeOffset = CurrentOffset(envPtr);
	jumpDist = testCodeOffset - jumpEvalCondFixup.codeOffset;
	if (TclFixupForwardJump(envPtr, &jumpEvalCondFixup, jumpDist, 127)) {
	    bodyCodeOffset += 3;
	    testCodeOffset += 3;
	}
	envPtr->currStackDepth = savedStackDepth;
	envPtr->line = mapPtr->loc[eclIndex].line[1];
	TclCompileExprWords(interp, testTokenPtr, 1, envPtr);
	envPtr->currStackDepth = savedStackDepth + 1;

	jumpDist = CurrentOffset(envPtr) - bodyCodeOffset;
	if (jumpDist > 127) {
	    TclEmitInstInt4(INST_JUMP_TRUE4, -jumpDist, envPtr);
	} else {
	    TclEmitInstInt1(INST_JUMP_TRUE1, -jumpDist, envPtr);
	}
    } else {
	jumpDist = CurrentOffset(envPtr) - bodyCodeOffset;
	if (jumpDist > 127) {
	    TclEmitInstInt4(INST_JUMP4, -jumpDist, envPtr);
	} else {
	    TclEmitInstInt1(INST_JUMP1, -jumpDist, envPtr);
	}
    }

    /*
     * Set the loop's body, continue and break offsets.
     */

    envPtr->exceptArrayPtr[range].continueOffset = testCodeOffset;
    envPtr->exceptArrayPtr[range].codeOffset = bodyCodeOffset;
    ExceptionRangeTarget(envPtr, range, breakOffset);

    /*
     * The while command's result is an empty string.
     */

  pushResult:
    envPtr->currStackDepth = savedStackDepth;
    PushLiteral(envPtr, "", 0);
    return TCL_OK;
}

/*
 *----------------------------------------------------------------------
 *
 * PushVarName --
 *
 *	Procedure used in the compiling where pushing a variable name is
 *	necessary (append, lappend, set).
 *
 * Results:
 * 	Returns TCL_OK for a successful compile. Returns TCL_ERROR to defer
 * 	evaluation to runtime.
 *
 * Side effects:
 *	Instructions are added to envPtr to execute the "set" command at
 *	runtime.
 *
 *----------------------------------------------------------------------
 */

static int
PushVarName(
    Tcl_Interp *interp,		/* Used for error reporting. */
    Tcl_Token *varTokenPtr,	/* Points to a variable token. */
    CompileEnv *envPtr,		/* Holds resulting instructions. */
    int flags,			/* TCL_CREATE_VAR or TCL_NO_LARGE_INDEX. */
    int *localIndexPtr,		/* Must not be NULL. */
    int *simpleVarNamePtr,	/* Must not be NULL. */
    int *isScalarPtr,		/* Must not be NULL. */
    int line)                   /* Line the token starts on. */
{
    register const char *p;
    const char *name, *elName;
    register int i, n;
    Tcl_Token *elemTokenPtr = NULL;
    int nameChars, elNameChars, simpleVarName, localIndex;
    int elemTokenCount = 0, allocedTokens = 0, removedParen = 0;

    /*
     * Decide if we can use a frame slot for the var/array name or if we need
     * to emit code to compute and push the name at runtime. We use a frame
     * slot (entry in the array of local vars) if we are compiling a procedure
     * body and if the name is simple text that does not include namespace
     * qualifiers.
     */

    simpleVarName = 0;
    name = elName = NULL;
    nameChars = elNameChars = 0;
    localIndex = -1;

    /*
     * Check not only that the type is TCL_TOKEN_SIMPLE_WORD, but whether
     * curly braces surround the variable name. This really matters for array
     * elements to handle things like
     *    set {x($foo)} 5
     * which raises an undefined var error if we are not careful here.
     */

    if ((varTokenPtr->type == TCL_TOKEN_SIMPLE_WORD) &&
	    (varTokenPtr->start[0] != '{')) {
	/*
	 * A simple variable name. Divide it up into "name" and "elName"
	 * strings. If it is not a local variable, look it up at runtime.
	 */

	simpleVarName = 1;

	name = varTokenPtr[1].start;
	nameChars = varTokenPtr[1].size;
	if (name[nameChars-1] == ')') {
	    /*
	     * last char is ')' => potential array reference.
	     */

	    for (i=0,p=name ; i<nameChars ; i++,p++) {
		if (*p == '(') {
		    elName = p + 1;
		    elNameChars = nameChars - i - 2;
		    nameChars = i;
		    break;
		}
	    }

	    if ((elName != NULL) && elNameChars) {
		/*
		 * An array element, the element name is a simple string:
		 * assemble the corresponding token.
		 */

		elemTokenPtr = (Tcl_Token *) TclStackAlloc(interp,
			sizeof(Tcl_Token));
		allocedTokens = 1;
		elemTokenPtr->type = TCL_TOKEN_TEXT;
		elemTokenPtr->start = elName;
		elemTokenPtr->size = elNameChars;
		elemTokenPtr->numComponents = 0;
		elemTokenCount = 1;
	    }
	}
    } else if (((n = varTokenPtr->numComponents) > 1)
	    && (varTokenPtr[1].type == TCL_TOKEN_TEXT)
	    && (varTokenPtr[n].type == TCL_TOKEN_TEXT)
	    && (varTokenPtr[n].start[varTokenPtr[n].size - 1] == ')')) {

	/*
	 * Check for parentheses inside first token.
	 */

	simpleVarName = 0;
	for (i = 0, p = varTokenPtr[1].start;
		i < varTokenPtr[1].size; i++, p++) {
	    if (*p == '(') {
		simpleVarName = 1;
		break;
	    }
	}
	if (simpleVarName) {
	    int remainingChars;

	    /*
	     * Check the last token: if it is just ')', do not count it.
	     * Otherwise, remove the ')' and flag so that it is restored at
	     * the end.
	     */

	    if (varTokenPtr[n].size == 1) {
		--n;
	    } else {
		--varTokenPtr[n].size;
		removedParen = n;
	    }

	    name = varTokenPtr[1].start;
	    nameChars = p - varTokenPtr[1].start;
	    elName = p + 1;
	    remainingChars = (varTokenPtr[2].start - p) - 1;
	    elNameChars = (varTokenPtr[n].start - p) + varTokenPtr[n].size - 2;

	    if (remainingChars) {
		/*
		 * Make a first token with the extra characters in the first
		 * token.
		 */

		elemTokenPtr = (Tcl_Token *) TclStackAlloc(interp,
			n * sizeof(Tcl_Token));
		allocedTokens = 1;
		elemTokenPtr->type = TCL_TOKEN_TEXT;
		elemTokenPtr->start = elName;
		elemTokenPtr->size = remainingChars;
		elemTokenPtr->numComponents = 0;
		elemTokenCount = n;

		/*
		 * Copy the remaining tokens.
		 */

		memcpy(elemTokenPtr+1, varTokenPtr+2,
			(n-1) * sizeof(Tcl_Token));
	    } else {
		/*
		 * Use the already available tokens.
		 */

		elemTokenPtr = &varTokenPtr[2];
		elemTokenCount = n - 1;
	    }
	}
    }

    if (simpleVarName) {
	/*
	 * See whether name has any namespace separators (::'s).
	 */

	int hasNsQualifiers = 0;
	for (i = 0, p = name;  i < nameChars;  i++, p++) {
	    if ((*p == ':') && ((i+1) < nameChars) && (*(p+1) == ':')) {
		hasNsQualifiers = 1;
		break;
	    }
	}

	/*
	 * Look up the var name's index in the array of local vars in the proc
	 * frame. If retrieving the var's value and it doesn't already exist,
	 * push its name and look it up at runtime.
	 */

	if ((envPtr->procPtr != NULL) && !hasNsQualifiers) {
	    localIndex = TclFindCompiledLocal(name, nameChars,
		    /*create*/ flags & TCL_CREATE_VAR,
		    envPtr->procPtr);
	    if ((flags & TCL_NO_LARGE_INDEX) && (localIndex > 255)) {
		/*
		 * We'll push the name.
		 */

		localIndex = -1;
	    }
	}
	if (localIndex < 0) {
	    PushLiteral(envPtr, name, nameChars);
	}

	/*
	 * Compile the element script, if any.
	 */

	if (elName != NULL) {
	    if (elNameChars) {
		envPtr->line = line;
		TclCompileTokens(interp, elemTokenPtr, elemTokenCount, envPtr);
	    } else {
		PushLiteral(envPtr, "", 0);
	    }
	}
    } else {
	/*
	 * The var name isn't simple: compile and push it.
	 */

	envPtr->line = line;
	CompileTokens(envPtr, varTokenPtr, interp);
    }

    if (removedParen) {
	++varTokenPtr[removedParen].size;
    }
    if (allocedTokens) {
	TclStackFree(interp, elemTokenPtr);
    }
    *localIndexPtr = localIndex;
    *simpleVarNamePtr = simpleVarName;
    *isScalarPtr = (elName == NULL);
    return TCL_OK;
}

/*
 *----------------------------------------------------------------------
 *
 * CompileUnaryOpCmd --
 *
 *	Utility routine to compile the unary operator commands.
 *
 * Results:
 * 	Returns TCL_OK for a successful compile. Returns TCL_ERROR to defer
 * 	evaluation to runtime.
 *
 * Side effects:
 *	Instructions are added to envPtr to execute the compiled command at
 *	runtime.
 *
 *----------------------------------------------------------------------
 */

static int
CompileUnaryOpCmd(
    Tcl_Interp *interp,
    Tcl_Parse *parsePtr,
    int instruction,
    CompileEnv *envPtr)
{
    Tcl_Token *tokenPtr;
    DefineLineInformation;	/* TIP #280 */

    if (parsePtr->numWords != 2) {
	return TCL_ERROR;
    }
    tokenPtr = TokenAfter(parsePtr->tokenPtr);
    CompileWord(envPtr, tokenPtr, interp, 1);
    TclEmitOpcode(instruction, envPtr);
    return TCL_OK;
}

/*
 *----------------------------------------------------------------------
 *
 * CompileAssociativeBinaryOpCmd --
 *
 *	Utility routine to compile the binary operator commands that accept an
 *	arbitrary number of arguments, and that are associative operations.
 *	Because of the associativity, we may combine operations from right to
 *	left, saving us any effort of re-ordering the arguments on the stack
 *	after substitutions are completed.
 *
 * Results:
 * 	Returns TCL_OK for a successful compile. Returns TCL_ERROR to defer
 * 	evaluation to runtime.
 *
 * Side effects:
 *	Instructions are added to envPtr to execute the compiled command at
 *	runtime.
 *
 *----------------------------------------------------------------------
 */

static int
CompileAssociativeBinaryOpCmd(
    Tcl_Interp *interp,
    Tcl_Parse *parsePtr,
    const char *identity,
    int instruction,
    CompileEnv *envPtr)
{
    Tcl_Token *tokenPtr = parsePtr->tokenPtr;
    DefineLineInformation;	/* TIP #280 */
    int words;

    for (words=1 ; words<parsePtr->numWords ; words++) {
	tokenPtr = TokenAfter(tokenPtr);
	CompileWord(envPtr, tokenPtr, interp, words);
    }
    if (parsePtr->numWords <= 2) {
	PushLiteral(envPtr, identity, -1);
	words++;
    }
    if (words > 3) {
	/*
	 * Reverse order of arguments to get precise agreement with
	 * [expr] in calcuations, including roundoff errors.
	 */
	TclEmitInstInt4(INST_REVERSE, words-1, envPtr);
    }
    while (--words > 1) {
	TclEmitOpcode(instruction, envPtr);
    }
    return TCL_OK;
}

/*
 *----------------------------------------------------------------------
 *
 * CompileStrictlyBinaryOpCmd --
 *
 *	Utility routine to compile the binary operator commands, that strictly
 *	accept exactly two arguments.
 *
 * Results:
 * 	Returns TCL_OK for a successful compile. Returns TCL_ERROR to defer
 * 	evaluation to runtime.
 *
 * Side effects:
 *	Instructions are added to envPtr to execute the compiled command at
 *	runtime.
 *
 *----------------------------------------------------------------------
 */

static int
CompileStrictlyBinaryOpCmd(
    Tcl_Interp *interp,
    Tcl_Parse *parsePtr,
    int instruction,
    CompileEnv *envPtr)
{
    if (parsePtr->numWords != 3) {
	return TCL_ERROR;
    }
    return CompileAssociativeBinaryOpCmd(interp, parsePtr,
	    NULL, instruction, envPtr);
}

/*
 *----------------------------------------------------------------------
 *
 * CompileComparisonOpCmd --
 *
 *	Utility routine to compile the n-ary comparison operator commands.
 *
 * Results:
 *	Returns TCL_OK for a successful compile. Returns TCL_ERROR to defer
 *	evaluation to runtime.
 *
 * Side effects:
 *	Instructions are added to envPtr to execute the compiled command at
 *	runtime.
 *
 *----------------------------------------------------------------------
 */

static int
CompileComparisonOpCmd(
    Tcl_Interp *interp,
    Tcl_Parse *parsePtr,
    int instruction,
    CompileEnv *envPtr)
{
    Tcl_Token *tokenPtr;
    DefineLineInformation;	/* TIP #280 */

    if (parsePtr->numWords < 3) {
	PushLiteral(envPtr, "1", 1);
    } else if (parsePtr->numWords == 3) {
	tokenPtr = TokenAfter(parsePtr->tokenPtr);
	CompileWord(envPtr, tokenPtr, interp, 1);
	tokenPtr = TokenAfter(tokenPtr);
	CompileWord(envPtr, tokenPtr, interp, 2);
	TclEmitOpcode(instruction, envPtr);
    } else if (envPtr->procPtr == NULL) {
	/*
	 * No local variable space!
	 */

	return TCL_ERROR;
    } else {
	int tmpIndex = TclFindCompiledLocal(NULL, 0, 1, envPtr->procPtr);
	int words;

	tokenPtr = TokenAfter(parsePtr->tokenPtr);
	CompileWord(envPtr, tokenPtr, interp, 1);
	tokenPtr = TokenAfter(tokenPtr);
	CompileWord(envPtr, tokenPtr, interp, 2);
	if (tmpIndex <= 255) {
	    TclEmitInstInt1(INST_STORE_SCALAR1, tmpIndex, envPtr);
	} else {
	    TclEmitInstInt4(INST_STORE_SCALAR4, tmpIndex, envPtr);
	}
	TclEmitOpcode(instruction, envPtr);
	for (words=3 ; words<parsePtr->numWords ;) {
	    if (tmpIndex <= 255) {
		TclEmitInstInt1(INST_LOAD_SCALAR1, tmpIndex, envPtr);
	    } else {
		TclEmitInstInt4(INST_LOAD_SCALAR4, tmpIndex, envPtr);
	    }
	    tokenPtr = TokenAfter(tokenPtr);
	    CompileWord(envPtr, tokenPtr, interp, words);
	    if (++words < parsePtr->numWords) {
		if (tmpIndex <= 255) {
		    TclEmitInstInt1(INST_STORE_SCALAR1, tmpIndex, envPtr);
		} else {
		    TclEmitInstInt4(INST_STORE_SCALAR4, tmpIndex, envPtr);
		}
	    }
	    TclEmitOpcode(instruction, envPtr);
	}
	for (; words>3 ; words--) {
	    TclEmitOpcode(INST_BITAND, envPtr);
	}

	/*
	 * Drop the value from the temp variable; retaining that reference
	 * might be expensive elsewhere.
	 */

	PushLiteral(envPtr, "", 0);
	if (tmpIndex <= 255) {
	    TclEmitInstInt1(INST_STORE_SCALAR1, tmpIndex, envPtr);
	} else {
	    TclEmitInstInt4(INST_STORE_SCALAR4, tmpIndex, envPtr);
	}
	TclEmitOpcode(INST_POP, envPtr);
    }
    return TCL_OK;
}

/*
 *----------------------------------------------------------------------
 *
 * TclCompile*OpCmd --
 *
 *	Procedures called to compile the corresponding "::tcl::mathop::*"
 *	commands. These are all wrappers around the utility operator command
 *	compiler functions, except for the compilers for subtraction and
 *	division, which are special.
 *
 * Results:
 * 	Returns TCL_OK for a successful compile. Returns TCL_ERROR to defer
 * 	evaluation to runtime.
 *
 * Side effects:
 *	Instructions are added to envPtr to execute the compiled command at
 *	runtime.
 *
 *----------------------------------------------------------------------
 */

int
TclCompileInvertOpCmd(
    Tcl_Interp *interp,
    Tcl_Parse *parsePtr,
    Command *cmdPtr,		/* Points to defintion of command being
				 * compiled. */
    CompileEnv *envPtr)
{
    return CompileUnaryOpCmd(interp, parsePtr, INST_BITNOT, envPtr);
}

int
TclCompileNotOpCmd(
    Tcl_Interp *interp,
    Tcl_Parse *parsePtr,
    Command *cmdPtr,		/* Points to defintion of command being
				 * compiled. */
    CompileEnv *envPtr)
{
    return CompileUnaryOpCmd(interp, parsePtr, INST_LNOT, envPtr);
}

int
TclCompileAddOpCmd(
    Tcl_Interp *interp,
    Tcl_Parse *parsePtr,
    Command *cmdPtr,		/* Points to defintion of command being
				 * compiled. */
    CompileEnv *envPtr)
{
    return CompileAssociativeBinaryOpCmd(interp, parsePtr, "0", INST_ADD,
	    envPtr);
}

int
TclCompileMulOpCmd(
    Tcl_Interp *interp,
    Tcl_Parse *parsePtr,
    Command *cmdPtr,		/* Points to defintion of command being
				 * compiled. */
    CompileEnv *envPtr)
{
    return CompileAssociativeBinaryOpCmd(interp, parsePtr, "1", INST_MULT,
	    envPtr);
}

int
TclCompileAndOpCmd(
    Tcl_Interp *interp,
    Tcl_Parse *parsePtr,
    Command *cmdPtr,		/* Points to defintion of command being
				 * compiled. */
    CompileEnv *envPtr)
{
    return CompileAssociativeBinaryOpCmd(interp, parsePtr, "-1", INST_BITAND,
	    envPtr);
}

int
TclCompileOrOpCmd(
    Tcl_Interp *interp,
    Tcl_Parse *parsePtr,
    Command *cmdPtr,		/* Points to defintion of command being
				 * compiled. */
    CompileEnv *envPtr)
{
    return CompileAssociativeBinaryOpCmd(interp, parsePtr, "0", INST_BITOR,
	    envPtr);
}

int
TclCompileXorOpCmd(
    Tcl_Interp *interp,
    Tcl_Parse *parsePtr,
    Command *cmdPtr,		/* Points to defintion of command being
				 * compiled. */
    CompileEnv *envPtr)
{
    return CompileAssociativeBinaryOpCmd(interp, parsePtr, "0", INST_BITXOR,
	    envPtr);
}

int
TclCompilePowOpCmd(
    Tcl_Interp *interp,
    Tcl_Parse *parsePtr,
    Command *cmdPtr,		/* Points to defintion of command being
				 * compiled. */
    CompileEnv *envPtr)
{
    /*
     * This one has its own implementation because the ** operator is
     * the only one with right associativity.
     */
    Tcl_Token *tokenPtr = parsePtr->tokenPtr;
    DefineLineInformation;	/* TIP #280 */
    int words;

    for (words=1 ; words<parsePtr->numWords ; words++) {
	tokenPtr = TokenAfter(tokenPtr);
	CompileWord(envPtr, tokenPtr, interp, words);
    }
    if (parsePtr->numWords <= 2) {
	PushLiteral(envPtr, "1", 1);
	words++;
    }
    while (--words > 1) {
	TclEmitOpcode(INST_EXPON, envPtr);
    }
    return TCL_OK;
}

int
TclCompileLshiftOpCmd(
    Tcl_Interp *interp,
    Tcl_Parse *parsePtr,
    Command *cmdPtr,		/* Points to defintion of command being
				 * compiled. */
    CompileEnv *envPtr)
{
    return CompileStrictlyBinaryOpCmd(interp, parsePtr, INST_LSHIFT, envPtr);
}

int
TclCompileRshiftOpCmd(
    Tcl_Interp *interp,
    Tcl_Parse *parsePtr,
    Command *cmdPtr,		/* Points to defintion of command being
				 * compiled. */
    CompileEnv *envPtr)
{
    return CompileStrictlyBinaryOpCmd(interp, parsePtr, INST_RSHIFT, envPtr);
}

int
TclCompileModOpCmd(
    Tcl_Interp *interp,
    Tcl_Parse *parsePtr,
    Command *cmdPtr,		/* Points to defintion of command being
				 * compiled. */
    CompileEnv *envPtr)
{
    return CompileStrictlyBinaryOpCmd(interp, parsePtr, INST_MOD, envPtr);
}

int
TclCompileNeqOpCmd(
    Tcl_Interp *interp,
    Tcl_Parse *parsePtr,
    Command *cmdPtr,		/* Points to defintion of command being
				 * compiled. */
    CompileEnv *envPtr)
{
    return CompileStrictlyBinaryOpCmd(interp, parsePtr, INST_NEQ, envPtr);
}

int
TclCompileStrneqOpCmd(
    Tcl_Interp *interp,
    Tcl_Parse *parsePtr,
    Command *cmdPtr,		/* Points to defintion of command being
				 * compiled. */
    CompileEnv *envPtr)
{
    return CompileStrictlyBinaryOpCmd(interp, parsePtr, INST_STR_NEQ, envPtr);
}

int
TclCompileInOpCmd(
    Tcl_Interp *interp,
    Tcl_Parse *parsePtr,
    Command *cmdPtr,		/* Points to defintion of command being
				 * compiled. */
    CompileEnv *envPtr)
{
    return CompileStrictlyBinaryOpCmd(interp, parsePtr, INST_LIST_IN, envPtr);
}

int
TclCompileNiOpCmd(
    Tcl_Interp *interp,
    Tcl_Parse *parsePtr,
    Command *cmdPtr,		/* Points to defintion of command being
				 * compiled. */
    CompileEnv *envPtr)
{
    return CompileStrictlyBinaryOpCmd(interp, parsePtr, INST_LIST_NOT_IN,
	    envPtr);
}

int
TclCompileLessOpCmd(
    Tcl_Interp *interp,
    Tcl_Parse *parsePtr,
    Command *cmdPtr,		/* Points to defintion of command being
				 * compiled. */
    CompileEnv *envPtr)
{
    return CompileComparisonOpCmd(interp, parsePtr, INST_LT, envPtr);
}

int
TclCompileLeqOpCmd(
    Tcl_Interp *interp,
    Tcl_Parse *parsePtr,
    Command *cmdPtr,		/* Points to defintion of command being
				 * compiled. */
    CompileEnv *envPtr)
{
    return CompileComparisonOpCmd(interp, parsePtr, INST_LE, envPtr);
}

int
TclCompileGreaterOpCmd(
    Tcl_Interp *interp,
    Tcl_Parse *parsePtr,
    Command *cmdPtr,		/* Points to defintion of command being
				 * compiled. */
    CompileEnv *envPtr)
{
    return CompileComparisonOpCmd(interp, parsePtr, INST_GT, envPtr);
}

int
TclCompileGeqOpCmd(
    Tcl_Interp *interp,
    Tcl_Parse *parsePtr,
    Command *cmdPtr,		/* Points to defintion of command being
				 * compiled. */
    CompileEnv *envPtr)
{
    return CompileComparisonOpCmd(interp, parsePtr, INST_GE, envPtr);
}

int
TclCompileEqOpCmd(
    Tcl_Interp *interp,
    Tcl_Parse *parsePtr,
    Command *cmdPtr,		/* Points to defintion of command being
				 * compiled. */
    CompileEnv *envPtr)
{
    return CompileComparisonOpCmd(interp, parsePtr, INST_EQ, envPtr);
}

int
TclCompileStreqOpCmd(
    Tcl_Interp *interp,
    Tcl_Parse *parsePtr,
    Command *cmdPtr,		/* Points to defintion of command being
				 * compiled. */
    CompileEnv *envPtr)
{
    return CompileComparisonOpCmd(interp, parsePtr, INST_STR_EQ, envPtr);
}

int
TclCompileMinusOpCmd(
    Tcl_Interp *interp,
    Tcl_Parse *parsePtr,
    Command *cmdPtr,		/* Points to defintion of command being
				 * compiled. */
    CompileEnv *envPtr)
{
    Tcl_Token *tokenPtr = parsePtr->tokenPtr;
    DefineLineInformation;	/* TIP #280 */
    int words;

    if (parsePtr->numWords == 1) {
	/* Fallback to direct eval to report syntax error */
	return TCL_ERROR;
    }
    for (words=1 ; words<parsePtr->numWords ; words++) {
	tokenPtr = TokenAfter(tokenPtr);
	CompileWord(envPtr, tokenPtr, interp, words);
    }
    if (words == 2) {
	TclEmitOpcode(INST_UMINUS, envPtr);
	return TCL_OK;
    }
    if (words == 3) {
	TclEmitOpcode(INST_SUB, envPtr);
	return TCL_OK;
    }
    /*
     * Reverse order of arguments to get precise agreement with
     * [expr] in calcuations, including roundoff errors.
     */
    TclEmitInstInt4(INST_REVERSE, words-1, envPtr);
    while (--words > 1) {
	TclEmitInstInt4(INST_REVERSE, 2, envPtr);
	TclEmitOpcode(INST_SUB, envPtr);
    }
    return TCL_OK;
}

int
TclCompileDivOpCmd(
    Tcl_Interp *interp,
    Tcl_Parse *parsePtr,
    Command *cmdPtr,		/* Points to defintion of command being
				 * compiled. */
    CompileEnv *envPtr)
{
    Tcl_Token *tokenPtr = parsePtr->tokenPtr;
    DefineLineInformation;	/* TIP #280 */
    int words;

    if (parsePtr->numWords == 1) {
	/* Fallback to direct eval to report syntax error */
	return TCL_ERROR;
    }
    if (parsePtr->numWords == 2) {
	PushLiteral(envPtr, "1.0", 3);
    }
    for (words=1 ; words<parsePtr->numWords ; words++) {
	tokenPtr = TokenAfter(tokenPtr);
	CompileWord(envPtr, tokenPtr, interp, words);
    }
    if (words <= 3) {
	TclEmitOpcode(INST_DIV, envPtr);
	return TCL_OK;
    }
    /*
     * Reverse order of arguments to get precise agreement with
     * [expr] in calcuations, including roundoff errors.
     */
    TclEmitInstInt4(INST_REVERSE, words-1, envPtr);
    while (--words > 1) {
	TclEmitInstInt4(INST_REVERSE, 2, envPtr);
	TclEmitOpcode(INST_DIV, envPtr);
    }
    return TCL_OK;
}

/*
 *----------------------------------------------------------------------
 *
 * IndexTailVarIfKnown --
 *
 *	Procedure used in compiling [global] and [variable] commands. It
 *	inspects the variable name described by varTokenPtr and, if the tail
 *	is known at compile time, defines a corresponding local variable.
 *
 * Results:
 * 	Returns the variable's index in the table of compiled locals if the
 *      tail is known at compile time, or -1 otherwise.
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */

static int
IndexTailVarIfKnown(
    Tcl_Interp *interp,
    Tcl_Token *varTokenPtr,	/* Token representing the variable name */
    CompileEnv *envPtr)		/* Holds resulting instructions. */
{
    Tcl_Obj *tailPtr;
    const char *tailName, *p;
    int len, n = varTokenPtr->numComponents;
    Tcl_Token *lastTokenPtr;
    int full, localIndex;

    /*
     * Determine if the tail is (a) known at compile time, and (b) not an
     * array element. Should any of these fail, return an error so that
     * the non-compiled command will be called at runtime.
     * In order for the tail to be known at compile time, the last token
     * in the word has to be constant and contain "::" if it is not the
     * only one.
     */

    if (envPtr->procPtr == NULL) {
	return -1;
    }

    TclNewObj(tailPtr);
    if (TclWordKnownAtCompileTime(varTokenPtr, tailPtr)) {
	full = 1;
	lastTokenPtr = varTokenPtr;
    } else {
	full = 0;
	lastTokenPtr = varTokenPtr + n;
	if (!TclWordKnownAtCompileTime(lastTokenPtr, tailPtr)) {
	    Tcl_DecrRefCount(tailPtr);
	    return -1;
	}
    }

    tailName = TclGetStringFromObj(tailPtr, &len);

    if (len) {
	if (*(tailName+len-1) == ')') {
	    /*
	     * Possible array: bail out
	     */

	    Tcl_DecrRefCount(tailPtr);
	    return -1;
	}

	/*
	 * Get the tail: immediately after the last '::'
	 */

	for(p = tailName + len -1; p > tailName; p--) {
	    if ((*p == ':') && (*(p-1) == ':')) {
		p++;
		break;
	    }
	}
	if (!full && (p == tailName)) {
	    /*
	     * No :: in the last component
	     */
	    Tcl_DecrRefCount(tailPtr);
	    return -1;
	}
	len -= p - tailName;
	tailName = p;
    }

    localIndex = TclFindCompiledLocal(tailName, len,
	    /*create*/ TCL_CREATE_VAR,
	    envPtr->procPtr);
    Tcl_DecrRefCount(tailPtr);
    return localIndex;
}

/*
 *----------------------------------------------------------------------
 *
 * TclCompileUpvarCmd --
 *
 *	Procedure called to compile the "upvar" command.
 *
 * Results:
 * 	Returns TCL_OK for a successful compile. Returns TCL_ERROR to defer
 * 	evaluation to runtime.
 *
 * Side effects:
 *	Instructions are added to envPtr to execute the "upvar" command at
 *	runtime.
 *
 *----------------------------------------------------------------------
 */

int
TclCompileUpvarCmd(
    Tcl_Interp *interp,		/* Used for error reporting. */
    Tcl_Parse *parsePtr,	/* Points to a parse structure for the command
				 * created by Tcl_ParseCommand. */
    Command *cmdPtr,		/* Points to defintion of command being
				 * compiled. */
    CompileEnv *envPtr)		/* Holds resulting instructions. */
{
    Tcl_Token *tokenPtr, *otherTokenPtr, *localTokenPtr;
    int simpleVarName, isScalar, localIndex, numWords, i;
    DefineLineInformation;	/* TIP #280 */
    Tcl_Obj *objPtr = Tcl_NewObj();

    if (envPtr->procPtr == NULL) {
	Tcl_DecrRefCount(objPtr);
	return TCL_ERROR;
    }

    numWords = parsePtr->numWords;
    if (numWords < 3) {
	Tcl_DecrRefCount(objPtr);
	return TCL_ERROR;
    }

    /*
     * Push the frame index if it is known at compile time
     */

    tokenPtr = TokenAfter(parsePtr->tokenPtr);
    if(TclWordKnownAtCompileTime(tokenPtr, objPtr)) {
	CallFrame *framePtr;
	Tcl_ObjType *newTypePtr, *typePtr = objPtr->typePtr;

	/*
	 * Attempt to convert to a level reference. Note that TclObjGetFrame
	 * only changes the obj type when a conversion was successful.
	 */

	TclObjGetFrame(interp, objPtr, &framePtr);
	newTypePtr = objPtr->typePtr;
	Tcl_DecrRefCount(objPtr);

	if (newTypePtr != typePtr) {
	    if(numWords%2) {
		return TCL_ERROR;
	    }
	    CompileWord(envPtr, tokenPtr, interp, 1);
	    otherTokenPtr = TokenAfter(tokenPtr);
	    i = 4;
	} else {
	    if(!(numWords%2)) {
		return TCL_ERROR;
	    }
	    PushLiteral(envPtr, "1", 1);
	    otherTokenPtr = tokenPtr;
	    i = 3;
	}
    } else {
	Tcl_DecrRefCount(objPtr);
	return TCL_ERROR;
    }

    /*
     * Loop over the (otherVar, thisVar) pairs. If any of the thisVar is not a
     * local variable, return an error so that the non-compiled command will
     * be called at runtime.
     */

    for(; i<=numWords; i+=2, otherTokenPtr = TokenAfter(localTokenPtr)) {
	localTokenPtr = TokenAfter(otherTokenPtr);

	CompileWord(envPtr, otherTokenPtr, interp, 1);
	PushVarName(interp, localTokenPtr, envPtr, TCL_CREATE_VAR,
		&localIndex, &simpleVarName, &isScalar,
		mapPtr->loc[eclIndex].line[1]);

	if((localIndex < 0) || !isScalar) {
	    return TCL_ERROR;
	}
	TclEmitInstInt4(INST_UPVAR, localIndex, envPtr);
    }

    /*
     * Pop the frame index, and set the result to empty
     */

    TclEmitOpcode(INST_POP, envPtr);
    PushLiteral(envPtr, "", 0);
    return TCL_OK;
}

/*
 *----------------------------------------------------------------------
 *
 * TclCompileNamespaceCmd --
 *
 *	Procedure called to compile the "namespace" command; currently, only
 *	the subcommand "namespace upvar" is compiled to bytecodes.
 *
 * Results:
 * 	Returns TCL_OK for a successful compile. Returns TCL_ERROR to defer
 * 	evaluation to runtime.
 *
 * Side effects:
 *	Instructions are added to envPtr to execute the "namespace upvar"
 *      command at runtime.
 *
 *----------------------------------------------------------------------
 */

int
TclCompileNamespaceCmd(
    Tcl_Interp *interp,		/* Used for error reporting. */
    Tcl_Parse *parsePtr,	/* Points to a parse structure for the command
				 * created by Tcl_ParseCommand. */
    Command *cmdPtr,		/* Points to defintion of command being
				 * compiled. */
    CompileEnv *envPtr)		/* Holds resulting instructions. */
{
    Tcl_Token *tokenPtr, *otherTokenPtr, *localTokenPtr;
    int simpleVarName, isScalar, localIndex, numWords, i;
    DefineLineInformation;	/* TIP #280 */

    if (envPtr->procPtr == NULL) {
	return TCL_ERROR;
    }

    /*
     * Only compile [namespace upvar ...]: needs an odd number of args, >=5
     */

    numWords = parsePtr->numWords;
    if (!(numWords%2) || (numWords < 5)) {
	return TCL_ERROR;
    }

    /*
     * Check if the second argument is "upvar"
     */

    tokenPtr = TokenAfter(parsePtr->tokenPtr);
    if ((tokenPtr->size != 5)  /* 5 == strlen("upvar") */
	    || strncmp(tokenPtr->start, "upvar", 5)) {
	return TCL_ERROR;
    }

    /*
     * Push the namespace
     */

    tokenPtr = TokenAfter(tokenPtr);
    CompileWord(envPtr, tokenPtr, interp, 1);

    /*
     * Loop over the (otherVar, thisVar) pairs. If any of the thisVar is not a
     * local variable, return an error so that the non-compiled command will
     * be called at runtime.
     */

    localTokenPtr = tokenPtr;
    for(i=4; i<=numWords; i+=2) {
	otherTokenPtr = TokenAfter(localTokenPtr);
	localTokenPtr = TokenAfter(otherTokenPtr);

	CompileWord(envPtr, otherTokenPtr, interp, 1);
	PushVarName(interp, localTokenPtr, envPtr, TCL_CREATE_VAR,
		&localIndex, &simpleVarName, &isScalar,
		mapPtr->loc[eclIndex].line[1]);

	if((localIndex < 0) || !isScalar) {
	    return TCL_ERROR;
	}
	TclEmitInstInt4(INST_NSUPVAR, localIndex, envPtr);
    }

    /*
     * Pop the namespace, and set the result to empty
     */

    TclEmitOpcode(INST_POP, envPtr);
    PushLiteral(envPtr, "", 0);
    return TCL_OK;
}

/*
 *----------------------------------------------------------------------
 *
 * TclCompileGlobalCmd --
 *
 *	Procedure called to compile the "global" command.
 *
 * Results:
 * 	Returns TCL_OK for a successful compile. Returns TCL_ERROR to defer
 * 	evaluation to runtime.
 *
 * Side effects:
 *	Instructions are added to envPtr to execute the "global" command at
 *	runtime.
 *
 *----------------------------------------------------------------------
 */

int
TclCompileGlobalCmd(
    Tcl_Interp *interp,		/* Used for error reporting. */
    Tcl_Parse *parsePtr,	/* Points to a parse structure for the command
				 * created by Tcl_ParseCommand. */
    Command *cmdPtr,		/* Points to defintion of command being
				 * compiled. */
    CompileEnv *envPtr)		/* Holds resulting instructions. */
{
    Tcl_Token *varTokenPtr;
    int localIndex, numWords, i;
    DefineLineInformation;	/* TIP #280 */

    numWords = parsePtr->numWords;
    if (numWords < 2) {
	return TCL_ERROR;
    }

    /*
     * 'global' has no effect outside of proc bodies; handle that at runtime
     */

    if (envPtr->procPtr == NULL) {
	return TCL_ERROR;
    }

    /*
     * Push the namespace
     */

    PushLiteral(envPtr, "::", 2);

    /*
     * Loop over the variables.
     */

    varTokenPtr = TokenAfter(parsePtr->tokenPtr);
    for(i=2; i<=numWords; varTokenPtr = TokenAfter(varTokenPtr),i++) {
	localIndex = IndexTailVarIfKnown(interp, varTokenPtr, envPtr);

	if(localIndex < 0) {
	    return TCL_ERROR;
	}

	CompileWord(envPtr, varTokenPtr, interp, 1);
	TclEmitInstInt4(INST_NSUPVAR, localIndex, envPtr);
    }

    /*
     * Pop the namespace, and set the result to empty
     */

    TclEmitOpcode(INST_POP, envPtr);
    PushLiteral(envPtr, "", 0);
    return TCL_OK;
}

/*
 *----------------------------------------------------------------------
 *
 * TclCompileVariableCmd --
 *
 *	Procedure called to compile the "variable" command.
 *
 * Results:
 * 	Returns TCL_OK for a successful compile. Returns TCL_ERROR to defer
 * 	evaluation to runtime.
 *
 * Side effects:
 *	Instructions are added to envPtr to execute the "variable" command at
 *	runtime.
 *
 *----------------------------------------------------------------------
 */

int
TclCompileVariableCmd(
    Tcl_Interp *interp,		/* Used for error reporting. */
    Tcl_Parse *parsePtr,	/* Points to a parse structure for the command
				 * created by Tcl_ParseCommand. */
    Command *cmdPtr,		/* Points to defintion of command being
				 * compiled. */
    CompileEnv *envPtr)		/* Holds resulting instructions. */
{
    Tcl_Token *varTokenPtr, *valueTokenPtr;
    int localIndex, numWords, i;
    DefineLineInformation;	/* TIP #280 */

    numWords = parsePtr->numWords;
    if (numWords < 2) {
	return TCL_ERROR;
    }

    /*
     * Bail out if not compiling a proc body
     */

    if (envPtr->procPtr == NULL) {
	return TCL_ERROR;
    }

    /*
     * Loop over the (var, value) pairs.
     */

    valueTokenPtr = parsePtr->tokenPtr;
    for(i=2; i<=numWords; i+=2) {
	varTokenPtr = TokenAfter(valueTokenPtr);
	valueTokenPtr = TokenAfter(varTokenPtr);

	localIndex = IndexTailVarIfKnown(interp, varTokenPtr, envPtr);

	if(localIndex < 0) {
	    return TCL_ERROR;
	}

	CompileWord(envPtr, varTokenPtr, interp, 1);
	TclEmitInstInt4(INST_VARIABLE, localIndex, envPtr);

	if (i != numWords) {
	    /*
	     * A value has been given: set the variable, pop the value
	     */

	    CompileWord(envPtr, valueTokenPtr, interp, 1);
	    TclEmitInstInt4(INST_STORE_SCALAR4, localIndex, envPtr);
	    TclEmitOpcode(INST_POP, envPtr);
	}
    }

    /*
     * Set the result to empty
     */

    PushLiteral(envPtr, "", 0);
    return TCL_OK;
}

/*
 *----------------------------------------------------------------------
 *
 * TclCompileEnsemble --
 *
 *	Procedure called to compile an ensemble command. Note that most
 *	ensembles are not compiled, since modifying a compiled ensemble causes
 *	a invalidation of all existing bytecode (expensive!) which is not
 *	normally warranted.
 *
 * Results:
 * 	Returns TCL_OK for a successful compile. Returns TCL_ERROR to defer
 * 	evaluation to runtime.
 *
 * Side effects:
 *	Instructions are added to envPtr to execute the subcommands of the
 *	ensemble at runtime if a compile-time mapping is possible.
 *
 *----------------------------------------------------------------------
 */

int
TclCompileEnsemble(
    Tcl_Interp *interp,		/* Used for error reporting. */
    Tcl_Parse *parsePtr,	/* Points to a parse structure for the command
				 * created by Tcl_ParseCommand. */
    Command *cmdPtr,		/* Points to defintion of command being
				 * compiled. */
    CompileEnv *envPtr)		/* Holds resulting instructions. */
{
    Tcl_Token *tokenPtr;
    Tcl_Obj *mapObj, *subcmdObj, *targetCmdObj, *listObj, **elems;
    Tcl_Command ensemble = (Tcl_Command) cmdPtr;
    Tcl_Parse synthetic;
    int len, numBytes, result, flags = 0, i;
    const char *word;

    if (parsePtr->numWords < 2) {
	return TCL_ERROR;
    }

    tokenPtr = TokenAfter(parsePtr->tokenPtr);
    if (tokenPtr->type != TCL_TOKEN_SIMPLE_WORD) {
	/*
	 * Too hard.
	 */

	return TCL_ERROR;
    }

    word = tokenPtr[1].start;
    numBytes = tokenPtr[1].size;

    /*
     * There's a sporting chance we'll be able to compile this. But now we
     * must check properly. To do that, check that we're compiling an ensemble
     * that has a compilable command as its appropriate subcommand.
     */

    if (Tcl_GetEnsembleMappingDict(NULL, ensemble, &mapObj) != TCL_OK
	    || mapObj == NULL) {
	/*
	 * Either not an ensemble or a mapping isn't installed. Crud. Too hard
	 * to proceed.
	 */

	return TCL_ERROR;
    }

    /*
     * Next, get the flags. We need them on several code paths.
     */

    (void) Tcl_GetEnsembleFlags(NULL, ensemble, &flags);

    /*
     * Check to see if there's also a subcommand list; must check to see if
     * the subcommand we are calling is in that list if it exists, since that
     * list filters the entries in the map.
     */

    (void) Tcl_GetEnsembleSubcommandList(NULL, ensemble, &listObj);
    if (listObj != NULL) {
	int sclen;
	const char *str;
	Tcl_Obj *matchObj = NULL;

	if (Tcl_ListObjGetElements(NULL, listObj, &len, &elems) != TCL_OK) {
	    return TCL_ERROR;
	}
	for (i=0 ; i<len ; i++) {
	    str = Tcl_GetStringFromObj(elems[i], &sclen);
	    if (sclen==numBytes && !memcmp(word, str, (unsigned) numBytes)) {
		/*
		 * Exact match! Excellent!
		 */

		result = Tcl_DictObjGet(NULL, mapObj,elems[i], &targetCmdObj);
		if (result != TCL_OK || targetCmdObj == NULL) {
		    return TCL_ERROR;
		}
		goto doneMapLookup;
	    }

	    /*
	     * Check to see if we've got a prefix match. A single prefix match
	     * is fine, and allows us to refine our dictionary lookup, but
	     * multiple prefix matches is a Bad Thing and will prevent us from
	     * making progress. Note that we cannot do the lookup immediately
	     * in the prefix case; might be another entry later in the list
	     * that causes things to fail.
	     */

	    if ((flags & TCL_ENSEMBLE_PREFIX)
		    && strncmp(word, str, (unsigned) numBytes) == 0) {
		if (matchObj != NULL) {
		    return TCL_ERROR;
		}
		matchObj = elems[i];
	    }
	}
	if (matchObj != NULL) {
	    result = Tcl_DictObjGet(NULL, mapObj, matchObj, &targetCmdObj);
	    if (result != TCL_OK || targetCmdObj == NULL) {
		return TCL_ERROR;
	    }
	    goto doneMapLookup;
	}
	return TCL_ERROR;
    } else {
	/*
	 * No map, so check the dictionary directly.
	 */

	TclNewStringObj(subcmdObj, word, numBytes);
	result = Tcl_DictObjGet(NULL, mapObj, subcmdObj, &targetCmdObj);
	TclDecrRefCount(subcmdObj);
	if (result == TCL_OK && targetCmdObj != NULL) {
	    /*
	     * Got it. Skip the fiddling around with prefixes.
	     */

	    goto doneMapLookup;
	}

	/*
	 * We've not literally got a valid subcommand. But maybe we have a
	 * prefix. Check if prefix matches are allowed.
	 */

	if (flags & TCL_ENSEMBLE_PREFIX) {
	    Tcl_DictSearch s;
	    int done, matched;
	    Tcl_Obj *tmpObj;

	    /*
	     * Iterate over the keys in the dictionary, checking to see if
	     * we're a prefix.
	     */

	    Tcl_DictObjFirst(NULL,mapObj,&s,&subcmdObj,&tmpObj,&done);
	    matched = 0;
	    while (!done) {
		if (strncmp(TclGetString(subcmdObj), word,
			(unsigned) numBytes) == 0) {
		    if (matched++) {
			/*
			 * Must have matched twice! Not unique, so no point
			 * looking further.
			 */

			break;
		    }
		    targetCmdObj = tmpObj;
		}
		Tcl_DictObjNext(&s, &subcmdObj, &tmpObj, &done);
	    }
	    Tcl_DictObjDone(&s);

	    /*
	     * If we have anything other than a single match, we've failed the
	     * unique prefix check.
	     */

	    if (matched != 1) {
		return TCL_ERROR;
	    }
	} else {
	    return TCL_ERROR;
	}
    }

    /*
     * OK, we definitely map to something. But what?
     *
     * The command we map to is the first word out of the map element. Note
     * that we also reject dealing with multi-element rewrites if we are in a
     * safe interpreter, as there is otherwise a (highly gnarly!) way to make
     * Tcl crash open to exploit.
     */

  doneMapLookup:
    if (Tcl_ListObjGetElements(NULL, targetCmdObj, &len, &elems) != TCL_OK) {
	return TCL_ERROR;
    }
    if (len > 1 && Tcl_IsSafe(interp)) {
	return TCL_ERROR;
    }
    targetCmdObj = elems[0];

    Tcl_IncrRefCount(targetCmdObj);
    cmdPtr = (Command *) Tcl_GetCommandFromObj(interp, targetCmdObj);
    TclDecrRefCount(targetCmdObj);
    if (cmdPtr == NULL || cmdPtr->compileProc == NULL) {
	/*
	 * Maps to an undefined command or a command without a compiler.
	 * Cannot compile.
	 */

	return TCL_ERROR;
    }

    /*
     * Now we've done the mapping process, can now actually try to compile.
     * We do this by handing off to the subcommand's actual compiler. But to
     * do that, we have to perform some trickery to rewrite the arguments.
     */

    TclParseInit(interp, NULL, 0, &synthetic);
    synthetic.numWords = parsePtr->numWords - 2 + len;
    TclGrowParseTokenArray(&synthetic, 2*len);
    synthetic.numTokens = 2*len;

    /*
     * Now we have the space to work in, install something rewritten. Note
     * that we are here praying for all our might that none of these words are
     * a script; the error detection code will crash if that happens and there
     * is nothing we can do to avoid it!
     */

    for (i=0 ; i<len ; i++) {
	int sclen;
	const char *str = Tcl_GetStringFromObj(elems[i], &sclen);

	synthetic.tokenPtr[2*i].type = TCL_TOKEN_SIMPLE_WORD;
	synthetic.tokenPtr[2*i].start = str;
	synthetic.tokenPtr[2*i].size = sclen;
	synthetic.tokenPtr[2*i].numComponents = 1;

	synthetic.tokenPtr[2*i+1].type = TCL_TOKEN_TEXT;
	synthetic.tokenPtr[2*i+1].start = str;
	synthetic.tokenPtr[2*i+1].size = sclen;
	synthetic.tokenPtr[2*i+1].numComponents = 0;
    }

    /*
     * Copy over the real argument tokens.
     */

    for (i=len; i<synthetic.numWords; i++) {
	int toCopy;
	tokenPtr = TokenAfter(tokenPtr);
	toCopy = tokenPtr->numComponents + 1;
	TclGrowParseTokenArray(&synthetic, toCopy);
	memcpy(synthetic.tokenPtr + synthetic.numTokens, tokenPtr,
		sizeof(Tcl_Token) * toCopy);
	synthetic.numTokens += toCopy;
    }

    /*
     * Hand off compilation to the subcommand compiler. At last!
     */

    result = cmdPtr->compileProc(interp, &synthetic, cmdPtr, envPtr);

    /*
     * Clean up if necessary.
     */

    Tcl_FreeParse(&synthetic);
    return result;
}

/*
 *----------------------------------------------------------------------
 *
 * TclCompileInfoExistsCmd --
 *
 *	Procedure called to compile the "info exists" subcommand.
 *
 * Results:
 * 	Returns TCL_OK for a successful compile. Returns TCL_ERROR to defer
 * 	evaluation to runtime.
 *
 * Side effects:
 *	Instructions are added to envPtr to execute the "info exists"
 *	subcommand at runtime.
 *
 *----------------------------------------------------------------------
 */

int
TclCompileInfoExistsCmd(
    Tcl_Interp *interp,		/* Used for error reporting. */
    Tcl_Parse *parsePtr,	/* Points to a parse structure for the command
				 * created by Tcl_ParseCommand. */
    Command *cmdPtr,		/* Points to defintion of command being
				 * compiled. */
    CompileEnv *envPtr)		/* Holds resulting instructions. */
{
    Tcl_Token *tokenPtr;
    int isScalar, simpleVarName, localIndex;
    DefineLineInformation;	/* TIP #280 */

    if (parsePtr->numWords != 2) {
	return TCL_ERROR;
    }

    /*
     * Decide if we can use a frame slot for the var/array name or if we need
     * to emit code to compute and push the name at runtime. We use a frame
     * slot (entry in the array of local vars) if we are compiling a procedure
     * body and if the name is simple text that does not include namespace
     * qualifiers.
     */

    tokenPtr = TokenAfter(parsePtr->tokenPtr);
    PushVarName(interp, tokenPtr, envPtr, TCL_CREATE_VAR, &localIndex,
	    &simpleVarName, &isScalar, mapPtr->loc[eclIndex].line[1]);

    /*
     * Emit instruction to check the variable for existence.
     */

    if (simpleVarName) {
	if (isScalar) {
	    if (localIndex < 0) {
		TclEmitOpcode(INST_EXIST_STK, envPtr);
	    } else {
		TclEmitInstInt4(INST_EXIST_SCALAR, localIndex, envPtr);
	    }
	} else {
	    if (localIndex < 0) {
		TclEmitOpcode(INST_EXIST_ARRAY_STK, envPtr);
	    } else {
		TclEmitInstInt4(INST_EXIST_ARRAY, localIndex, envPtr);
	    }
	}
    } else {
	TclEmitOpcode(INST_EXIST_STK, envPtr);
    }

    return TCL_OK;
}

/*
 * Local Variables:
 * mode: c
 * c-basic-offset: 4
 * fill-column: 78
 * End:
 */
