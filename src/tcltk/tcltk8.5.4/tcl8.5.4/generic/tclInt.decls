# tclInt.decls --
#
#	This file contains the declarations for all unsupported
#	functions that are exported by the Tcl library.  This file
#	is used to generate the tclIntDecls.h, tclIntPlatDecls.h,
#	tclIntStub.c, tclPlatStub.c, tclCompileDecls.h and tclCompileStub.c
#	files
#
# Copyright (c) 1998-1999 by Scriptics Corporation.
# Copyright (c) 2001 by Kevin B. Kenny.  All rights reserved.
# Copyright (c) 2007 Daniel A. Steffen <das@users.sourceforge.net>
#
# See the file "license.terms" for information on usage and redistribution
# of this file, and for a DISCLAIMER OF ALL WARRANTIES.
#
# RCS: @(#) $Id: tclInt.decls,v 1.121 2008/01/23 17:31:42 dgp Exp $

library tcl

# Define the unsupported generic interfaces.

interface tclInt

# Declare each of the functions in the unsupported internal Tcl
# interface.  These interfaces are allowed to changed between versions.
# Use at your own risk.  Note that the position of functions should not
# be changed between versions to avoid gratuitous incompatibilities.

# Replaced by Tcl_FSAccess in 8.4:
#declare 0 generic {
#    int TclAccess(CONST char *path, int mode)
#}
#declare 1 generic {
#    int TclAccessDeleteProc(TclAccessProc_ *proc)
#}
#declare 2 generic {
#    int TclAccessInsertProc(TclAccessProc_ *proc)
#}
declare 3 generic {
    void TclAllocateFreeObjects(void)
}
# Replaced by TclpChdir in 8.1:
#  declare 4 generic {
#      int TclChdir(Tcl_Interp *interp, char *dirName)
#  }
declare 5 {unix win} {
    int TclCleanupChildren(Tcl_Interp *interp, int numPids, Tcl_Pid *pidPtr,
	    Tcl_Channel errorChan)
}
declare 6 generic {
    void TclCleanupCommand(Command *cmdPtr)
}
declare 7 generic {
    int TclCopyAndCollapse(int count, CONST char *src, char *dst)
}
declare 8 generic {
    int TclCopyChannel(Tcl_Interp *interp, Tcl_Channel inChan,
	    Tcl_Channel outChan, int toRead, Tcl_Obj *cmdPtr)
}

# TclCreatePipeline unofficially exported for use by BLT.

declare 9 {unix win} {
    int TclCreatePipeline(Tcl_Interp *interp, int argc, CONST char **argv,
	    Tcl_Pid **pidArrayPtr, TclFile *inPipePtr, TclFile *outPipePtr,
	    TclFile *errFilePtr)
}
declare 10 generic {
    int TclCreateProc(Tcl_Interp *interp, Namespace *nsPtr,
	    CONST char *procName,
	    Tcl_Obj *argsPtr, Tcl_Obj *bodyPtr, Proc **procPtrPtr)
}
declare 11 generic {
    void TclDeleteCompiledLocalVars(Interp *iPtr, CallFrame *framePtr)
}
declare 12 generic {
    void TclDeleteVars(Interp *iPtr, TclVarHashTable *tablePtr)
}
# Removed in 8.5
#declare 13 generic {
#    int TclDoGlob(Tcl_Interp *interp, char *separators,
#	    Tcl_DString *headPtr, char *tail, Tcl_GlobTypeData *types)
#}
declare 14 generic {
    void TclDumpMemoryInfo(FILE *outFile)
}
# Removed in 8.1:
#  declare 15 generic {
#      void TclExpandParseValue(ParseValue *pvPtr, int needed)
#  }
declare 16 generic {
    void TclExprFloatError(Tcl_Interp *interp, double value)
}
# Removed in 8.4
#declare 17 generic {
#    int TclFileAttrsCmd(Tcl_Interp *interp, int objc, Tcl_Obj *CONST objv[])
#}
#declare 18 generic {
#    int TclFileCopyCmd(Tcl_Interp *interp, int argc, char **argv)
#}
#declare 19 generic {
#    int TclFileDeleteCmd(Tcl_Interp *interp, int argc, char **argv)
#}
#declare 20 generic {
#    int TclFileMakeDirsCmd(Tcl_Interp *interp, int argc, char **argv)
#}
#declare 21 generic {
#    int TclFileRenameCmd(Tcl_Interp *interp, int argc, char **argv)
#}
declare 22 generic {
    int TclFindElement(Tcl_Interp *interp, CONST char *listStr,
	    int listLength, CONST char **elementPtr, CONST char **nextPtr,
	    int *sizePtr, int *bracePtr)
}
declare 23 generic {
    Proc *TclFindProc(Interp *iPtr, CONST char *procName)
}
# Replaced with macro (see tclInt.h) in Tcl 8.5
#declare 24 generic {
#    int TclFormatInt(char *buffer, long n)
#}
declare 25 generic {
    void TclFreePackageInfo(Interp *iPtr)
}
# Removed in 8.1:
#  declare 26 generic {
#      char *TclGetCwd(Tcl_Interp *interp)
#  }
# Removed in 8.5
#declare 27 generic {
#    int TclGetDate(char *p, unsigned long now, long zone,
#	    unsigned long *timePtr)
#}
declare 28 generic {
    Tcl_Channel TclpGetDefaultStdChannel(int type)
}
# Removed in 8.4b2:
#declare 29 generic {
#    Tcl_Obj *TclGetElementOfIndexedArray(Tcl_Interp *interp,
#	    int localIndex, Tcl_Obj *elemPtr, int flags)
#}
# Replaced by char *TclGetEnv(CONST char *name, Tcl_DString *valuePtr) in 8.1:
#  declare 30 generic {
#      char *TclGetEnv(CONST char *name)
#  }
declare 31 generic {
    CONST char *TclGetExtension(CONST char *name)
}
declare 32 generic {
    int TclGetFrame(Tcl_Interp *interp, CONST char *str,
	    CallFrame **framePtrPtr)
}
# Removed in Tcl 8.5
#declare 33 generic {
#    TclCmdProcType TclGetInterpProc(void)
#}
declare 34 generic {
    int TclGetIntForIndex(Tcl_Interp *interp, Tcl_Obj *objPtr,
	    int endValue, int *indexPtr)
}
# Removed in 8.4b2:
#declare 35 generic {
#    Tcl_Obj *TclGetIndexedScalar(Tcl_Interp *interp, int localIndex,
#	    int flags)
#}
declare 36 generic {
    int TclGetLong(Tcl_Interp *interp, CONST char *str, long *longPtr)
}
declare 37 generic {
    int TclGetLoadedPackages(Tcl_Interp *interp, char *targetName)
}
declare 38 generic {
    int TclGetNamespaceForQualName(Tcl_Interp *interp, CONST char *qualName,
	    Namespace *cxtNsPtr, int flags, Namespace **nsPtrPtr,
	    Namespace **altNsPtrPtr, Namespace **actualCxtPtrPtr,
	    CONST char **simpleNamePtr)
}
declare 39 generic {
    TclObjCmdProcType TclGetObjInterpProc(void)
}
declare 40 generic {
    int TclGetOpenMode(Tcl_Interp *interp, CONST char *str, int *seekFlagPtr)
}
declare 41 generic {
    Tcl_Command TclGetOriginalCommand(Tcl_Command command)
}
declare 42 generic {
    char *TclpGetUserHome(CONST char *name, Tcl_DString *bufferPtr)
}
# Removed in Tcl 8.5a2
#declare 43 generic {
#    int TclGlobalInvoke(Tcl_Interp *interp, int argc, CONST84 char **argv,
#	    int flags)
#}
declare 44 generic {
    int TclGuessPackageName(CONST char *fileName, Tcl_DString *bufPtr)
}
declare 45 generic {
    int TclHideUnsafeCommands(Tcl_Interp *interp)
}
declare 46 generic {
    int TclInExit(void)
}
# Removed in 8.4b2:
#declare 47 generic {
#    Tcl_Obj *TclIncrElementOfIndexedArray(Tcl_Interp *interp,
#	    int localIndex, Tcl_Obj *elemPtr, long incrAmount)
#}
# Removed in 8.4b2:
#declare 48 generic {
#    Tcl_Obj *TclIncrIndexedScalar(Tcl_Interp *interp, int localIndex,
#	    long incrAmount)
#}
#declare 49 generic {
#    Tcl_Obj *TclIncrVar2(Tcl_Interp *interp, Tcl_Obj *part1Ptr,
#	    Tcl_Obj *part2Ptr, long incrAmount, int part1NotParsed)
#}
declare 50 generic {
    void TclInitCompiledLocals(Tcl_Interp *interp, CallFrame *framePtr,
	    Namespace *nsPtr)
}
declare 51 generic {
    int TclInterpInit(Tcl_Interp *interp)
}
# Removed in Tcl 8.5a2
#declare 52 generic {
#    int TclInvoke(Tcl_Interp *interp, int argc, CONST84 char **argv,
#	    int flags)
#}
declare 53 generic {
    int TclInvokeObjectCommand(ClientData clientData, Tcl_Interp *interp,
	    int argc, CONST84 char **argv)
}
declare 54 generic {
    int TclInvokeStringCommand(ClientData clientData, Tcl_Interp *interp,
	    int objc, Tcl_Obj *CONST objv[])
}
declare 55 generic {
    Proc *TclIsProc(Command *cmdPtr)
}
# Replaced with TclpLoadFile in 8.1:
#  declare 56 generic {
#      int TclLoadFile(Tcl_Interp *interp, char *fileName, char *sym1,
#  	    char *sym2, Tcl_PackageInitProc **proc1Ptr,
#  	    Tcl_PackageInitProc **proc2Ptr)
#  }
# Signature changed to take a length in 8.1:
#  declare 57 generic {
#      int TclLooksLikeInt(char *p)
#  }
declare 58 generic {
    Var *TclLookupVar(Tcl_Interp *interp, CONST char *part1, CONST char *part2,
	    int flags, CONST char *msg, int createPart1, int createPart2,
	    Var **arrayPtrPtr)
}
# Replaced by Tcl_FSMatchInDirectory in 8.4
#declare 59 generic {
#    int TclpMatchFiles(Tcl_Interp *interp, char *separators,
#	    Tcl_DString *dirPtr, char *pattern, char *tail)
#}
declare 60 generic {
    int TclNeedSpace(CONST char *start, CONST char *end)
}
declare 61 generic {
    Tcl_Obj *TclNewProcBodyObj(Proc *procPtr)
}
declare 62 generic {
    int TclObjCommandComplete(Tcl_Obj *cmdPtr)
}
declare 63 generic {
    int TclObjInterpProc(ClientData clientData, Tcl_Interp *interp,
	    int objc, Tcl_Obj *CONST objv[])
}
declare 64 generic {
    int TclObjInvoke(Tcl_Interp *interp, int objc, Tcl_Obj *CONST objv[],
	    int flags)
}
# Removed in Tcl 8.5a2
#declare 65 generic {
#    int TclObjInvokeGlobal(Tcl_Interp *interp, int objc,
#	    Tcl_Obj *CONST objv[], int flags)
#}
#declare 66 generic {
#    int TclOpenFileChannelDeleteProc(TclOpenFileChannelProc_ *proc)
#}
#declare 67 generic {
#    int TclOpenFileChannelInsertProc(TclOpenFileChannelProc_ *proc)
#}
# Replaced by Tcl_FSAccess in 8.4:
#declare 68 generic {
#    int TclpAccess(CONST char *path, int mode)
#}
declare 69 generic {
    char *TclpAlloc(unsigned int size)
}
#declare 70 generic {
#    int TclpCopyFile(CONST char *source, CONST char *dest)
#}
#declare 71 generic {
#    int TclpCopyDirectory(CONST char *source, CONST char *dest,
#	    Tcl_DString *errorPtr)
#}
#declare 72 generic {
#    int TclpCreateDirectory(CONST char *path)
#}
#declare 73 generic {
#    int TclpDeleteFile(CONST char *path)
#}
declare 74 generic {
    void TclpFree(char *ptr)
}
declare 75 generic {
    unsigned long TclpGetClicks(void)
}
declare 76 generic {
    unsigned long TclpGetSeconds(void)
}

# deprecated
declare 77 generic {
    void TclpGetTime(Tcl_Time *time)
}
declare 78 generic {
    int TclpGetTimeZone(unsigned long time)
}
# Replaced by Tcl_FSListVolumes in 8.4:
#declare 79 generic {
#    int TclpListVolumes(Tcl_Interp *interp)
#}
# Replaced by Tcl_FSOpenFileChannel in 8.4:
#declare 80 generic {
#    Tcl_Channel TclpOpenFileChannel(Tcl_Interp *interp, char *fileName,
#	    char *modeString, int permissions)
#}
declare 81 generic {
    char *TclpRealloc(char *ptr, unsigned int size)
}
#declare 82 generic {
#    int TclpRemoveDirectory(CONST char *path, int recursive,
#	    Tcl_DString *errorPtr)
#}
#declare 83 generic {
#    int TclpRenameFile(CONST char *source, CONST char *dest)
#}
# Removed in 8.1:
#  declare 84 generic {
#      int TclParseBraces(Tcl_Interp *interp, char *str, char **termPtr,
#  	    ParseValue *pvPtr)
#  }
#  declare 85 generic {
#      int TclParseNestedCmd(Tcl_Interp *interp, char *str, int flags,
#  	    char **termPtr, ParseValue *pvPtr)
#  }
#  declare 86 generic {
#      int TclParseQuotes(Tcl_Interp *interp, char *str, int termChar,
#  	    int flags, char **termPtr, ParseValue *pvPtr)
#  }
#  declare 87 generic {
#      void TclPlatformInit(Tcl_Interp *interp)
#  }
declare 88 generic {
    char *TclPrecTraceProc(ClientData clientData, Tcl_Interp *interp,
	    CONST char *name1, CONST char *name2, int flags)
}
declare 89 generic {
    int TclPreventAliasLoop(Tcl_Interp *interp, Tcl_Interp *cmdInterp,
	    Tcl_Command cmd)
}
# Removed in 8.1 (only available if compiled with TCL_COMPILE_DEBUG):
#  declare 90 generic {
#      void TclPrintByteCodeObj(Tcl_Interp *interp, Tcl_Obj *objPtr)
#  }
declare 91 generic {
    void TclProcCleanupProc(Proc *procPtr)
}
declare 92 generic {
    int TclProcCompileProc(Tcl_Interp *interp, Proc *procPtr,
	    Tcl_Obj *bodyPtr, Namespace *nsPtr, CONST char *description,
	    CONST char *procName)
}
declare 93 generic {
    void TclProcDeleteProc(ClientData clientData)
}
# Removed in Tcl 8.5:
#declare 94 generic {
#    int TclProcInterpProc(ClientData clientData, Tcl_Interp *interp,
#	    int argc, CONST84 char **argv)
#}
# Replaced by Tcl_FSStat in 8.4:
#declare 95 generic {
#    int TclpStat(CONST char *path, Tcl_StatBuf *buf)
#}
declare 96 generic {
    int TclRenameCommand(Tcl_Interp *interp, CONST char *oldName,
            CONST char *newName)
}
declare 97 generic {
    void TclResetShadowedCmdRefs(Tcl_Interp *interp, Command *newCmdPtr)
}
declare 98 generic {
    int TclServiceIdle(void)
}
# Removed in 8.4b2:
#declare 99 generic {
#    Tcl_Obj *TclSetElementOfIndexedArray(Tcl_Interp *interp, int localIndex,
#	    Tcl_Obj *elemPtr, Tcl_Obj *objPtr, int flags)
#}
# Removed in 8.4b2:
#declare 100 generic {
#    Tcl_Obj *TclSetIndexedScalar(Tcl_Interp *interp, int localIndex,
#	    Tcl_Obj *objPtr, int flags)
#}
declare 101 generic {
    char *TclSetPreInitScript(char *string)
}
declare 102 generic {
    void TclSetupEnv(Tcl_Interp *interp)
}
declare 103 generic {
    int TclSockGetPort(Tcl_Interp *interp, CONST char *str, CONST char *proto,
	    int *portPtr)
}
declare 104 {unix win} {
    int TclSockMinimumBuffers(int sock, int size)
}
# Replaced by Tcl_FSStat in 8.4:
#declare 105 generic {
#    int TclStat(CONST char *path, Tcl_StatBuf *buf)
#}
#declare 106 generic {
#    int TclStatDeleteProc(TclStatProc_ *proc)
#}
#declare 107 generic {
#    int TclStatInsertProc(TclStatProc_ *proc)
#}
declare 108 generic {
    void TclTeardownNamespace(Namespace *nsPtr)
}
declare 109 generic {
    int TclUpdateReturnInfo(Interp *iPtr)
}
# Removed in 8.1:
#  declare 110 generic {
#      char *TclWordEnd(char *start, char *lastChar, int nested, int *semiPtr)
#  }

# Procedures used in conjunction with Tcl namespaces. They are
# defined here instead of in tcl.decls since they are not stable yet.

declare 111 generic {
    void Tcl_AddInterpResolvers(Tcl_Interp *interp, CONST char *name,
	    Tcl_ResolveCmdProc *cmdProc, Tcl_ResolveVarProc *varProc,
	    Tcl_ResolveCompiledVarProc *compiledVarProc)
}
declare 112 generic {
    int Tcl_AppendExportList(Tcl_Interp *interp, Tcl_Namespace *nsPtr,
	    Tcl_Obj *objPtr)
}
declare 113 generic {
    Tcl_Namespace *Tcl_CreateNamespace(Tcl_Interp *interp, CONST char *name,
	    ClientData clientData, Tcl_NamespaceDeleteProc *deleteProc)
}
declare 114 generic {
    void Tcl_DeleteNamespace(Tcl_Namespace *nsPtr)
}
declare 115 generic {
    int Tcl_Export(Tcl_Interp *interp, Tcl_Namespace *nsPtr,
	    CONST char *pattern, int resetListFirst)
}
declare 116 generic {
    Tcl_Command Tcl_FindCommand(Tcl_Interp *interp, CONST char *name,
	    Tcl_Namespace *contextNsPtr, int flags)
}
declare 117 generic {
    Tcl_Namespace *Tcl_FindNamespace(Tcl_Interp *interp, CONST char *name,
	    Tcl_Namespace *contextNsPtr, int flags)
}
declare 118 generic {
    int Tcl_GetInterpResolvers(Tcl_Interp *interp, CONST char *name,
	    Tcl_ResolverInfo *resInfo)
}
declare 119 generic {
    int Tcl_GetNamespaceResolvers(Tcl_Namespace *namespacePtr,
	    Tcl_ResolverInfo *resInfo)
}
declare 120 generic {
    Tcl_Var Tcl_FindNamespaceVar(Tcl_Interp *interp, CONST char *name,
	    Tcl_Namespace *contextNsPtr, int flags)
}
declare 121 generic {
    int Tcl_ForgetImport(Tcl_Interp *interp, Tcl_Namespace *nsPtr,
	    CONST char *pattern)
}
declare 122 generic {
    Tcl_Command Tcl_GetCommandFromObj(Tcl_Interp *interp, Tcl_Obj *objPtr)
}
declare 123 generic {
    void Tcl_GetCommandFullName(Tcl_Interp *interp, Tcl_Command command,
	    Tcl_Obj *objPtr)
}
declare 124 generic {
    Tcl_Namespace *Tcl_GetCurrentNamespace(Tcl_Interp *interp)
}
declare 125 generic {
    Tcl_Namespace *Tcl_GetGlobalNamespace(Tcl_Interp *interp)
}
declare 126 generic {
    void Tcl_GetVariableFullName(Tcl_Interp *interp, Tcl_Var variable,
	    Tcl_Obj *objPtr)
}
declare 127 generic {
    int Tcl_Import(Tcl_Interp *interp, Tcl_Namespace *nsPtr,
	    CONST char *pattern, int allowOverwrite)
}
declare 128 generic {
    void Tcl_PopCallFrame(Tcl_Interp *interp)
}
declare 129 generic {
    int Tcl_PushCallFrame(Tcl_Interp *interp, Tcl_CallFrame *framePtr,
	    Tcl_Namespace *nsPtr, int isProcCallFrame)
}
declare 130 generic {
    int Tcl_RemoveInterpResolvers(Tcl_Interp *interp, CONST char *name)
}
declare 131 generic {
    void Tcl_SetNamespaceResolvers(Tcl_Namespace *namespacePtr,
	    Tcl_ResolveCmdProc *cmdProc, Tcl_ResolveVarProc *varProc,
	    Tcl_ResolveCompiledVarProc *compiledVarProc)
}
declare 132 generic {
    int TclpHasSockets(Tcl_Interp *interp)
}
declare 133 generic {
    struct tm *TclpGetDate(CONST time_t *time, int useGMT)
}
# Removed in 8.5
#declare 134 generic {
#    size_t TclpStrftime(char *s, size_t maxsize, CONST char *format,
#	    CONST struct tm *t, int useGMT)
#}
#declare 135 generic {
#    int TclpCheckStackSpace(void)
#}

# Added in 8.1:

#declare 137 generic {
#   int TclpChdir(CONST char *dirName)
#}
declare 138 generic {
    CONST84_RETURN char *TclGetEnv(CONST char *name, Tcl_DString *valuePtr)
}
#declare 139 generic {
#    int TclpLoadFile(Tcl_Interp *interp, char *fileName, char *sym1,
#	    char *sym2, Tcl_PackageInitProc **proc1Ptr,
#	    Tcl_PackageInitProc **proc2Ptr, ClientData *clientDataPtr)
#}
#declare 140 generic {
#    int TclLooksLikeInt(CONST char *bytes, int length)
#}
# This is used by TclX, but should otherwise be considered private
declare 141 generic {
    CONST84_RETURN char *TclpGetCwd(Tcl_Interp *interp, Tcl_DString *cwdPtr)
}
declare 142 generic {
    int TclSetByteCodeFromAny(Tcl_Interp *interp, Tcl_Obj *objPtr,
	    CompileHookProc *hookProc, ClientData clientData)
}
declare 143 generic {
    int TclAddLiteralObj(struct CompileEnv *envPtr, Tcl_Obj *objPtr,
	    LiteralEntry **litPtrPtr)
}
declare 144 generic {
    void TclHideLiteral(Tcl_Interp *interp, struct CompileEnv *envPtr,
	    int index)
}
declare 145 generic {
    struct AuxDataType *TclGetAuxDataType(char *typeName)
}
declare 146 generic {
    TclHandle TclHandleCreate(VOID *ptr)
}
declare 147 generic {
    void TclHandleFree(TclHandle handle)
}
declare 148 generic {
    TclHandle TclHandlePreserve(TclHandle handle)
}
declare 149 generic {
    void TclHandleRelease(TclHandle handle)
}

# Added for Tcl 8.2

declare 150 generic {
    int TclRegAbout(Tcl_Interp *interp, Tcl_RegExp re)
}
declare 151 generic {
    void TclRegExpRangeUniChar(Tcl_RegExp re, int index, int *startPtr,
	    int *endPtr)
}
declare 152 generic {
    void TclSetLibraryPath(Tcl_Obj *pathPtr)
}
declare 153 generic {
    Tcl_Obj *TclGetLibraryPath(void)
}

# moved to tclTest.c (static) in 8.3.2/8.4a2
#declare 154 generic {
#    int TclTestChannelCmd(ClientData clientData,
#    Tcl_Interp *interp, int argc, char **argv)
#}
#declare 155 generic {
#    int TclTestChannelEventCmd(ClientData clientData,
#	     Tcl_Interp *interp, int argc, char **argv)
#}

declare 156 generic {
    void TclRegError(Tcl_Interp *interp, CONST char *msg,
	    int status)
}
declare 157 generic {
    Var *TclVarTraceExists(Tcl_Interp *interp, CONST char *varName)
}
declare 158 generic {
    void TclSetStartupScriptFileName(CONST char *filename)
}
declare 159 generic {
    CONST84_RETURN char *TclGetStartupScriptFileName(void)
}
#declare 160 generic {
#    int TclpMatchFilesTypes(Tcl_Interp *interp, char *separators,
#	    Tcl_DString *dirPtr, char *pattern, char *tail,
#	    GlobTypeData *types)
#}

# new in 8.3.2/8.4a2
declare 161 generic {
    int TclChannelTransform(Tcl_Interp *interp, Tcl_Channel chan,
	    Tcl_Obj *cmdObjPtr)
}
declare 162 generic {
    void TclChannelEventScriptInvoker(ClientData clientData, int flags)
}

# ALERT: The result of 'TclGetInstructionTable' is actually an
# "InstructionDesc*" but we do not want to describe this structure in
# "tclInt.h". It is described in "tclCompile.h". Use a cast to the
# correct type when calling this procedure.

declare 163 generic {
    void *TclGetInstructionTable(void)
}

# ALERT: The argument of 'TclExpandCodeArray' is actually a
# "CompileEnv*" but we do not want to describe this structure in
# "tclInt.h". It is described in "tclCompile.h".

declare 164 generic {
    void TclExpandCodeArray(void *envPtr)
}

# These functions are vfs aware, but are generally only useful internally.
declare 165 generic {
    void TclpSetInitialEncodings(void)
}

# New function due to TIP #33
declare 166 generic {
    int TclListObjSetElement(Tcl_Interp *interp, Tcl_Obj *listPtr,
	    int index, Tcl_Obj *valuePtr)
}

# VFS-aware versions of Tcl*StartupScriptFileName (158 and 159 above)
declare 167 generic {
    void TclSetStartupScriptPath(Tcl_Obj *pathPtr)
}
declare 168 generic {
    Tcl_Obj *TclGetStartupScriptPath(void)
}
# variant of Tcl_UtfNCmp that takes n as bytes, not chars
declare 169 generic {
    int TclpUtfNcmp2(CONST char *s1, CONST char *s2, unsigned long n)
}
declare 170 generic {
    int TclCheckInterpTraces(Tcl_Interp *interp, CONST char *command,
            int numChars, Command *cmdPtr, int result, int traceFlags,
	    int objc, Tcl_Obj *CONST objv[])
}
declare 171 generic {
    int TclCheckExecutionTraces(Tcl_Interp *interp, CONST char *command,
            int numChars, Command *cmdPtr, int result, int traceFlags,
	    int objc, Tcl_Obj *CONST objv[])
}
declare 172 generic {
    int TclInThreadExit(void)
}

# added for 8.4.2

declare 173 generic {
    int TclUniCharMatch(CONST Tcl_UniChar *string, int strLen,
	    CONST Tcl_UniChar *pattern, int ptnLen, int flags)
}

# added for 8.4.3

#declare 174 generic {
#    Tcl_Obj *TclIncrWideVar2(Tcl_Interp *interp, Tcl_Obj *part1Ptr,
#	    Tcl_Obj *part2Ptr, Tcl_WideInt wideIncrAmount, int part1NotParsed)
#}

# Factoring out of trace code

declare 175 generic {
    int TclCallVarTraces(Interp *iPtr, Var *arrayPtr, Var *varPtr,
	    CONST char *part1, CONST char *part2, int flags, int leaveErrMsg)
}
declare 176 generic {
    void TclCleanupVar(Var *varPtr, Var *arrayPtr)
}
declare 177 generic {
    void TclVarErrMsg(Tcl_Interp *interp, CONST char *part1, CONST char *part2,
	    CONST char *operation, CONST char *reason)
}
declare 178 generic {
    void Tcl_SetStartupScript(Tcl_Obj *pathPtr, CONST char* encodingName)
}
declare 179 generic {
    Tcl_Obj *Tcl_GetStartupScript(CONST char **encodingNamePtr)
}

# REMOVED
# Allocate lists without copying arrays
# declare 180 generic {
#    Tcl_Obj *TclNewListObjDirect(int objc, Tcl_Obj **objv)
# }
#declare 181 generic {
#    Tcl_Obj *TclDbNewListObjDirect(int objc, Tcl_Obj **objv,
#	    CONST char *file, int line)
#}

# TclpGmtime and TclpLocaltime promoted to the generic interface from unix

declare 182 generic {
     struct tm *TclpLocaltime(CONST time_t *clock)
}
declare 183 generic {
     struct tm *TclpGmtime(CONST time_t *clock)
}

# For the new "Thread Storage" subsystem.

### REMOVED on grounds it should never have been exposed. All these
### functions are now either static in tclThreadStorage.c or
### MODULE_SCOPE.
# declare 184 generic {
#      void TclThreadStorageLockInit(void)
# }
# declare 185 generic {
#      void TclThreadStorageLock(void)
# }
# declare 186 generic {
#      void TclThreadStorageUnlock(void)
# }
# declare 187 generic {
#      void TclThreadStoragePrint(FILE *outFile, int flags)
# }
# declare 188 generic {
#      Tcl_HashTable *TclThreadStorageGetHashTable(Tcl_ThreadId id)
# }
# declare 189 generic {
#      Tcl_HashTable *TclThreadStorageInit(Tcl_ThreadId id, void *reserved)
# }
# declare 190 generic {
#      void TclThreadStorageDataKeyInit(Tcl_ThreadDataKey *keyPtr)
# }
# declare 191 generic {
#      void *TclThreadStorageDataKeyGet(Tcl_ThreadDataKey *keyPtr)
# }
# declare 192 generic {
#      void TclThreadStorageDataKeySet(Tcl_ThreadDataKey *keyPtr, void *data)
# }
# declare 193 generic {
#      void TclFinalizeThreadStorageThread(Tcl_ThreadId id)
# }
# declare 194 generic {
#      void TclFinalizeThreadStorage(void)
# }
# declare 195 generic {
#      void TclFinalizeThreadStorageData(Tcl_ThreadDataKey *keyPtr)
# }
# declare 196 generic {
#      void TclFinalizeThreadStorageDataKey(Tcl_ThreadDataKey *keyPtr)
# }

#
# Added in tcl8.5a5 for compiler/executor experimentation.
# Disabled in Tcl 8.5.1; experiments terminated. :/
#
#declare 197 generic {
#    int TclCompEvalObj(Tcl_Interp *interp, Tcl_Obj *objPtr,
#		        CONST CmdFrame* invoker, int word)
#}
declare 198 generic {
    int TclObjGetFrame(Tcl_Interp *interp, Tcl_Obj *objPtr,
	    CallFrame **framePtrPtr)
}

#declare 199 generic {
#    int TclMatchIsTrivial(CONST char *pattern)
#}

# 200-208 exported for use by the test suite [Bug 1054748]
declare 200 generic {
    int TclpObjRemoveDirectory(Tcl_Obj *pathPtr, int recursive,
	Tcl_Obj **errorPtr)
}
declare 201 generic {
    int TclpObjCopyDirectory(Tcl_Obj *srcPathPtr, Tcl_Obj *destPathPtr,
	Tcl_Obj **errorPtr)
}
declare 202 generic {
    int TclpObjCreateDirectory(Tcl_Obj *pathPtr)
}
declare 203 generic {
    int TclpObjDeleteFile(Tcl_Obj *pathPtr)
}
declare 204 generic {
    int TclpObjCopyFile(Tcl_Obj *srcPathPtr, Tcl_Obj *destPathPtr)
}
declare 205 generic {
    int TclpObjRenameFile(Tcl_Obj *srcPathPtr, Tcl_Obj *destPathPtr)
}
declare 206 generic {
    int TclpObjStat(Tcl_Obj *pathPtr, Tcl_StatBuf *buf)
}
declare 207 generic {
    int TclpObjAccess(Tcl_Obj *pathPtr, int mode)
}
declare 208 generic {
    Tcl_Channel TclpOpenFileChannel(Tcl_Interp *interp,
	    Tcl_Obj *pathPtr, int mode, int permissions)
}
# Made public by TIP 258
#declare 209 generic {
#    Tcl_Obj * TclGetEncodingSearchPath(void)
#}
#declare 210 generic {
#    int TclSetEncodingSearchPath(Tcl_Obj *searchPath)
#}
#declare 211 generic {
#    CONST char * TclpGetEncodingNameFromEnvironment(Tcl_DString *bufPtr)
#}
declare 212 generic {
    void TclpFindExecutable(CONST char *argv0)
}
declare 213 generic {
    Tcl_Obj * TclGetObjNameOfExecutable(void)
}
declare 214 generic {
    void TclSetObjNameOfExecutable(Tcl_Obj *name, Tcl_Encoding encoding)
}
declare 215 generic {
    void * TclStackAlloc(Tcl_Interp *interp, int numBytes)
}
declare 216 generic {
    void TclStackFree(Tcl_Interp *interp, void *freePtr)
}
declare 217 generic {
    int TclPushStackFrame(Tcl_Interp *interp, Tcl_CallFrame **framePtrPtr,
            Tcl_Namespace *namespacePtr, int isProcCallFrame )
}
declare 218 generic {
    void TclPopStackFrame(Tcl_Interp *interp)
}

# for use in tclTest.c
declare 224 generic {
    TclPlatformType *TclGetPlatform(void)
}

#
declare 225 generic {
    Tcl_Obj *TclTraceDictPath(Tcl_Interp *interp, Tcl_Obj *rootPtr,
	    int keyc, Tcl_Obj *CONST keyv[], int flags)
}
declare 226 generic {
    int TclObjBeingDeleted(Tcl_Obj *objPtr)
}
declare 227 generic {
    void TclSetNsPath(Namespace *nsPtr, int pathLength,
            Tcl_Namespace *pathAry[])
}
declare 228 generic {
    int TclObjInterpProcCore(register Tcl_Interp *interp, Tcl_Obj *procNameObj,
             int skip, ProcErrorProc errorProc)
}
declare 229 generic {
    int	TclPtrMakeUpvar(Tcl_Interp *interp, Var *otherP1Ptr,
	    CONST char *myName, int myFlags, int index)
}
declare 230 generic {
    Var *TclObjLookupVar(Tcl_Interp *interp, Tcl_Obj *part1Ptr,
	    CONST char *part2, int flags, CONST char *msg,
	    CONST int createPart1, CONST int createPart2, Var **arrayPtrPtr)
}
declare 231 generic {
    int	TclGetNamespaceFromObj(Tcl_Interp *interp, Tcl_Obj *objPtr,
	    Tcl_Namespace **nsPtrPtr)
}

# Bits and pieces of TIP#280's guts
declare 232 generic {
    int TclEvalObjEx(Tcl_Interp *interp, Tcl_Obj *objPtr, int flags,
	    const CmdFrame *invoker, int word)
}
declare 233 generic {
    void TclGetSrcInfoForPc(CmdFrame *contextPtr)
}

# Exports for VarReform compat: Itcl, XOTcl like to peek into our varTables :(
declare 234 generic {
    Var *TclVarHashCreateVar(TclVarHashTable *tablePtr, const char *key,
             int *newPtr)
}
declare 235 generic {
    void TclInitVarHashTable(TclVarHashTable *tablePtr, Namespace *nsPtr)
}


declare 236 generic {
    void TclBackgroundException(Tcl_Interp *interp, int code)
}

##############################################################################

# Define the platform specific internal Tcl interface. These functions are
# only available on the designated platform.

interface tclIntPlat

################################
# Windows specific functions

declare 0 win {
    void TclWinConvertError(DWORD errCode)
}
declare 1 win {
    void TclWinConvertWSAError(DWORD errCode)
}
declare 2 win {
    struct servent *TclWinGetServByName(CONST char *nm,
	    CONST char *proto)
}
declare 3 win {
    int TclWinGetSockOpt(int s, int level, int optname,
	    char FAR *optval, int FAR *optlen)
}
declare 4 win {
    HINSTANCE TclWinGetTclInstance(void)
}
# Removed in 8.1:
#  declare 5 win {
#      HINSTANCE TclWinLoadLibrary(char *name)
#  }
declare 6 win {
    u_short TclWinNToHS(u_short ns)
}
declare 7 win {
    int TclWinSetSockOpt(int s, int level, int optname,
	    CONST char FAR *optval, int optlen)
}
declare 8 win {
    unsigned long TclpGetPid(Tcl_Pid pid)
}
declare 9 win {
    int TclWinGetPlatformId(void)
}
# Removed in 8.3.1 (for Win32s only)
#declare 10 win {
#    int TclWinSynchSpawn(void *args, int type, void **trans, Tcl_Pid *pidPtr)
#}

# Pipe channel functions

declare 11 win {
    void TclGetAndDetachPids(Tcl_Interp *interp, Tcl_Channel chan)
}
declare 12 win {
    int TclpCloseFile(TclFile file)
}
declare 13 win {
    Tcl_Channel TclpCreateCommandChannel(TclFile readFile,
	    TclFile writeFile, TclFile errorFile, int numPids, Tcl_Pid *pidPtr)
}
declare 14 win {
    int TclpCreatePipe(TclFile *readPipe, TclFile *writePipe)
}
declare 15 win {
    int TclpCreateProcess(Tcl_Interp *interp, int argc, CONST char **argv,
	    TclFile inputFile, TclFile outputFile, TclFile errorFile,
	    Tcl_Pid *pidPtr)
}
# Signature changed in 8.1:
#  declare 16 win {
#      TclFile TclpCreateTempFile(char *contents, Tcl_DString *namePtr)
#  }
#  declare 17 win {
#      char *TclpGetTZName(void)
#  }
declare 18 win {
    TclFile TclpMakeFile(Tcl_Channel channel, int direction)
}
declare 19 win {
    TclFile TclpOpenFile(CONST char *fname, int mode)
}
declare 20 win {
    void TclWinAddProcess(HANDLE hProcess, DWORD id)
}

# removed permanently for 8.4
#declare 21 win {
#    void TclpAsyncMark(Tcl_AsyncHandler async)
#}

# Added in 8.1:
declare 22 win {
    TclFile TclpCreateTempFile(CONST char *contents)
}
declare 23 win {
    char *TclpGetTZName(int isdst)
}
declare 24 win {
    char *TclWinNoBackslash(char *path)
}
# replaced by generic TclGetPlatform
#declare 25 win {
#    TclPlatformType *TclWinGetPlatform(void)
#}
declare 26 win {
    void TclWinSetInterfaces(int wide)
}

# Added in Tcl 8.3.3 / 8.4

declare 27 win {
    void TclWinFlushDirtyChannels(void)
}

# Added in 8.4.2

declare 28 win {
    void TclWinResetInterfaces(void)
}
declare 29 win {
    int TclWinCPUID( unsigned int index, unsigned int *regs )
}

################################
# Unix specific functions

# Pipe channel functions

declare 0 unix {
    void TclGetAndDetachPids(Tcl_Interp *interp, Tcl_Channel chan)
}
declare 1 unix {
    int TclpCloseFile(TclFile file)
}
declare 2 unix {
    Tcl_Channel TclpCreateCommandChannel(TclFile readFile,
	    TclFile writeFile, TclFile errorFile, int numPids, Tcl_Pid *pidPtr)
}
declare 3 unix {
    int TclpCreatePipe(TclFile *readPipe, TclFile *writePipe)
}
declare 4 unix {
    int TclpCreateProcess(Tcl_Interp *interp, int argc, CONST char **argv,
	    TclFile inputFile, TclFile outputFile, TclFile errorFile,
	    Tcl_Pid *pidPtr)
}
# Signature changed in 8.1:
#  declare 5 unix {
#      TclFile TclpCreateTempFile(char *contents, Tcl_DString *namePtr)
#  }
declare 6 unix {
    TclFile TclpMakeFile(Tcl_Channel channel, int direction)
}
declare 7 unix {
    TclFile TclpOpenFile(CONST char *fname, int mode)
}
declare 8 unix {
    int TclUnixWaitForFile(int fd, int mask, int timeout)
}

# Added in 8.1:

declare 9 unix {
    TclFile TclpCreateTempFile(CONST char *contents)
}

# Added in 8.4:

declare 10 unix {
    Tcl_DirEntry *TclpReaddir(DIR *dir)
}
# Slots 11 and 12 are forwarders for functions that were promoted to
# generic Stubs
declare 11 unix {
    struct tm *TclpLocaltime_unix(CONST time_t *clock)
}
declare 12 unix {
    struct tm *TclpGmtime_unix(CONST time_t *clock)
}
declare 13 unix {
    char *TclpInetNtoa(struct in_addr addr)
}

# Added in 8.5:

declare 14 unix {
    int TclUnixCopyFile(CONST char *src, CONST char *dst,
	    CONST Tcl_StatBuf *statBufPtr, int dontCopyAtts)
}

################################
# Mac OS X specific functions

declare 15 macosx {
    int TclMacOSXGetFileAttribute(Tcl_Interp *interp, int objIndex,
	    Tcl_Obj *fileName, Tcl_Obj **attributePtrPtr)
}
declare 16 macosx {
    int TclMacOSXSetFileAttribute(Tcl_Interp *interp, int objIndex,
	    Tcl_Obj *fileName, Tcl_Obj *attributePtr)
}
declare 17 macosx {
    int TclMacOSXCopyFileAttributes(CONST char *src, CONST char *dst,
	    CONST Tcl_StatBuf *statBufPtr)
}
declare 18 macosx {
    int TclMacOSXMatchType(Tcl_Interp *interp, CONST char *pathName,
	    CONST char *fileName, Tcl_StatBuf *statBufPtr,
	    Tcl_GlobTypeData *types)
}
