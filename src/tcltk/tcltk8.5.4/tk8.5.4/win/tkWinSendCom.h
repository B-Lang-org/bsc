/*
 * tkWinSendCom.h --
 *
 *	This file provides procedures that implement the Windows "send"
 *	command, allowing commands to be passed from interpreter to
 *	interpreter.
 *
 * Copyright (C) 2002 Pat Thoyts <patthoyts@users.sourceforge.net>
 *
 * See the file "license.terms" for information on usage and redistribution of
 * this file, and for a DISCLAIMER OF ALL WARRANTIES.
 *
 * RCS: @(#) $Id: tkWinSendCom.h,v 1.3 2005/12/02 13:42:29 dkf Exp $
 */

#ifndef _tkWinSendCom_h_INCLUDE
#define _tkWinSendCom_h_INCLUDE

#include "tkWinInt.h"
#include <ole2.h>

#ifdef _MSC_VER
#   pragma comment (lib, "ole32.lib")
#   pragma comment (lib, "oleaut32.lib")
#   pragma comment (lib, "uuid.lib")
#endif

/*
 * TkWinSendCom CoClass structure
 */

typedef struct {
    IDispatchVtbl *lpVtbl;
    ISupportErrorInfoVtbl *lpVtbl2;
    long refcount;
    Tcl_Interp *interp;
} TkWinSendCom;

/*
 * TkWinSendCom Dispatch IDs
 */

#define TKWINSENDCOM_DISPID_SEND   1
#define TKWINSENDCOM_DISPID_ASYNC  2

/*
 * TkWinSendCom public functions
 */

HRESULT                 TkWinSendCom_CreateInstance(Tcl_Interp *interp,
                            REFIID riid, void **ppv);
int                     TkWinSend_QueueCommand(Tcl_Interp *interp,
                            Tcl_Obj *cmdPtr);
void                    SetExcepInfo(Tcl_Interp *interp,
                            EXCEPINFO *pExcepInfo);

#endif /* _tkWinSendCom_h_INCLUDE */

/*
 * Local Variables:
 * mode: c
 * End:
 */
