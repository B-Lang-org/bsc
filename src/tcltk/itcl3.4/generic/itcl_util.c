/*
 * ------------------------------------------------------------------------
 *      PACKAGE:  [incr Tcl]
 *  DESCRIPTION:  Object-Oriented Extensions to Tcl
 *
 *  [incr Tcl] provides object-oriented extensions to Tcl, much as
 *  C++ provides object-oriented extensions to C.  It provides a means
 *  of encapsulating related procedures together with their shared data
 *  in a local namespace that is hidden from the outside world.  It
 *  promotes code re-use through inheritance.  More than anything else,
 *  it encourages better organization of Tcl applications through the
 *  object-oriented paradigm, leading to code that is easier to
 *  understand and maintain.
 *
 *  This segment provides common utility functions used throughout
 *  the other [incr Tcl] source files.
 *
 * ========================================================================
 *  AUTHOR:  Michael J. McLennan
 *           Bell Labs Innovations for Lucent Technologies
 *           mmclennan@lucent.com
 *           http://www.tcltk.com/itcl
 *
 *     RCS:  $Id: itcl_util.c,v 1.18 2007/08/07 20:05:30 msofer Exp $
 * ========================================================================
 *           Copyright (c) 1993-1998  Lucent Technologies, Inc.
 * ------------------------------------------------------------------------
 * See the file "license.terms" for information on usage and redistribution
 * of this file, and for a DISCLAIMER OF ALL WARRANTIES.
 */
#include "itclInt.h"

/*
 *  POOL OF LIST ELEMENTS FOR LINKED LIST
 */
static Itcl_ListElem *listPool = NULL;
static int listPoolLen = 0;

#define ITCL_VALID_LIST 0x01face10  /* magic bit pattern for validation */
#define ITCL_LIST_POOL_SIZE 200     /* max number of elements in listPool */


/*
 *  These records are used to keep track of reference-counted data
 *  for Itcl_PreserveData and Itcl_ReleaseData.
 */
typedef struct ItclPreservedData {
    ClientData data;                /* reference to data */
    int usage;                      /* number of active uses */
    Tcl_FreeProc *fproc;            /* procedure used to free data */
} ItclPreservedData;

static Tcl_HashTable *ItclPreservedList = NULL;
TCL_DECLARE_MUTEX(ItclPreservedListLock)

/*
 *  This structure is used to take a snapshot of the interpreter
 *  state in Itcl_SaveInterpState.  You can snapshot the state,
 *  execute a command, and then back up to the result or the
 *  error that was previously in progress.
 */
typedef struct InterpState {
    int validate;                   /* validation stamp */
    int status;                     /* return code status */
    Tcl_Obj *objResult;             /* result object */
    char *errorInfo;                /* contents of errorInfo variable */
    char *errorCode;                /* contents of errorCode variable */
} InterpState;

#define TCL_STATE_VALID 0x01233210  /* magic bit pattern for validation */


/*
 * ------------------------------------------------------------------------
 *  Itcl_Assert()
 *
 *  Called whenever an assert() test fails.  Prints a diagnostic
 *  message and abruptly exits.
 * ------------------------------------------------------------------------
 */

void
Itcl_Assert(testExpr, fileName, lineNumber)
    CONST char *testExpr;   /* string representing test expression */
    CONST char *fileName;   /* file name containing this call */
    int lineNumber;	    /* line number containing this call */
{
    Tcl_Panic("Itcl Assertion failed: \"%s\" (line %d of %s)",
	testExpr, lineNumber, fileName);
}



/*
 * ------------------------------------------------------------------------
 *  Itcl_InitStack()
 *
 *  Initializes a stack structure, allocating a certain amount of memory
 *  for the stack and setting the stack length to zero.
 * ------------------------------------------------------------------------
 */
void
Itcl_InitStack(stack)
    Itcl_Stack *stack;     /* stack to be initialized */
{
    stack->values = stack->space;
    stack->max = sizeof(stack->space)/sizeof(ClientData);
    stack->len = 0;
}

/*
 * ------------------------------------------------------------------------
 *  Itcl_DeleteStack()
 *
 *  Destroys a stack structure, freeing any memory that may have been
 *  allocated to represent it.
 * ------------------------------------------------------------------------
 */
void
Itcl_DeleteStack(stack)
    Itcl_Stack *stack;     /* stack to be deleted */
{
    /*
     *  If memory was explicitly allocated (instead of using the
     *  built-in buffer) then free it.
     */
    if (stack->values != stack->space) {
        ckfree((char*)stack->values);
    }
    stack->values = NULL;
    stack->len = stack->max = 0;
}

/*
 * ------------------------------------------------------------------------
 *  Itcl_PushStack()
 *
 *  Pushes a piece of client data onto the top of the given stack.
 *  If the stack is not large enough, it is automatically resized.
 * ------------------------------------------------------------------------
 */
void
Itcl_PushStack(cdata,stack)
    ClientData cdata;      /* data to be pushed onto stack */
    Itcl_Stack *stack;     /* stack */
{
    ClientData *newStack;

    if (stack->len+1 >= stack->max) {
        stack->max = 2*stack->max;
        newStack = (ClientData*)
            ckalloc((unsigned)(stack->max*sizeof(ClientData)));

        if (stack->values) {
            memcpy((char*)newStack, (char*)stack->values,
                (size_t)(stack->len*sizeof(ClientData)));

            if (stack->values != stack->space)
                ckfree((char*)stack->values);
        }
        stack->values = newStack;
    }
    stack->values[stack->len++] = cdata;
}

/*
 * ------------------------------------------------------------------------
 *  Itcl_PopStack()
 *
 *  Pops a bit of client data from the top of the given stack.
 * ------------------------------------------------------------------------
 */
ClientData
Itcl_PopStack(stack)
    Itcl_Stack *stack;  /* stack to be manipulated */
{
    if (stack->values && (stack->len > 0)) {
        stack->len--;
        return stack->values[stack->len];
    }
    return (ClientData)NULL;
}

/*
 * ------------------------------------------------------------------------
 *  Itcl_PeekStack()
 *
 *  Gets the current value from the top of the given stack.
 * ------------------------------------------------------------------------
 */
ClientData
Itcl_PeekStack(stack)
    Itcl_Stack *stack;  /* stack to be examined */
{
    if (stack->values && (stack->len > 0)) {
        return stack->values[stack->len-1];
    }
    return (ClientData)NULL;
}

/*
 * ------------------------------------------------------------------------
 *  Itcl_GetStackValue()
 *
 *  Gets a value at some index within the stack.  Index "0" is the
 *  first value pushed onto the stack.
 * ------------------------------------------------------------------------
 */
ClientData
Itcl_GetStackValue(stack,pos)
    Itcl_Stack *stack;  /* stack to be examined */
    int pos;            /* get value at this index */
{
    if (stack->values && (stack->len > 0)) {
        assert(pos < stack->len);
        return stack->values[pos];
    }
    return (ClientData)NULL;
}


/*
 * ------------------------------------------------------------------------
 *  Itcl_InitList()
 *
 *  Initializes a linked list structure, setting the list to the empty
 *  state.
 * ------------------------------------------------------------------------
 */
void
Itcl_InitList(listPtr)
    Itcl_List *listPtr;     /* list to be initialized */
{
    listPtr->validate = ITCL_VALID_LIST;
    listPtr->num      = 0;
    listPtr->head     = NULL;
    listPtr->tail     = NULL;
}

/*
 * ------------------------------------------------------------------------
 *  Itcl_DeleteList()
 *
 *  Destroys a linked list structure, deleting all of its elements and
 *  setting it to an empty state.  If the elements have memory associated
 *  with them, this memory must be freed before deleting the list or it
 *  will be lost.
 * ------------------------------------------------------------------------
 */
void
Itcl_DeleteList(listPtr)
    Itcl_List *listPtr;     /* list to be deleted */
{
    Itcl_ListElem *elemPtr;

    assert(listPtr->validate == ITCL_VALID_LIST);

    elemPtr = listPtr->head;
    while (elemPtr) {
        elemPtr = Itcl_DeleteListElem(elemPtr);
    }
    listPtr->validate = 0;
}

/*
 * ------------------------------------------------------------------------
 *  Itcl_CreateListElem()
 *
 *  Low-level routined used by procedures like Itcl_InsertList() and
 *  Itcl_AppendList() to create new list elements.  If elements are
 *  available, one is taken from the list element pool.  Otherwise,
 *  a new one is allocated.
 * ------------------------------------------------------------------------
 */
Itcl_ListElem*
Itcl_CreateListElem(listPtr)
    Itcl_List *listPtr;     /* list that will contain this new element */
{
    Itcl_ListElem *elemPtr;

    if (listPoolLen > 0) {
        elemPtr = listPool;
        listPool = elemPtr->next;
        --listPoolLen;
    }
    else {
        elemPtr = (Itcl_ListElem*)ckalloc((unsigned)sizeof(Itcl_ListElem));
    }
    elemPtr->owner = listPtr;
    elemPtr->value = NULL;
    elemPtr->next  = NULL;
    elemPtr->prev  = NULL;

    return elemPtr;
}

/*
 * ------------------------------------------------------------------------
 *  Itcl_DeleteListElem()
 *
 *  Destroys a single element in a linked list, returning it to a pool of
 *  elements that can be later reused.  Returns a pointer to the next
 *  element in the list.
 * ------------------------------------------------------------------------
 */
Itcl_ListElem*
Itcl_DeleteListElem(elemPtr)
    Itcl_ListElem *elemPtr;     /* list element to be deleted */
{
    Itcl_List *listPtr;
    Itcl_ListElem *nextPtr;

    nextPtr = elemPtr->next;

    if (elemPtr->prev) {
        elemPtr->prev->next = elemPtr->next;
    }
    if (elemPtr->next) {
        elemPtr->next->prev = elemPtr->prev;
    }

    listPtr = elemPtr->owner;
    if (elemPtr == listPtr->head)
        listPtr->head = elemPtr->next;
    if (elemPtr == listPtr->tail)
        listPtr->tail = elemPtr->prev;
    --listPtr->num;

    if (listPoolLen < ITCL_LIST_POOL_SIZE) {
        elemPtr->next = listPool;
        listPool = elemPtr;
        ++listPoolLen;
    }
    else {
        ckfree((char*)elemPtr);
    }
    return nextPtr;
}

/*
 * ------------------------------------------------------------------------
 *  Itcl_InsertList()
 *
 *  Creates a new list element containing the given value and returns
 *  a pointer to it.  The element is inserted at the beginning of the
 *  specified list.
 * ------------------------------------------------------------------------
 */
Itcl_ListElem*
Itcl_InsertList(listPtr,val)
    Itcl_List *listPtr;     /* list being modified */
    ClientData val;         /* value associated with new element */
{
    Itcl_ListElem *elemPtr;
    assert(listPtr->validate == ITCL_VALID_LIST);

    elemPtr = Itcl_CreateListElem(listPtr);

    elemPtr->value = val;
    elemPtr->next  = listPtr->head;
    elemPtr->prev  = NULL;
    if (listPtr->head) {
        listPtr->head->prev = elemPtr;
    }
    listPtr->head  = elemPtr;
    if (listPtr->tail == NULL) {
        listPtr->tail = elemPtr;
    }
    ++listPtr->num;

    return elemPtr;
}

/*
 * ------------------------------------------------------------------------
 *  Itcl_InsertListElem()
 *
 *  Creates a new list element containing the given value and returns
 *  a pointer to it.  The element is inserted in the list just before
 *  the specified element.
 * ------------------------------------------------------------------------
 */
Itcl_ListElem*
Itcl_InsertListElem(pos,val)
    Itcl_ListElem *pos;     /* insert just before this element */
    ClientData val;         /* value associated with new element */
{
    Itcl_List *listPtr;
    Itcl_ListElem *elemPtr;

    listPtr = pos->owner;
    assert(listPtr->validate == ITCL_VALID_LIST);
    assert(pos != NULL);

    elemPtr = Itcl_CreateListElem(listPtr);
    elemPtr->value = val;

    elemPtr->prev = pos->prev;
    if (elemPtr->prev) {
        elemPtr->prev->next = elemPtr;
    }
    elemPtr->next = pos;
    pos->prev     = elemPtr;

    if (listPtr->head == pos) {
        listPtr->head = elemPtr;
    }
    if (listPtr->tail == NULL) {
        listPtr->tail = elemPtr;
    }
    ++listPtr->num;

    return elemPtr;
}

/*
 * ------------------------------------------------------------------------
 *  Itcl_AppendList()
 *
 *  Creates a new list element containing the given value and returns
 *  a pointer to it.  The element is appended at the end of the
 *  specified list.
 * ------------------------------------------------------------------------
 */
Itcl_ListElem*
Itcl_AppendList(listPtr,val)
    Itcl_List *listPtr;     /* list being modified */
    ClientData val;         /* value associated with new element */
{
    Itcl_ListElem *elemPtr;
    assert(listPtr->validate == ITCL_VALID_LIST);

    elemPtr = Itcl_CreateListElem(listPtr);

    elemPtr->value = val;
    elemPtr->prev  = listPtr->tail;
    elemPtr->next  = NULL;
    if (listPtr->tail) {
        listPtr->tail->next = elemPtr;
    }
    listPtr->tail  = elemPtr;
    if (listPtr->head == NULL) {
        listPtr->head = elemPtr;
    }
    ++listPtr->num;

    return elemPtr;
}

/*
 * ------------------------------------------------------------------------
 *  Itcl_AppendListElem()
 *
 *  Creates a new list element containing the given value and returns
 *  a pointer to it.  The element is inserted in the list just after
 *  the specified element.
 * ------------------------------------------------------------------------
 */
Itcl_ListElem*
Itcl_AppendListElem(pos,val)
    Itcl_ListElem *pos;     /* insert just after this element */
    ClientData val;         /* value associated with new element */
{
    Itcl_List *listPtr;
    Itcl_ListElem *elemPtr;

    listPtr = pos->owner;
    assert(listPtr->validate == ITCL_VALID_LIST);
    assert(pos != NULL);

    elemPtr = Itcl_CreateListElem(listPtr);
    elemPtr->value = val;

    elemPtr->next = pos->next;
    if (elemPtr->next) {
        elemPtr->next->prev = elemPtr;
    }
    elemPtr->prev = pos;
    pos->next     = elemPtr;

    if (listPtr->tail == pos) {
        listPtr->tail = elemPtr;
    }
    if (listPtr->head == NULL) {
        listPtr->head = elemPtr;
    }
    ++listPtr->num;

    return elemPtr;
}

/*
 * ------------------------------------------------------------------------
 *  Itcl_SetListValue()
 *
 *  Modifies the value associated with a list element.
 * ------------------------------------------------------------------------
 */
void
Itcl_SetListValue(elemPtr,val)
    Itcl_ListElem *elemPtr; /* list element being modified */
    ClientData val;         /* new value associated with element */
{
    Itcl_List *listPtr = elemPtr->owner;
    assert(listPtr->validate == ITCL_VALID_LIST);
    assert(elemPtr != NULL);

    elemPtr->value = val;
}


/*
 * ========================================================================
 *  REFERENCE-COUNTED DATA
 *
 *  The following procedures manage generic reference-counted data.
 *  They are similar in spirit to the Tcl_Preserve/Tcl_Release
 *  procedures defined in the Tcl/Tk core.  But these procedures use
 *  a hash table instead of a linked list to maintain the references,
 *  so they scale better.  Also, the Tcl procedures have a bad behavior
 *  during the "exit" command.  Their exit handler shuts them down
 *  when other data is still being reference-counted and cleaned up.
 *
 * ------------------------------------------------------------------------
 *  Itcl_EventuallyFree()
 *
 *  Registers a piece of data so that it will be freed when no longer
 *  in use.  The data is registered with an initial usage count of "0".
 *  Future calls to Itcl_PreserveData() increase this usage count, and
 *  calls to Itcl_ReleaseData() decrease the count until it reaches
 *  zero and the data is freed.
 * ------------------------------------------------------------------------
 */
void
Itcl_EventuallyFree(cdata, fproc)
    ClientData cdata;          /* data to be freed when not in use */
    Tcl_FreeProc *fproc;       /* procedure called to free data */
{
    int newEntry;
    Tcl_HashEntry *entry;
    ItclPreservedData *chunk;

    /*
     *  If the clientData value is NULL, do nothing.
     */
    if (cdata == NULL) {
        return;
    }

    /*
     *  If a list has not yet been created to manage bits of
     *  preserved data, then create it.
     */
    Tcl_MutexLock(&ItclPreservedListLock);
    if (!ItclPreservedList) {
        ItclPreservedList = (Tcl_HashTable*)ckalloc(
            (unsigned)sizeof(Tcl_HashTable)
        );
        Tcl_InitHashTable(ItclPreservedList, TCL_ONE_WORD_KEYS);
    }

    /*
     *  Find or create the data in the global list.
     */
    entry = Tcl_CreateHashEntry(ItclPreservedList,(char*)cdata, &newEntry);
    if (newEntry) {
        chunk = (ItclPreservedData*)ckalloc(
            (unsigned)sizeof(ItclPreservedData)
        );
        chunk->data  = cdata;
        chunk->usage = 0;
        chunk->fproc = fproc;
        Tcl_SetHashValue(entry, (ClientData)chunk);
    }
    else {
        chunk = (ItclPreservedData*)Tcl_GetHashValue(entry);
        chunk->fproc = fproc;
    }

    /*
     *  If the usage count is zero, then delete the data now.
     */
    if (chunk->usage == 0) {
	chunk->usage = -1;  /* cannot preserve/release anymore */

	Tcl_MutexUnlock(&ItclPreservedListLock);
	(*chunk->fproc)((char*)chunk->data);
	Tcl_MutexLock(&ItclPreservedListLock);
	Tcl_DeleteHashEntry(entry);
	ckfree((char*)chunk);
    }
    Tcl_MutexUnlock(&ItclPreservedListLock);
}

/*
 * ------------------------------------------------------------------------
 *  Itcl_PreserveData()
 *
 *  Increases the usage count for a piece of data that will be freed
 *  later when no longer needed.  Each call to Itcl_PreserveData()
 *  puts one claim on a piece of data, and subsequent calls to
 *  Itcl_ReleaseData() remove those claims.  When Itcl_EventuallyFree()
 *  is called, and when the usage count reaches zero, the data is
 *  freed.
 * ------------------------------------------------------------------------
 */
void
Itcl_PreserveData(cdata)
    ClientData cdata;      /* data to be preserved */
{
    Tcl_HashEntry *entry;
    ItclPreservedData *chunk;
    int newEntry;

    /*
     *  If the clientData value is NULL, do nothing.
     */
    if (cdata == NULL) {
        return;
    }

    /*
     *  If a list has not yet been created to manage bits of
     *  preserved data, then create it.
     */
    Tcl_MutexLock(&ItclPreservedListLock);
    if (!ItclPreservedList) {
        ItclPreservedList = (Tcl_HashTable*)ckalloc(
            (unsigned)sizeof(Tcl_HashTable)
        );
        Tcl_InitHashTable(ItclPreservedList,TCL_ONE_WORD_KEYS);
    }

    /*
     *  Find the data in the global list and bump its usage count.
     */
    entry = Tcl_CreateHashEntry(ItclPreservedList,(char*)cdata, &newEntry);
    if (newEntry) {
        chunk = (ItclPreservedData*)ckalloc(
            (unsigned)sizeof(ItclPreservedData)
        );
        chunk->data  = cdata;
        chunk->usage = 0;
        chunk->fproc = NULL;
        Tcl_SetHashValue(entry, (ClientData)chunk);
    }
    else {
        chunk = (ItclPreservedData*)Tcl_GetHashValue(entry);
    }

    /*
     *  Only increment the usage if it is non-negative.
     *  Negative numbers mean that the data is in the process
     *  of being destroyed by Itcl_ReleaseData(), and should
     *  not be further preserved.
     */
    if (chunk->usage >= 0) {
        chunk->usage++;
    }
    Tcl_MutexUnlock(&ItclPreservedListLock);
}

/*
 * ------------------------------------------------------------------------
 *  Itcl_ReleaseData()
 *
 *  Decreases the usage count for a piece of data that was registered
 *  previously via Itcl_PreserveData().  After Itcl_EventuallyFree()
 *  is called and the usage count reaches zero, the data is
 *  automatically freed.
 * ------------------------------------------------------------------------
 */
void
Itcl_ReleaseData(cdata)
    ClientData cdata;      /* data to be released */
{
    Tcl_HashEntry *entry;
    ItclPreservedData *chunk;

    /*
     *  If the clientData value is NULL, do nothing.
     */
    if (cdata == NULL) {
        return;
    }

    /*
     *  Otherwise, find the data in the global list and
     *  decrement its usage count.
     */
    entry = NULL;
    Tcl_MutexLock(&ItclPreservedListLock);
    if (ItclPreservedList) {
        entry = Tcl_FindHashEntry(ItclPreservedList,(char*)cdata);
    }
    if (!entry) {
	Tcl_MutexUnlock(&ItclPreservedListLock);
        Tcl_Panic("Itcl_ReleaseData can't find reference for 0x%x", cdata);
    }

    /*
     *  Only decrement the usage if it is non-negative.
     *  When the usage reaches zero, set it to a negative number
     *  to indicate that data is being destroyed, and then
     *  invoke the client delete proc.  When the data is deleted,
     *  remove the entry from the preservation list.
     */
    chunk = (ItclPreservedData*)Tcl_GetHashValue(entry);
    if (chunk->usage > 0 && --chunk->usage == 0) {

	if (chunk->fproc) {
	    chunk->usage = -1;  /* cannot preserve/release anymore */
	    Tcl_MutexUnlock(&ItclPreservedListLock);
	    (*chunk->fproc)((char*)chunk->data);
	    Tcl_MutexLock(&ItclPreservedListLock);
        }

        Tcl_DeleteHashEntry(entry);
        ckfree((char*)chunk);
    }
    Tcl_MutexUnlock(&ItclPreservedListLock);
}


/*
 * ------------------------------------------------------------------------
 *  Itcl_SaveInterpState()
 *
 *  Takes a snapshot of the current result state of the interpreter.
 *  The snapshot can be restored at any point by Itcl_RestoreInterpState.
 *  So if you are in the middle of building a return result, you can
 *  snapshot the interpreter, execute a command that might generate an
 *  error, restore the snapshot, and continue building the result string.
 *
 *  Once a snapshot is saved, it must be restored by calling
 *  Itcl_RestoreInterpState, or discarded by calling
 *  Itcl_DiscardInterpState.  Otherwise, memory will be leaked.
 *
 *  Returns a token representing the state of the interpreter.
 * ------------------------------------------------------------------------
 */
Itcl_InterpState
Itcl_SaveInterpState(interp, status)
    Tcl_Interp* interp;     /* interpreter being modified */
    int status;             /* integer status code for current operation */
{
    Interp *iPtr = (Interp*)interp;

    InterpState *info;
    CONST char *val;

    /*
     * ERR_IN_PROGRESS was replaced by new APIs in 8.5a2.  Call them if they
     * are available, or somehow magic them in from the stubs table.
     * Tcl_ChannelThreadActionProc is a stubs slot higher than the APIs we
     * need, so its existence indicates slot-y goodness.
     */
#ifndef ERR_IN_PROGRESS
    return (Itcl_InterpState) Tcl_SaveInterpState(interp, status);
#elif defined(USE_TCL_STUBS) && defined(Tcl_ChannelThreadActionProc)
    if (itclCompatFlags & ITCL_COMPAT_USE_ISTATE_API) {
	Itcl_InterpState (*tcl_SaveInterpState)(Tcl_Interp *, int) =
	    (Itcl_InterpState (*)(Tcl_Interp *, int)) tclStubsPtr->reserved535;
	return (*tcl_SaveInterpState)(interp, status);
    }
#endif

    info = (InterpState*)ckalloc(sizeof(InterpState));
    info->validate = TCL_STATE_VALID;
    info->status = status;
    info->errorInfo = NULL;
    info->errorCode = NULL;

    /*
     *  Get the result object from the interpreter.  This synchronizes
     *  the old-style result, so we don't have to worry about it.
     *  Keeping the object result is enough.
     */
    info->objResult = Tcl_GetObjResult(interp);
    Tcl_IncrRefCount(info->objResult);

    /*
     *  If an error is in progress, preserve its state.
     */
#ifdef ERR_IN_PROGRESS   /* this disappeared in 8.5a2 */
    if ((iPtr->flags & ERR_IN_PROGRESS) != 0) {
#else
    if (iPtr->errorInfo != NULL) {
#endif
        val = Tcl_GetVar(interp, "errorInfo", TCL_GLOBAL_ONLY);
        if (val) {
            info->errorInfo = ckalloc((unsigned)(strlen(val)+1));
            strcpy(info->errorInfo, val);
        }

        val = Tcl_GetVar(interp, "errorCode", TCL_GLOBAL_ONLY);
        if (val) {
            info->errorCode = ckalloc((unsigned)(strlen(val)+1));
            strcpy(info->errorCode, val);
        }
    }

    /*
     *  Now, reset the interpreter to a clean state.
     */
    Tcl_ResetResult(interp);

    return (Itcl_InterpState)info;
}


/*
 * ------------------------------------------------------------------------
 *  Itcl_RestoreInterpState()
 *
 *  Restores the state of the interpreter to a snapshot taken by
 *  Itcl_SaveInterpState.  This affects variables such as "errorInfo"
 *  and "errorCode".  After this call, the token for the interpreter
 *  state is no longer valid.
 *
 *  Returns the status code that was pending at the time the state was
 *  captured.
 * ------------------------------------------------------------------------
 */
int
Itcl_RestoreInterpState(interp, state)
    Tcl_Interp* interp;       /* interpreter being modified */
    Itcl_InterpState state;   /* token representing interpreter state */
{
    InterpState *info = (InterpState*)state;
    int status;

    /*
     * ERR_IN_PROGRESS was replaced by new APIs in 8.5a2.  Call them if they
     * are available, or somehow magic them in from the stubs table.
     * Tcl_ChannelThreadActionProc is a stubs slot higher than the APIs we
     * need, so its existence indicates slot-y goodness.
     */
#ifndef ERR_IN_PROGRESS
    return Tcl_RestoreInterpState(interp, (Tcl_InterpState)state);
#elif defined(USE_TCL_STUBS) && defined(Tcl_ChannelThreadActionProc)
    if (itclCompatFlags & ITCL_COMPAT_USE_ISTATE_API) {
	int (*tcl_RestoreInterpState)() = (int (*)()) tclStubsPtr->reserved536;
 	return (*tcl_RestoreInterpState)(interp, state);
    }
#endif

    if (info->validate != TCL_STATE_VALID) {
        Tcl_Panic("bad token in Itcl_RestoreInterpState");
    }
    Tcl_ResetResult(interp);

    /*
     *  If an error is in progress, restore its state.
     *  Set the error code the hard way--set the variable directly
     *  and fix the interpreter flags.  Otherwise, if the error code
     *  string is really a list, it will get wrapped in extra {}'s.
     */
    if (info->errorInfo) {
        Tcl_AddErrorInfo(interp, info->errorInfo);
        ckfree(info->errorInfo);
    }

    if (info->errorCode) {
        Tcl_SetObjErrorCode(interp, Tcl_NewStringObj(info->errorCode, -1));
        ckfree(info->errorCode);
    }

    /*
     *  Assign the object result back to the interpreter, then
     *  release our hold on it.
     */
    Tcl_SetObjResult(interp, info->objResult);
    Tcl_DecrRefCount(info->objResult);

    status = info->status;
    info->validate = 0;
    ckfree((char*)info);

    return status;
}


/*
 * ------------------------------------------------------------------------
 *  Itcl_DiscardInterpState()
 *
 *  Frees the memory associated with an interpreter snapshot taken by
 *  Itcl_SaveInterpState.  If the snapshot is not restored, this
 *  procedure must be called to discard it, or the memory will be lost.
 *  After this call, the token for the interpreter state is no longer
 *  valid.
 * ------------------------------------------------------------------------
 */
void
Itcl_DiscardInterpState(state)
    Itcl_InterpState state;  /* token representing interpreter state */
{
    InterpState *info = (InterpState*)state;

    /*
     * ERR_IN_PROGRESS was replaced by new APIs in 8.5a2.  Call them if they
     * are available, or somehow magic them in from the stubs table.
     * Tcl_ChannelThreadActionProc is a stubs slot higher than the APIs we
     * need, so its existence indicates slot-y goodness.
     */
#ifndef ERR_IN_PROGRESS
    Tcl_DiscardInterpState((Tcl_InterpState)state);
    return;
#elif defined(USE_TCL_STUBS) && defined(Tcl_ChannelThreadActionProc)
    if (itclCompatFlags & ITCL_COMPAT_USE_ISTATE_API) {
	void (* tcl_DiscardInterpState)() = (void (*)())
	    tclStubsPtr->reserved537;
	(*tcl_DiscardInterpState)(state);
	return;
    }
#endif

    if (info->validate != TCL_STATE_VALID) {
        Tcl_Panic("bad token in Itcl_DiscardInterpState");
    }

    if (info->errorInfo) {
        ckfree(info->errorInfo);
    }
    if (info->errorCode) {
        ckfree(info->errorCode);
    }
    Tcl_DecrRefCount(info->objResult);

    info->validate = 0;
    ckfree((char*)info);
}


/*
 * ------------------------------------------------------------------------
 *  Itcl_Protection()
 *
 *  Used to query/set the protection level used when commands/variables
 *  are defined within a class.  The default protection level (when
 *  no public/protected/private command is active) is ITCL_DEFAULT_PROTECT.
 *  In the default case, new commands are treated as public, while new
 *  variables are treated as protected.
 *
 *  If the specified level is 0, then this procedure returns the
 *  current value without changing it.  Otherwise, it sets the current
 *  value to the specified protection level, and returns the previous
 *  value.
 * ------------------------------------------------------------------------
 */
int
Itcl_Protection(interp, newLevel)
    Tcl_Interp *interp;  /* interpreter being queried */
    int newLevel;        /* new protection level or 0 */
{
    int oldVal;
    ItclObjectInfo *info;

    /*
     *  If a new level was specified, then set the protection level.
     *  In any case, return the protection level as it stands right now.
     */
    info = (ItclObjectInfo*) Tcl_GetAssocData(interp, ITCL_INTERP_DATA,
        (Tcl_InterpDeleteProc**)NULL);

    assert(info != NULL);
    oldVal = info->protection;

    if (newLevel != 0) {
        assert(newLevel == ITCL_PUBLIC ||
            newLevel == ITCL_PROTECTED ||
            newLevel == ITCL_PRIVATE ||
            newLevel == ITCL_DEFAULT_PROTECT);
        info->protection = newLevel;
    }
    return oldVal;
}


/*
 * ------------------------------------------------------------------------
 *  Itcl_ProtectionStr()
 *
 *  Converts an integer protection code (ITCL_PUBLIC, ITCL_PROTECTED,
 *  or ITCL_PRIVATE) into a human-readable character string.  Returns
 *  a pointer to this string.
 * ------------------------------------------------------------------------
 */
char*
Itcl_ProtectionStr(pLevel)
    int pLevel;     /* protection level */
{
    switch (pLevel) {
    case ITCL_PUBLIC:
        return "public";
    case ITCL_PROTECTED:
        return "protected";
    case ITCL_PRIVATE:
        return "private";
    }
    return "<bad-protection-code>";
}


/*
 * ------------------------------------------------------------------------
 *  Itcl_CanAccess()
 *
 *  Checks to see if a class member can be accessed from a particular
 *  namespace context.  Public things can always be accessed.  Protected
 *  things can be accessed if the "from" namespace appears in the
 *  inheritance hierarchy of the class namespace.  Private things
 *  can be accessed only if the "from" namespace is the same as the
 *  class that contains them.
 *
 *  Returns 1/0 indicating true/false.
 * ------------------------------------------------------------------------
 */
int
Itcl_CanAccess(memberPtr, fromNsPtr)
    ItclMember* memberPtr;     /* class member being tested */
    Tcl_Namespace* fromNsPtr;  /* namespace requesting access */
{
    ItclClass* fromCdPtr;
    Tcl_HashEntry *entry;

    /*
     *  If the protection level is "public" or "private", then the
     *  answer is known immediately.
     */
    if (memberPtr->protection == ITCL_PUBLIC) {
        return 1;
    }
    else if (memberPtr->protection == ITCL_PRIVATE) {
        return (memberPtr->classDefn->namesp == fromNsPtr);
    }

    /*
     *  If the protection level is "protected", then check the
     *  heritage of the namespace requesting access.  If cdefnPtr
     *  is in the heritage, then access is allowed.
     */
    assert (memberPtr->protection == ITCL_PROTECTED);

    if (Itcl_IsClassNamespace(fromNsPtr)) {
        fromCdPtr = (ItclClass*)fromNsPtr->clientData;

        entry = Tcl_FindHashEntry(&fromCdPtr->heritage,
            (char*)memberPtr->classDefn);

        if (entry) {
            return 1;
        }
    }
    return 0;
}


/*
 * ------------------------------------------------------------------------
 *  Itcl_CanAccessFunc()
 *
 *  Checks to see if a member function with the specified protection
 *  level can be accessed from a particular namespace context.  This
 *  follows the same rules enforced by Itcl_CanAccess, but adds one
 *  special case:  If the function is a protected method, and if the
 *  current context is a base class that has the same method, then
 *  access is allowed.
 *
 *  Returns 1/0 indicating true/false.
 * ------------------------------------------------------------------------
 */
int
Itcl_CanAccessFunc(mfunc, fromNsPtr)
    ItclMemberFunc* mfunc;     /* member function being tested */
    Tcl_Namespace* fromNsPtr;  /* namespace requesting access */
{
    ItclClass *cdPtr, *fromCdPtr;
    ItclMemberFunc *ovlfunc;
    Tcl_HashEntry *entry;

    /*
     *  Apply the usual rules first.
     */
    if (Itcl_CanAccess(mfunc->member, fromNsPtr)) {
        return 1;
    }

    /*
     *  As a last resort, see if the namespace is really a base
     *  class of the class containing the method.  Look for a
     *  method with the same name in the base class.  If there
     *  is one, then this method overrides it, and the base class
     *  has access.
     */
    if ((mfunc->member->flags & ITCL_COMMON) == 0 &&
        Itcl_IsClassNamespace(fromNsPtr)) {

        cdPtr = mfunc->member->classDefn;
        fromCdPtr = (ItclClass*)fromNsPtr->clientData;

        if (Tcl_FindHashEntry(&cdPtr->heritage, (char*)fromCdPtr)) {
            entry = Tcl_FindHashEntry(&fromCdPtr->resolveCmds,
                mfunc->member->name);

            if (entry) {
                ovlfunc = (ItclMemberFunc*)Tcl_GetHashValue(entry);
                if ((ovlfunc->member->flags & ITCL_COMMON) == 0 &&
                     ovlfunc->member->protection < ITCL_PRIVATE) {
                    return 1;
                }
            }
        }
    }
    return 0;
}


/*
 * ------------------------------------------------------------------------
 *  Itcl_GetTrueNamespace()
 *
 *  Returns the current namespace context.  This procedure is similar
 *  to Tcl_GetCurrentNamespace, but it supports the notion of
 *  "transparent" call frames installed by Itcl_HandleInstance.
 *
 *  Returns a pointer to the current namespace calling context.
 * ------------------------------------------------------------------------
 */
Tcl_Namespace*
Itcl_GetTrueNamespace(interp, info)
    Tcl_Interp *interp;        /* interpreter being queried */
    ItclObjectInfo *info;      /* object info associated with interp */
{
    int i, transparent;
    Itcl_CallFrame *framePtr, *transFramePtr;
    Tcl_Namespace *contextNs;

    /*
     *  See if the current call frame is on the list of transparent
     *  call frames.
     */
    transparent = 0;

    framePtr = _Tcl_GetCallFrame(interp, 0);
    for (i = Itcl_GetStackSize(&info->transparentFrames)-1; i >= 0; i--) {
        transFramePtr = (Itcl_CallFrame*)
            Itcl_GetStackValue(&info->transparentFrames, i);

        if (framePtr == transFramePtr) {
            transparent = 1;
            break;
        }
    }

    /*
     *  If this is a transparent call frame, return the namespace
     *  context one level up.
     */
    if (transparent) {
        framePtr = _Tcl_GetCallFrame(interp, 1);
        if (framePtr) {
            contextNs = framePtr->nsPtr;
        } else {
            contextNs = Tcl_GetGlobalNamespace(interp);
        }
    }
    else {
        contextNs = Tcl_GetCurrentNamespace(interp);
    }
    return contextNs;
}


/*
 * ------------------------------------------------------------------------
 *  Itcl_ParseNamespPath()
 *
 *  Parses a reference to a namespace element of the form:
 *
 *      namesp::namesp::namesp::element
 *
 *  Returns pointers to the head part ("namesp::namesp::namesp")
 *  and the tail part ("element").  If the head part is missing,
 *  a NULL pointer is returned and the rest of the string is taken
 *  as the tail.
 *
 *  Both head and tail point to locations within the given dynamic
 *  string buffer.  This buffer must be uninitialized when passed
 *  into this procedure, and it must be freed later on, when the
 *  strings are no longer needed.
 * ------------------------------------------------------------------------
 */
void
Itcl_ParseNamespPath(name, buffer, head, tail)
    CONST char *name;    /* path name to class member */
    Tcl_DString *buffer; /* dynamic string buffer (uninitialized) */
    char **head;         /* returns "namesp::namesp::namesp" part */
    char **tail;         /* returns "element" part */
{
    register char *sep, *newname;

    Tcl_DStringInit(buffer);

    /*
     *  Copy the name into the buffer and parse it.  Look
     *  backward from the end of the string to the first '::'
     *  scope qualifier.
     */
    Tcl_DStringAppend(buffer, name, -1);
    newname = Tcl_DStringValue(buffer);

    for (sep=newname; *sep != '\0'; sep++)
        ;

    while (--sep > newname) {
        if (*sep == ':' && *(sep-1) == ':') {
            break;
        }
    }

    /*
     *  Found head/tail parts.  If there are extra :'s, keep backing
     *  up until the head is found.  This supports the Tcl namespace
     *  behavior, which allows names like "foo:::bar".
     */
    if (sep > newname) {
        *tail = sep+1;
        while (sep > newname && *(sep-1) == ':') {
            sep--;
        }
        *sep = '\0';
        *head = newname;
    }

    /*
     *  No :: separators--the whole name is treated as a tail.
     */
    else {
        *tail = newname;
        *head = NULL;
    }
}


/*
 * ------------------------------------------------------------------------
 *  Itcl_DecodeScopedCommand()
 *
 *  Decodes a scoped command of the form:
 *
 *      namespace inscope <namesp> <command>
 *
 *  If the given string is not a scoped value, this procedure does
 *  nothing and returns TCL_OK.  If the string is a scoped value,
 *  then it is decoded, and the namespace, and the simple command
 *  string are returned as arguments; the simple command should
 *  be freed when no longer in use.  If anything goes wrong, this
 *  procedure returns TCL_ERROR, along with an error message in
 *  the interpreter.
 * ------------------------------------------------------------------------
 */
int
Itcl_DecodeScopedCommand(interp, name, rNsPtr, rCmdPtr)
    Tcl_Interp *interp;		/* current interpreter */
    CONST char *name;		/* string to be decoded */
    Tcl_Namespace **rNsPtr;	/* returns: namespace for scoped value */
    char **rCmdPtr;		/* returns: simple command word */
{
    Tcl_Namespace *nsPtr = NULL;
    char *cmdName;
    int len = strlen(name);
    CONST char *pos;
    int listc, result;
    char **listv;

    cmdName = ckalloc((unsigned)strlen(name)+1);
    strcpy(cmdName, name);

    if ((*name == 'n') && (len > 17) && (strncmp(name, "namespace", 9) == 0)) {
	for (pos = (name + 9);  (*pos == ' ');  pos++) {
	    /* empty body: skip over spaces */
	}
	if ((*pos == 'i') && ((pos + 7) <= (name + len))
	        && (strncmp(pos, "inscope", 7) == 0)) {

            result = Tcl_SplitList(interp, (CONST84 char *)name, &listc,
		    &listv);
            if (result == TCL_OK) {
                if (listc != 4) {
                    Tcl_AppendResult(interp,
                        "malformed command \"", name, "\": should be \"",
                        "namespace inscope namesp command\"",
                        (char*)NULL);
                    result = TCL_ERROR;
                } else {
                    nsPtr = Tcl_FindNamespace(interp, listv[2],
                        (Tcl_Namespace*)NULL, TCL_LEAVE_ERR_MSG);

                    if (!nsPtr) {
                        result = TCL_ERROR;
                    } else {
			ckfree(cmdName);
                        cmdName = ckalloc((unsigned)(strlen(listv[3])+1));
                        strcpy(cmdName, listv[3]);
                    }
                }
            }
            ckfree((char*)listv);

            if (result != TCL_OK) {
                char msg[512];
                sprintf(msg, "\n    (while decoding scoped command \"%.400s\")", name);
                Tcl_AddObjErrorInfo(interp, msg, -1);
                return TCL_ERROR;
            }
	}
    }

    *rNsPtr = nsPtr;
    *rCmdPtr = cmdName;
    return TCL_OK;
}


/*
 * ------------------------------------------------------------------------
 *  Itcl_EvalArgs()
 *
 *  This procedure invokes a list of (objc,objv) arguments as a
 *  single command.  It is similar to Tcl_EvalObj, but it doesn't
 *  do any parsing or compilation.  It simply treats the first
 *  argument as a command and invokes that command in the current
 *  context.
 *
 *  Returns TCL_OK if successful.  Otherwise, this procedure returns
 *  TCL_ERROR along with an error message in the interpreter.
 * ------------------------------------------------------------------------
 */
int
Itcl_EvalArgs(interp, objc, objv)
    Tcl_Interp *interp;      /* current interpreter */
    int objc;                /* number of arguments */
    Tcl_Obj *CONST objv[];   /* argument objects */
{
    int result;
    Tcl_Command cmd;
    Command *cmdPtr;
    int cmdlinec;
    Tcl_Obj **cmdlinev;
    Tcl_Obj *cmdlinePtr = NULL;

    /*
     * Resolve the command by converting it to a CmdName object.
     * This caches a pointer to the Command structure for the
     * command, so if we need it again, it's ready to use.
     */
    cmd = Tcl_GetCommandFromObj(interp, objv[0]);
    cmdPtr = (Command*)cmd;

    cmdlinec = objc;
    cmdlinev = (Tcl_Obj	**) objv;

    /*
     * If the command is still not found, handle it with the
     * "unknown" proc.
     */
    if (cmdPtr == NULL) {
        cmd = Tcl_FindCommand(interp, "unknown",
            (Tcl_Namespace *) NULL, /*flags*/ TCL_GLOBAL_ONLY);

        if (cmd == NULL) {
            Tcl_ResetResult(interp);
            Tcl_AppendResult(interp,
                "invalid command name \"",
                Tcl_GetStringFromObj(objv[0], NULL), "\"", NULL);
            return TCL_ERROR;
        }
        cmdPtr = (Command*)cmd;

        cmdlinePtr = Itcl_CreateArgs(interp, "unknown", objc, objv);
        Tcl_ListObjGetElements(NULL, cmdlinePtr, &cmdlinec, &cmdlinev);
    }

    /*
     *  Finally, invoke the command's Tcl_ObjCmdProc.  Be careful
     *  to pass in the proper client data.
     */
    Tcl_ResetResult(interp);
    result = (*cmdPtr->objProc)(cmdPtr->objClientData, interp,
        cmdlinec, cmdlinev);

    if (cmdlinePtr) {
        Tcl_DecrRefCount(cmdlinePtr);
    }
    return result;
}


/*
 * ------------------------------------------------------------------------
 *  Itcl_CreateArgs()
 *
 *  This procedure takes a string and a list of (objc,objv) arguments,
 *  and glues them together in a single list.  This is useful when
 *  a command word needs to be prepended or substituted into a command
 *  line before it is executed.  The arguments are returned in a single
 *  list object, and they can be retrieved by calling
 *  Tcl_ListObjGetElements.  When the arguments are no longer needed,
 *  they should be discarded by decrementing the reference count for
 *  the list object.
 *
 *  Returns a pointer to the list object containing the arguments.
 * ------------------------------------------------------------------------
 */
Tcl_Obj*
Itcl_CreateArgs(interp, string, objc, objv)
    Tcl_Interp *interp;      /* current interpreter */
    CONST char *string;      /* first command word */
    int objc;                /* number of arguments */
    Tcl_Obj *CONST objv[];   /* argument objects */
{
    int i;
    Tcl_Obj *listPtr;

    listPtr = Tcl_NewListObj(0, (Tcl_Obj**)NULL);
    Tcl_ListObjAppendElement((Tcl_Interp*)NULL, listPtr,
        Tcl_NewStringObj((CONST84 char *)string, -1));

    for (i=0; i < objc; i++) {
        Tcl_ListObjAppendElement((Tcl_Interp*)NULL, listPtr, objv[i]);
    }

    Tcl_IncrRefCount(listPtr);
    return listPtr;
}
