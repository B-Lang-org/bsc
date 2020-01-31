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
 *  ADDING [incr Tcl] TO A Tcl-BASED APPLICATION:
 *
 *    To add [incr Tcl] facilities to a Tcl application, modify the
 *    Tcl_AppInit() routine as follows:
 *
 *    1) Include this header file near the top of the file containing
 *       Tcl_AppInit():
 *
 *         #include "itcl.h"
 *
 *    2) Within the body of Tcl_AppInit(), add the following lines:
 *
 *         if (Itcl_Init(interp) == TCL_ERROR) {
 *             return TCL_ERROR;
 *         }
 * 
 *    3) Link your application with libitcl.a
 *
 *    NOTE:  An example file "tclAppInit.c" containing the changes shown
 *           above is included in this distribution.
 *  
 * ========================================================================
 *  AUTHOR:  Michael J. McLennan
 *           Bell Labs Innovations for Lucent Technologies
 *           mmclennan@lucent.com
 *           http://www.tcltk.com/itcl
 *
 *     RCS:  $Id: itcl.h,v 1.31 2007/05/24 22:15:41 hobbs Exp $
 * ========================================================================
 *           Copyright (c) 1993-1998  Lucent Technologies, Inc.
 * ------------------------------------------------------------------------
 * See the file "license.terms" for information on usage and redistribution
 * of this file, and for a DISCLAIMER OF ALL WARRANTIES.
 */
#ifndef ITCL_H
#define ITCL_H

#include "tcl.h"

#ifndef TCL_ALPHA_RELEASE
#   define TCL_ALPHA_RELEASE	0
#endif
#ifndef TCL_BETA_RELEASE
#   define TCL_BETA_RELEASE	1
#endif
#ifndef TCL_FINAL_RELEASE
#   define TCL_FINAL_RELEASE	2
#endif


#define ITCL_MAJOR_VERSION	3
#define ITCL_MINOR_VERSION	4
#define ITCL_RELEASE_LEVEL	TCL_FINAL_RELEASE
#define ITCL_RELEASE_SERIAL	0

#define ITCL_VERSION		"3.4"
#define ITCL_PATCH_LEVEL	"3.4.0"

/* 
 * A special definition used to allow this header file to be included 
 * in resource files so that they can get obtain version information from
 * this file.  Resource compilers don't like all the C stuff, like typedefs
 * and procedure declarations, that occur below.
 */

#ifndef RC_INVOKED

#undef TCL_STORAGE_CLASS
#ifdef BUILD_itcl
#   define TCL_STORAGE_CLASS DLLEXPORT
#else
#   ifdef USE_ITCL_STUBS
#	define TCL_STORAGE_CLASS
#   else
#	define TCL_STORAGE_CLASS DLLIMPORT
#   endif
#endif

/*
 * Fix the Borland bug that's in the EXTERN macro from tcl.h.
 */
#ifndef TCL_EXTERN
#   undef DLLIMPORT
#   undef DLLEXPORT
#   ifdef __cplusplus
#	define TCL_EXTERNC extern "C"
#   else
#	define TCL_EXTERNC extern
#   endif
#   if defined(STATIC_BUILD)
#	define DLLIMPORT
#	define DLLEXPORT
#	define TCL_EXTERN(RTYPE) TCL_EXTERNC RTYPE
#   elif (defined(__WIN32__) && ( \
	    defined(_MSC_VER) || (__BORLANDC__ >= 0x0550) || \
	    defined(__LCC__) || defined(__WATCOMC__) || \
	    (defined(__GNUC__) && defined(__declspec)) \
	)) || (defined(MAC_TCL) && FUNCTION_DECLSPEC)
#	define DLLIMPORT __declspec(dllimport)
#	define DLLEXPORT __declspec(dllexport)
#	define TCL_EXTERN(RTYPE) TCL_EXTERNC TCL_STORAGE_CLASS RTYPE
#   elif defined(__BORLANDC__)
#	define DLLIMPORT __import
#	define DLLEXPORT __export
	/* Pre-5.5 Borland requires the attributes be placed after the */
	/* return type instead. */
#	define TCL_EXTERN(RTYPE) TCL_EXTERNC RTYPE TCL_STORAGE_CLASS
#   else
#	define DLLIMPORT
#	define DLLEXPORT
#	define TCL_EXTERN(RTYPE) TCL_EXTERNC TCL_STORAGE_CLASS RTYPE
#   endif
#endif


/*
 * Starting from the 8.4 core, Tcl API is CONST'ified.  Our API is always
 * CONST, but we need to build with Tcl when it isn't CONST and fake it
 * when needed with <= 8.3
 *
 * http://wiki.tcl.tk/3669
 */

#ifndef CONST84
#   define CONST84
#endif


/*
 * Protection levels:
 *
 * ITCL_PUBLIC    - accessible from any namespace
 * ITCL_PROTECTED - accessible from namespace that imports in "protected" mode
 * ITCL_PRIVATE   - accessible only within the namespace that contains it
 */
#define ITCL_PUBLIC           1
#define ITCL_PROTECTED        2
#define ITCL_PRIVATE          3
#define ITCL_DEFAULT_PROTECT  4


/*
 *  Generic stack.
 */
typedef struct Itcl_Stack {
    ClientData *values;          /* values on stack */
    int len;                     /* number of values on stack */
    int max;                     /* maximum size of stack */
    ClientData space[5];         /* initial space for stack data */
} Itcl_Stack;

#define Itcl_GetStackSize(stackPtr) ((stackPtr)->len)

/*
 *  Generic linked list.
 */
struct Itcl_List;
typedef struct Itcl_ListElem {
    struct Itcl_List* owner;     /* list containing this element */
    ClientData value;            /* value associated with this element */
    struct Itcl_ListElem *prev;  /* previous element in linked list */
    struct Itcl_ListElem *next;  /* next element in linked list */
} Itcl_ListElem;

typedef struct Itcl_List {
    int validate;                /* validation stamp */
    int num;                     /* number of elements */
    struct Itcl_ListElem *head;  /* previous element in linked list */
    struct Itcl_ListElem *tail;  /* next element in linked list */
} Itcl_List;

#define Itcl_FirstListElem(listPtr) ((listPtr)->head)
#define Itcl_LastListElem(listPtr)  ((listPtr)->tail)
#define Itcl_NextListElem(elemPtr)  ((elemPtr)->next)
#define Itcl_PrevListElem(elemPtr)  ((elemPtr)->prev)
#define Itcl_GetListLength(listPtr) ((listPtr)->num)
#define Itcl_GetListValue(elemPtr)  ((elemPtr)->value)

/*
 *  Token representing the state of an interpreter.
 */
typedef struct Itcl_InterpState_ *Itcl_InterpState;


/*
 * Include the public function declarations that are accessible via
 * the stubs table.
 */

#include "itclDecls.h"


/*
 * Itcl_InitStubs is used by extensions like Itk that can be linked
 * against the itcl stubs library.  If we are not using stubs
 * then this reduces to package require.
 */

#ifdef USE_ITCL_STUBS

TCL_EXTERNC CONST char *
	Itcl_InitStubs _ANSI_ARGS_((Tcl_Interp *interp,
			    CONST char *version, int exact));
#else
#define Itcl_InitStubs(interp, version, exact) \
      Tcl_PkgRequire(interp, "Itcl", version, exact)
#endif

/*
 * Public functions that are not accessible via the stubs table.
 */


#endif /* RC_INVOKED */

#undef TCL_STORAGE_CLASS
#define TCL_STORAGE_CLASS DLLIMPORT

#endif /* ITCL_H */
