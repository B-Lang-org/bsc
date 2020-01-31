/*
 * ------------------------------------------------------------------------
 *      PACKAGE:  [incr Tk]
 *  DESCRIPTION:  Building mega-widgets with [incr Tcl]
 *
 *  [incr Tk] provides a framework for building composite "mega-widgets"
 *  using [incr Tcl] classes.  It defines a set of base classes that are
 *  specialized to create all other widgets.
 *
 *  This file defines the initialization and facilities common to all
 *  mega-widgets.
 *
 * ========================================================================
 *  AUTHOR:  Michael J. McLennan
 *           Bell Labs Innovations for Lucent Technologies
 *           mmclennan@lucent.com
 *           http://www.tcltk.com/itcl
 *
 *     RCS:  $Id: itk_cmds.c,v 1.17 2007/05/24 22:12:56 hobbs Exp $
 * ========================================================================
 *           Copyright (c) 1993-1998  Lucent Technologies, Inc.
 * ------------------------------------------------------------------------
 * See the file "license.terms" for information on usage and redistribution
 * of this file, and for a DISCLAIMER OF ALL WARRANTIES.
 */
#include "itk.h"

/*  
 * The following script is used to initialize Itcl in a safe interpreter.
 */
 
static char safeInitScript[] =
"proc ::itcl::local {class name args} {\n\
    set ptr [uplevel [list $class $name] $args]\n\
    uplevel [list set itcl-local-$ptr $ptr]\n\
    set cmd [uplevel namespace which -command $ptr]\n\
    uplevel [list trace variable itcl-local-$ptr u \"::itcl::delete object $cmd; list\"]\n\
    return $ptr\n\
}";  

/*
 *  FORWARD DECLARATIONS
 */
static int Initialize _ANSI_ARGS_((Tcl_Interp *interp));
/*
 * The following string is the startup script executed in new
 * interpreters.  It looks on disk in several different directories
 * for a script "init.tcl" that is compatible with this version
 * of Tcl.  The init.tcl script does all of the real work of
 * initialization.
 */

static char initScript[] = "\n\
namespace eval ::itk {\n\
    proc _find_init {} {\n\
        global env tcl_library\n\
        variable library\n\
        variable version\n\
        rename _find_init {}\n\
        if {[info exists library]} {\n\
            lappend dirs $library\n\
        } else {\n\
            if {[catch {uplevel #0 source -rsrc itk}] == 0} {\n\
                return\n\
            }\n\
            set dirs {}\n\
            if {[info exists env(ITK_LIBRARY)]} {\n\
                lappend dirs $env(ITK_LIBRARY)\n\
            }\n\
            lappend dirs [file join [file dirname $tcl_library] itk$version]\n\
            set bindir [file dirname [info nameofexecutable]]\n\
            lappend dirs [file join $bindir .. lib itk$version]\n\
            lappend dirs [file join $bindir .. library]\n\
            lappend dirs [file join $bindir .. .. library]\n\
            lappend dirs [file join $bindir .. .. itk library]\n\
            # On MacOSX, check the directories in the tcl_pkgPath\n\
            if {[string equal $::tcl_platform(platform) \"unix\"] && \
                    [string equal $::tcl_platform(os) \"Darwin\"]} {\n\
                foreach d $::tcl_pkgPath {\n\
                    lappend dirs [file join $d itk$version]\n\
                }\n\
            }\n\
        }\n\
        foreach i $dirs {\n\
            set library $i\n\
            set itkfile [file join $i itk.tcl]\n\
            if {![catch {uplevel #0 [list source $itkfile]} msg]} {\n\
                return\n\
            }\n\
        }\n\
        set msg \"Can't find a usable itk.tcl in the following directories:\n\"\n\
        append msg \"    $dirs\n\"\n\
        append msg \"This probably means that Itcl/Itk weren't installed properly.\n\"\n\
        append msg \"If you know where the Itk library directory was installed,\n\"\n\
        append msg \"you can set the environment variable ITK_LIBRARY to point\n\"\n\
        append msg \"to the library directory.\n\"\n\
        error $msg\n\
    }\n\
    _find_init\n\
}";

/*
 * ------------------------------------------------------------------------
 *  Initialize()
 *
 *  Invoked whenever a new interpeter is created to install the
 *  [incr Tk] package.
 *
 *  Creates the "::itk" namespace and installs access commands.
 *
 *  Returns TCL_OK on success, or TCL_ERROR (along with an error
 *  message in the interpreter) if anything goes wrong.
 * ------------------------------------------------------------------------
 */
static int
Initialize(interp)
    Tcl_Interp *interp;  /* interpreter to be updated */
{
    Tcl_Namespace *itkNs, *parserNs;
    ClientData parserInfo;

#ifndef USE_TCL_STUBS
    if (Tcl_PkgRequire(interp, "Tcl", TCL_VERSION, 0) == NULL) {
      return TCL_ERROR;
    }
    if (Tcl_PkgRequire(interp, "Tk", TK_VERSION, 0) == NULL) {
      return TCL_ERROR;
    }
    if (Tcl_PkgRequire(interp, "Itcl", ITCL_VERSION, 0) == NULL) {
      return TCL_ERROR;
    }
#else
    if (Tcl_InitStubs(interp, "8.1", 0) == NULL) {
      return TCL_ERROR;
    }
    if (Tk_InitStubs(interp, "8.1", 0) == NULL) {
	return TCL_ERROR;
    };
    if (Itcl_InitStubs(interp, ITCL_VERSION, 1) == NULL) {
	return TCL_ERROR;
    }
#endif


    /*
     *  Add the "itk_option" ensemble to the itcl class definition parser.
     */
    parserNs = Tcl_FindNamespace(interp, "::itcl::parser",
        (Tcl_Namespace*)NULL, /* flags */ 0);

    if (!parserNs) {
        Tcl_AppendResult(interp,
            "cannot initialize [incr Tk]: [incr Tcl] has not been installed\n",
            "Make sure that Itcl_Init() is called before Itk_Init()",
            (char*)NULL);
        return TCL_ERROR;
    }
    parserInfo = parserNs->clientData;

    if (Itcl_CreateEnsemble(interp, "::itcl::parser::itk_option") != TCL_OK) {
        return TCL_ERROR;
    }
    if (Itcl_AddEnsemblePart(interp, "::itcl::parser::itk_option",
            "define", "-switch resourceName resourceClass init ?config?",
            Itk_ClassOptionDefineCmd,
            parserInfo, Itcl_ReleaseData) != TCL_OK) {

        return TCL_ERROR;
    }
    Itcl_PreserveData(parserInfo);

    if (Itcl_AddEnsemblePart(interp, "::itcl::parser::itk_option",
            "add", "name ?name name...?",
            Itk_ClassOptionIllegalCmd,
            (ClientData)NULL, (Tcl_CmdDeleteProc*)NULL) != TCL_OK ||

        Itcl_AddEnsemblePart(interp, "::itcl::parser::itk_option",
            "remove", "name ?name name...?",
            Itk_ClassOptionIllegalCmd,
            (ClientData)NULL, (Tcl_CmdDeleteProc*)NULL) != TCL_OK) {

        return TCL_ERROR;
    }

    /*
     *  Install [incr Tk] facilities if not already installed.
     */
    itkNs = Tcl_FindNamespace(interp, "::itk", (Tcl_Namespace*)NULL,
        /* flags */ 0);

    if (itkNs == NULL) {
	/*
	 *  Create the "itk" namespace.  Export all the commands in
	 *  the namespace so that they can be imported by a command
	 *  such as "namespace import itk::*"
	 */
	itkNs = Tcl_CreateNamespace(interp, "::itk",
	    (ClientData)NULL, (Tcl_NamespaceDeleteProc*)NULL);
    }

    if (!itkNs ||
        Tcl_Export(interp, itkNs, "*", /* resetListFirst */ 1) != TCL_OK) {
        return TCL_ERROR;
    }

    /*
     *  Setup things for itk::Archetype base class.
     */
    if (Itk_ArchetypeInit(interp) != TCL_OK) {
        return TCL_ERROR;
    }

    /*
     *  Fix the "itcl::configbody" command to recognize mega-widget
     *  options.
     */
    Tcl_CreateObjCommand(interp, "::itcl::configbody", Itk_ConfigBodyCmd,
        (ClientData)NULL, (Tcl_CmdDeleteProc*)NULL);

    Tcl_SetVar(interp, "::itk::version", ITK_VERSION, 0);
    Tcl_SetVar(interp, "::itk::patchLevel", ITK_PATCH_LEVEL, 0);

    /*
     *  Signal that the package has been loaded and provide the Itk Stubs table
     *  for dependent modules.  I know this is unlikely, but possible that
     *  someone could be extending Itk.  Who is to say that Itk is the
     *  end-of-the-line?
     */

#if TCL_DOES_STUBS
    {
	extern ItkStubs itkStubs;
	if (Tcl_PkgProvideEx(interp, "Itk", ITK_VERSION,
		(ClientData) &itkStubs) != TCL_OK) {
	    return TCL_ERROR;
	}
    }
#else
    if (Tcl_PkgProvide(interp, "Itk", ITK_VERSION) != TCL_OK) {
	return TCL_ERROR;
    }
#endif
    return TCL_OK;
}

/*
 * ------------------------------------------------------------------------
 *  Itk_Init()
 *
 *  Invoked whenever a new interpeter is created to install the
 *  [incr Tcl] package.  Usually invoked within Tcl_AppInit() at
 *  the start of execution.
 *
 *  Creates the "::itk" namespace and installs access commands.
 *
 *  Returns TCL_OK on success, or TCL_ERROR (along with an error
 *  message in the interpreter) if anything goes wrong.
 * ------------------------------------------------------------------------
 */
int
Itk_Init(interp)
    Tcl_Interp *interp;  /* interpreter to be updated */
{
    if (Initialize(interp) != TCL_OK) {
	return TCL_ERROR;
    }
    return Tcl_Eval(interp, initScript);
    return TCL_OK;
}


/*
 * ------------------------------------------------------------------------
 *  Itk_SafeInit()
 *   
 *  Invoked whenever a new SAFE INTERPRETER is created to install
 *  the [incr Tcl] package.
 *      
 *  Creates the "::itk" namespace and installs access commands for
 *  creating classes and querying info.
 *  
 *  Returns TCL_OK on success, or TCL_ERROR (along with an error 
 *  message in the interpreter) if anything goes wrong.
 * ------------------------------------------------------------------------
 */  
int 
Itk_SafeInit(interp)
    Tcl_Interp *interp;  /* interpreter to be updated */ 
{   
    if (Initialize(interp) != TCL_OK) {
        return TCL_ERROR;
    }
    return Tcl_Eval(interp, safeInitScript);
}


/*
 * ------------------------------------------------------------------------
 *  Itk_ConfigBodyCmd()
 *
 *  Replacement for the usual "itcl::configbody" command.  Recognizes
 *  mega-widget options included in a class definition.  Options are
 *  identified by their "switch" name, but without the "-" prefix:
 *
 *    itcl::configbody <class>::<itkOption> <body>
 *
 *  Handles bodies for public variables as well:
 *
 *    itcl::configbody <class>::<publicVar> <body>
 *
 *  If an <itkOption> is found, it has priority over public variables.
 *  If <body> has the form "@name" then it is treated as a reference
 *  to a C handling procedure; otherwise, it is taken as a body of
 *  Tcl statements.
 *
 *  Returns TCL_OK/TCL_ERROR to indicate success/failure.
 * ------------------------------------------------------------------------
 */
/* ARGSUSED */
int
Itk_ConfigBodyCmd(dummy, interp, objc, objv)
    ClientData dummy;        /* unused */
    Tcl_Interp *interp;      /* current interpreter */
    int objc;                /* number of arguments */
    Tcl_Obj *CONST objv[];   /* argument objects */
{
    int result = TCL_OK;

    char *token, *head, *tail;
    ItclClass *cdefn;
    ItclMemberCode *mcode;
    ItkClassOptTable *optTable;
    Tcl_HashEntry *entry;
    ItkClassOption *opt;
    Tcl_DString buffer;

    if (objc != 3) {
        Tcl_WrongNumArgs(interp, 1, objv, "class::option body");
        return TCL_ERROR;
    }

    /*
     *  Parse the member name "namesp::namesp::class::option".
     *  Make sure that a class name was specified, and that the
     *  class exists.
     */
    token = Tcl_GetStringFromObj(objv[1], (int*)NULL);
    Itcl_ParseNamespPath(token, &buffer, &head, &tail);

    if (!head || *head == '\0') {
        Tcl_AppendResult(interp,
            "missing class specifier for body declaration \"", token, "\"",
            (char*)NULL);
        result = TCL_ERROR;
        goto configBodyCmdDone;
    }

    cdefn = Itcl_FindClass(interp, head, /* autoload */ 1);
    if (cdefn == NULL) {
        result = TCL_ERROR;
        goto configBodyCmdDone;
    }

    /*
     *  Look first for a configuration option with that name.
     *  If it is not found, assume the reference is for a public
     *  variable, and use the usual "configbody" implementation
     *  to handle it.
     */
    optTable = Itk_FindClassOptTable(cdefn);
    opt = NULL;

    if (optTable) {
        Tcl_DString optName;

        Tcl_DStringInit(&optName);
        Tcl_DStringAppend(&optName, "-", -1);
        Tcl_DStringAppend(&optName, tail, -1);
        entry = Tcl_FindHashEntry(&optTable->options,
            Tcl_DStringValue(&optName));

        if (entry) {
            opt = (ItkClassOption*)Tcl_GetHashValue(entry);
        }
        Tcl_DStringFree(&optName);
    }

    if (opt == NULL) {
        result = Itcl_ConfigBodyCmd(dummy, interp, objc, objv);
        goto configBodyCmdDone;
    }

    /*
     *  Otherwise, change the implementation for this option.
     */
    token = Tcl_GetStringFromObj(objv[2], (int*)NULL);

    if (Itcl_CreateMemberCode(interp, cdefn, (char*)NULL, token,
        &mcode) != TCL_OK) {

        result = TCL_ERROR;
        goto configBodyCmdDone;
    }

    Itcl_PreserveData((ClientData)mcode);
    Itcl_EventuallyFree((ClientData)mcode, Itcl_DeleteMemberCode);

    if (opt->member->code) {
        Itcl_ReleaseData((ClientData)opt->member->code);
    }
    opt->member->code = mcode;

configBodyCmdDone:
    Tcl_DStringFree(&buffer);
    return result;
}
