#
# itcl.tcl
# ----------------------------------------------------------------------
# Invoked automatically upon startup to customize the interpreter
# for [incr Tcl].
# ----------------------------------------------------------------------
#   AUTHOR:  Michael J. McLennan
#            Bell Labs Innovations for Lucent Technologies
#            mmclennan@lucent.com
#            http://www.tcltk.com/itcl
#
#      RCS:  $Id: itcl.tcl,v 1.10 2008/08/06 22:39:57 msofer Exp $
# ----------------------------------------------------------------------
#            Copyright (c) 1993-1998  Lucent Technologies, Inc.
# ======================================================================
# See the file "license.terms" for information on usage and
# redistribution of this file, and for a DISCLAIMER OF ALL WARRANTIES.

proc ::itcl::delete_helper { name args } {
    ::itcl::delete object $name
}

# ----------------------------------------------------------------------
#  USAGE:  local <className> <objName> ?<arg> <arg>...?
#
#  Creates a new object called <objName> in class <className>, passing
#  the remaining <arg>'s to the constructor.  Unlike the usual
#  [incr Tcl] objects, however, an object created by this procedure
#  will be automatically deleted when the local call frame is destroyed.
#  This command is useful for creating objects that should only remain
#  alive until a procedure exits.
# ----------------------------------------------------------------------
proc ::itcl::local {class name args} {
    set ptr [uplevel [list $class $name] $args]
    uplevel [list set itcl-local-$ptr $ptr]
    set cmd [uplevel namespace which -command $ptr]
    uplevel [list trace variable itcl-local-$ptr u \
        "::itcl::delete_helper $cmd"]
    return $ptr
}

# ----------------------------------------------------------------------
# auto_mkindex
# ----------------------------------------------------------------------
# Define Itcl commands that will be recognized by the auto_mkindex
# parser in Tcl...
#

#
# USAGE:  itcl::class name body
# Adds an entry for the given class declaration.
#
foreach cmd {itcl::class class} {
    auto_mkindex_parser::command $cmd {name body} {
	variable index
	variable scriptFile
	append index "set [list auto_index([fullname $name])]"
	append index " \[list source \[file join \$dir [list $scriptFile]\]\]\n"

	variable parser
	variable contextStack
	set contextStack [linsert $contextStack 0 $name]
	$parser eval $body
	set contextStack [lrange $contextStack 1 end]
    }
}

#
# USAGE:  itcl::body name arglist body
# Adds an entry for the given method/proc body.
#
foreach cmd {itcl::body body} {
    auto_mkindex_parser::command $cmd {name arglist body} {
	variable index
	variable scriptFile
	append index "set [list auto_index([fullname $name])]"
	append index " \[list source \[file join \$dir [list $scriptFile]\]\]\n"
    }
}

#
# USAGE:  itcl::configbody name arglist body
# Adds an entry for the given method/proc body.
#
foreach cmd {itcl::configbody configbody} {
    auto_mkindex_parser::command $cmd {name body} {
	variable index
	variable scriptFile
	append index "set [list auto_index([fullname $name])]"
	append index " \[list source \[file join \$dir [list $scriptFile]\]\]\n"
    }
}

#
# USAGE:  ensemble name ?body?
# Adds an entry to the auto index list for the given ensemble name.
#
foreach cmd {itcl::ensemble ensemble} {
    auto_mkindex_parser::command $cmd {name {body ""}} {
	variable index
	variable scriptFile
	append index "set [list auto_index([fullname $name])]"
	append index " \[list source \[file join \$dir [list $scriptFile]\]\]\n"
    }
}

#
# USAGE:  public arg ?arg arg...?
#         protected arg ?arg arg...?
#         private arg ?arg arg...?
#
# Evaluates the arguments as commands, so we can recognize proc
# declarations within classes.
#
foreach cmd {public protected private} {
    auto_mkindex_parser::command $cmd {args} {
        variable parser
        $parser eval $args
    }
}

# ----------------------------------------------------------------------
# auto_import
# ----------------------------------------------------------------------
# This procedure overrides the usual "auto_import" function in the
# Tcl library.  It is invoked during "namespace import" to make see
# if the imported commands reside in an autoloaded library.  If so,
# stubs are created to represent the commands.  Executing a stub
# later on causes the real implementation to be autoloaded.
#
# Arguments -
# pattern	The pattern of commands being imported (like "foo::*")
#               a canonical namespace as returned by [namespace current]

proc auto_import {pattern} {
    global auto_index

    set ns [uplevel namespace current]
    set patternList [auto_qualify $pattern $ns]

    auto_load_index

    foreach pattern $patternList {
        foreach name [array names auto_index $pattern] {
            if {"" == [info commands $name]} {
                ::itcl::import::stub create $name
            }
        }
    }
}

# ----------------------------------------------------------------------
# itcl_class, itcl_info
# ----------------------------------------------------------------------
# Compat handling for itcl_class/info, set for auto_index loading only
#
# Only need to convert public/protected usage.
# Uses Tcl 8.4+ coding style
#

if {([llength [info commands itcl_class]] == 0)
    && [package vsatisfies $::tcl_version 8.4]} {
    proc ::itcl::CmdSplit {body} {
	# DGP's command split
	set commands {}
	set chunk ""
	foreach line [split $body "\n"] {
	    append chunk $line
	    if {[info complete "$chunk\n"]} {
		# $chunk ends in a complete Tcl command, and none of the
		# newlines within it end a complete Tcl command.  If there
		# are multiple Tcl commands in $chunk, they must be
		# separated by semi-colons.
		set cmd ""
		foreach part [split $chunk ";"] {
		    append cmd $part
		    if {[info complete "$cmd\n"]} {
			set cmd [string trimleft $cmd]
			# Drop empty commands and comments
			if {($cmd ne "") && ![string match #* $cmd]} {
			    lappend commands $cmd
			}
			if {[string match #* $cmd]} {
			    set cmd "#;"
			} else {
			    set cmd ""
			}
		    } else {
			# No complete command yet.
			# Replace semicolon and continue
			append cmd ";"
		    }
		}
		set chunk ""
	    } else {
		# No end of command yet.  Put the newline back and continue
		append chunk "\n"
	    }
	}
	if {[string trim $chunk] ne ""} {
	    return -code error "Can't parse body into a\
                sequence of commands.\n\tIncomplete command:\n$chunk"
	}
	return $commands
    }

    proc ::itcl::itcl_class {className body} {
	# inherit baseClass ?baseClass...? ; # no change
	# constructor args ?init? body     ; # no change
	# destructor body                  ; # no change
	# method name args body            ; # no change
	# proc name args body              ; # no change
	# common varName ?init?            ; # no change
	# public varName ?init? ?config?   ; # variable ...
	# protected varName ?init?         ; # variable ... (?)
	set cmds [::itcl::CmdSplit $body]
	set newcmds [list]
	foreach cmd $cmds {
	    if {![catch {lindex $cmd 0} firstcmd]} {
		if {$firstcmd eq "public" || $firstcmd eq "protected"} {
		    set cmd [linsert $cmd 1 "variable"]
		}
	    }
	    append newcmds "$cmd\n"
	}
	return [uplevel 1 [list ::itcl::class $className $newcmds]]
    }
    set ::auto_index(itcl_class) [list interp alias {} ::itcl_class {} ::itcl::itcl_class]
    set ::auto_index(itcl_info) [list interp alias {} ::itcl_info {} ::itcl::find]
}

# ----------------------------------------------------------------------
# [namespace inscope]
# ----------------------------------------------------------------------
# Modify [unknown] to handle Itcl's usage of [namespace inscope]
#

namespace eval ::itcl {
    variable UNKNOWN_ORIG [info body ::unknown]
    variable UNKNOWN_ADD {
	##########################################################################
	##########################################################################
	# ADDED BY Itcl
	#
	# Itcl requires special handling for [namespace inscope]
	#

	set cmd [lindex $args 0]
	if {[regexp "^:*namespace\[ \t\n\]+inscope" $cmd] && [llength $cmd] == 4} {
	    #return -code error "You need an {*}"
	    set arglist [lrange $args 1 end]
	    set ret [catch {uplevel 1 ::$cmd $arglist} result opts]
	    dict unset opts -errorinfo
	    dict incr opts -level
	    return -options $opts $result
	}
	##########################################################################
	##########################################################################
    }
    proc ::unknown args "$UNKNOWN_ADD\n$UNKNOWN_ORIG"

}
