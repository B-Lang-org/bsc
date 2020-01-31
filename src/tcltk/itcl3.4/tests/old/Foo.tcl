#
# Old test suite for [incr Tcl] v1.5
# ----------------------------------------------------------------------
#   AUTHOR:  Michael J. McLennan
#            Bell Labs Innovations for Lucent Technologies
#            mmclennan@lucent.com
#            http://www.tcltk.com/itcl
#
#      RCS:  $Id: Foo.tcl,v 1.1 1998/07/27 18:41:22 stanton Exp $
# ----------------------------------------------------------------------
#            Copyright (c) 1993-1998  Lucent Technologies, Inc.
# ======================================================================
# See the file "license.terms" for information on usage and
# redistribution of this file, and for a DISCLAIMER OF ALL WARRANTIES.

itcl_class Foo {
	#
	#  Constructor/destructor add their name to a global var for
	#  tracking implicit constructors/destructors
	#
	constructor {config} {
		global WATCH
		lappend WATCH [namespace current]
		set foos([namespace tail $this]) $this
		incr nfoo
	}
	destructor {
		global WATCH
		lappend WATCH [namespace current]
		unset foos([namespace tail $this])
	}

	method nothing {} {}

	method do {cmds} {
		return "Foo says '[eval $cmds]'"
	}

	#
	#  Test formal arguments for methods/procs
	#  (formal args should not clobber data members)
	#
	method testMethodArgs {blit _blit args} {
		return "$blit, $_blit, and [llength $args] other args"
	}
	proc testProcArgs {nfoo args} {
		return "$nfoo, and [llength $args] other args"
	}

	#
	#  Test methods using the "config" argument
	#
	method config {{config "-blit auto -blat matic"}} {
		return $config
	}
	method xconfig {x config} {
		return "$x|$config"
	}
	method configx {config x} {
		return "$config|$x"
	}
	method xecho {x args} {
		return "$x | [llength $args]: $args"
	}

	#
	#  Test procs and access to common vars
	#
	proc echo {x args} {
		return "$x | [llength $args]: $args"
	}
	proc foos {{pattern *}} {
		set retn {}
		foreach i [array names foos] {
			if {$i != "_ignore_" && [string match $pattern $i]} {
				lappend retn $i
			}
		}
		return $retn
	}
	proc nfoos {} {
		return $nfoo
	}

	#
	#  Test public/protected/common variable definitions
	#
	public blit
	public blat 0
	public blot 1 {global WATCH; set WATCH "blot=$blot"}

	protected _blit
	protected _blat 0

	common foos
	set foos(_ignore_) "foos-is-now-an-array"

	common nfoo 0
}
