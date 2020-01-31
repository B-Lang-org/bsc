# ----------------------------------------------------------------------
#  PURPOSE:  Tracking for hazardous products manufactured by the
#            "toaster" company.
#
#   AUTHOR:  Michael J. McLennan       Phone: (610)712-2842
#            AT&T Bell Laboratories   E-mail: michael.mclennan@att.com
#
#      RCS:  $Id: Hazard.tcl,v 1.1 1998/07/27 18:41:30 stanton Exp $
# ----------------------------------------------------------------------
#               Copyright (c) 1993  AT&T Bell Laboratories
# ======================================================================
# Permission to use, copy, modify, and distribute this software and its
# documentation for any purpose and without fee is hereby granted,
# provided that the above copyright notice appear in all copies and that
# both that the copyright notice and warranty disclaimer appear in
# supporting documentation, and that the names of AT&T Bell Laboratories
# any of their entities not be used in advertising or publicity
# pertaining to distribution of the software without specific, written
# prior permission.
#
# AT&T disclaims all warranties with regard to this software, including
# all implied warranties of merchantability and fitness.  In no event
# shall AT&T be liable for any special, indirect or consequential
# damages or any damages whatsoever resulting from loss of use, data or
# profits, whether in an action of contract, negligence or other
# tortuous action, arising out of or in connection with the use or
# performance of this software.
# ======================================================================

itcl_class HazardRec {
	constructor {cname} {
		set class $cname
	}
	method change {var inc} {
		if {![info exists $var]} {
			error "bad field \"$var\""
		}
		incr $var $inc
	}
	method report {} {
		return "$class: $total produced, $actives active, $accidents accidents"
	}
	protected class {}
	protected total 0
	protected actives 0
	protected accidents 0
}

itcl_class Hazard {

	constructor {} {
		set class [virtual info class]
		if {![info exists recs($class)]} {
			set recs($class) [HazardRec #auto $class]
		}
		$recs($class) change total +1
		$recs($class) change actives +1
	}
	destructor {
		set class [virtual info class]
		$recs($class) change actives -1
	}

	method accident {mesg} {
		set class [virtual info class]
		$recs($class) change accidents +1
		puts stderr $mesg
	}

	proc report {class} {
		if {[info exists recs($class)]} {
			return [$recs($class) report]
		} else {
			error "no information for class \"$class\""
		}
	}
    common recs
}
