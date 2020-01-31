# ----------------------------------------------------------------------
#  PURPOSE:  Class definition for handling toasters via [incr Tcl].
#
#   AUTHOR:  Michael J. McLennan       Phone: (610)712-2842
#            AT&T Bell Laboratories   E-mail: michael.mclennan@att.com
#
#      RCS:  $Id: Toaster.tcl,v 1.1 1998/07/27 18:41:31 stanton Exp $
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

itcl_class Toaster {
	inherit Appliance Hazard

	constructor {config} {}
	destructor {
		if {$crumbs > 0} {
			puts stdout "$crumbs crumbs ... what a mess!"
		}
	}
	method config {config} {}

	method toast {nslices} {
		power [expr 0.03*$heat]
		if {$nslices < 1 || $nslices > 2} {
			error "bad number of slices: should be 1 or 2"
		}
		set crumbs [expr $crumbs+$heat*$nslices]
		if {$crumbs >= $maxcrumbs} {
			accident "== FIRE! FIRE! =="
			set crumbs $maxcrumbs
		}
		return [check]
	}

	method clean {} {
		power 0.5
		set crumbs 0
		return [check]
	}

	method check {} {
		set level [expr $crumbs*100.0/$maxcrumbs]
		return [format "crumb tray: %.0f%% full" $level]
	}

	proc resize {newsize} {
		set maxcrumbs $newsize
	}

	public heat 3 {
		if {$heat < 1 || $heat > 5} {
			error "invalid setting $heat: should be 1-5"
		}
	}
	protected crumbs 0
	common maxcrumbs 40
}
