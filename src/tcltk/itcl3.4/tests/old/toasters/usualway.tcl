# ----------------------------------------------------------------------
#  PURPOSE:  Procedures for managing toasters in the usual
#            procedure-oriented Tcl programming style.  These
#            routines illustrate data sharing through global
#            variables and naming conventions to logically group
#            related procedures.  The same programming task can
#            be accomplished much more cleanly with [incr Tcl].
#            Inheritance also allows new behavior to be "mixed-in"
#            more cleanly (see Appliance and Product base classes).
#
#   AUTHOR:  Michael J. McLennan       Phone: (610)712-2842
#            AT&T Bell Laboratories   E-mail: michael.mclennan@att.com
#
#      RCS:  $Id: usualway.tcl,v 1.1 1998/07/27 18:41:32 stanton Exp $
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

# ----------------------------------------------------------------------
# COMMAND: make_toaster <name> <heat>
#
#   INPUTS
#     <name> = name of new toaster
#     <heat> = heat setting (1-5)
#
#   RETURNS
#     name of new toaster
#
#   SIDE-EFFECTS
#     Creates a record of a new toaster with the given heat setting
#     and an empty crumb tray.
# ----------------------------------------------------------------------
proc make_toaster {name heat} {
	global allToasters

	if {$heat < 1 || $heat > 5} {
		error "invalid heat setting: should be 1-5"
	}
	set allToasters($name-heat) $heat
	set allToasters($name-crumbs) 0
}

# ----------------------------------------------------------------------
# COMMAND: toast_bread <name> <slices>
#
#   INPUTS
#       <name> = name of toaster used to toast bread
#     <slices> = number of bread slices (1 or 2)
#
#   RETURNS
#     current crumb count
#
#   SIDE-EFFECTS
#     Toasts bread and adds crumbs to crumb tray.
# ----------------------------------------------------------------------
proc toast_bread {name slices} {
	global allToasters

	if {[info exists allToasters($name-crumbs)]} {
		set c $allToasters($name-crumbs)
		set c [expr $c+$allToasters($name-heat)*$slices]
		set allToasters($name-crumbs) $c
	} else {
		error "not a toaster: $name"
	}
}

# ----------------------------------------------------------------------
# COMMAND: clean_toaster <name>
#
#   INPUTS
#       <name> = name of toaster to be cleaned
#
#   RETURNS
#     current crumb count
#
#   SIDE-EFFECTS
#     Cleans toaster by emptying crumb tray.
# ----------------------------------------------------------------------
proc clean_toaster {name} {
	global allToasters
	set allToasters($name-crumbs) 0
}

# ----------------------------------------------------------------------
# COMMAND: destroy_toaster <name>
#
#   INPUTS
#       <name> = name of toaster to be destroyed
#
#   RETURNS
#     nothing
#
#   SIDE-EFFECTS
#     Spills all crumbs in the toaster and then destroys it.
# ----------------------------------------------------------------------
proc destroy_toaster {name} {
	global allToasters

	if {[info exists allToasters($name-crumbs)]} {
		puts stdout "$allToasters($name-crumbs) crumbs ... what a mess!"
		unset allToasters($name-heat)
		unset allToasters($name-crumbs)
	}
}
