# ----------------------------------------------------------------------
#  PURPOSE:  Electrical outlet supplying power for Appliances.
#
#   AUTHOR:  Michael J. McLennan       Phone: (610)712-2842
#            AT&T Bell Laboratories   E-mail: michael.mclennan@att.com
#
#      RCS:  $Id: Outlet.tcl,v 1.1 1998/07/27 18:41:30 stanton Exp $
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

itcl_class Outlet {
	constructor {config} {}
	method config {config} {}

	destructor {
		if {$usage > 0} bill
	}

	method use {power} {
		set usage [expr $usage+$power]
	}

	method sendBill {} {
		if {[catch "open /tmp/bill w" fout] != 0} {
			error "cannot create bill in /tmp"
		} else {
			set amount [format "$%.2f" [expr $usage*$rate]]
			puts $fout "----------------------------------------"
			puts $fout "/////////// MEGA-POWER, INC. ///////////"
			puts $fout "----------------------------------------"
			puts $fout "   Customer: $owner"
			puts $fout "     Outlet: $this"
			puts $fout "      Usage: $usage kilowatt-hours"
			puts $fout "                                        "
			puts $fout " Amount Due: $amount"
			puts $fout "----------------------------------------"
			close $fout
			exec mail $owner < /tmp/bill
			set usage 0
		}
	}

	proc bill {{customer *}} {
		foreach outlet [itcl_info objects -class Outlet] {
			set owner [$outlet info public owner -value]
			if {[string match $customer $owner]} {
				$outlet sendBill
			}
		}
	}

	proc rate {{newval ""}} {
		if {$newval == ""} {
			return $rate
		}
		set rate $newval
	}

	public owner {}
	protected usage 0

	common rate 0.05
}
