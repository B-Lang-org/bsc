# ----------------------------------------------------------------------
#  PURPOSE:  Class definition for handling "smart" toasters via
#            [incr Tcl].  A "smart" toaster is a toaster that
#            automatically cleans itself when the crumb tray is full.
#
#   AUTHOR:  Michael J. McLennan       Phone: (610)712-2842
#            AT&T Bell Laboratories   E-mail: michael.mclennan@att.com
#
#      RCS:  $Id: SmartToaster.tcl,v 1.1 1998/07/27 18:41:31 stanton Exp $
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

itcl_class SmartToaster {
	inherit Toaster

	method toast {nslices} {
		if {$crumbs >= [expr $maxcrumbs-10]} {
			clean
		}
		return [Toaster::toast $nslices]
	}
}
