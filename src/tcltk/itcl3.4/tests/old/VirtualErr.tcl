#
# Old test suite for [incr Tcl] v1.5
# ----------------------------------------------------------------------
#   AUTHOR:  Michael J. McLennan
#            Bell Labs Innovations for Lucent Technologies
#            mmclennan@lucent.com
#            http://www.tcltk.com/itcl
#
#      RCS:  $Id: VirtualErr.tcl,v 1.1 1998/07/27 18:41:23 stanton Exp $
# ----------------------------------------------------------------------
#            Copyright (c) 1993-1998  Lucent Technologies, Inc.
# ======================================================================
# See the file "license.terms" for information on usage and
# redistribution of this file, and for a DISCLAIMER OF ALL WARRANTIES.

itcl_class VirtualErr {
	#
	#  The following inherit statement will cause an error,
	#  since it will find the same base class "Foo" inherited
	#  from several places.
	#
	inherit Mongrel Foo BarFoo
}
