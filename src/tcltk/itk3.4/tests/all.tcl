# all.tcl --
#
# This file contains a top-level script to run all of the Tcl
# tests.  Execute it by invoking "source all.test" when running tcltest
# in this directory.
#
# Copyright (c) 1998-2000 by Ajuba Solutions
# All rights reserved.
# 
# RCS: @(#) $Id: all.tcl,v 1.4 2004/09/22 09:37:08 davygrvy Exp $

package require tcltest 2.1

tcltest::testsDirectory [file dir [info script]]
tcltest::runAllTests

return
