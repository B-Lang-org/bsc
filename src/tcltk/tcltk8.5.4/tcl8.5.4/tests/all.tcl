# all.tcl --
#
# This file contains a top-level script to run all of the Tcl
# tests.  Execute it by invoking "source all.test" when running tcltest
# in this directory.
#
# Copyright (c) 1998-1999 by Scriptics Corporation.
# Copyright (c) 2000 by Ajuba Solutions
#
# See the file "license.terms" for information on usage and redistribution
# of this file, and for a DISCLAIMER OF ALL WARRANTIES.
# 
# RCS: @(#) $Id: all.tcl,v 1.19 2006/11/03 00:34:52 hobbs Exp $

package require Tcl 8.5
package require tcltest 2.2
namespace import tcltest::*
configure {*}$argv -testdir [file dir [info script]]
runAllTests
