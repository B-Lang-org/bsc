#!/bin/sh

# \
exec $BLUESPECDIR/bin/bluetcl "$0" "$@"

package require Bluetcl
package require types
namespace import types::getNonPolyType types::showTypeSize

namespace import utils::map_

proc usage {} {
    puts "Usage: dumpStructures.tcl <options> packageName <types>"
    puts ""
    puts "  packageName = name of Bluespec package to process"
    puts "    expects that packageName.bo files exists"
    puts "  types = optional list of types to dump the structures"
    puts "           default is to dump all non polymorphic types"
    puts ""
    puts "  options are:"
    puts "   -p <path> path name for additional bo files (same as bsc -p)"
    puts ""
    puts "Examples:"
    puts "% dumpStructures.tcl Prelude"
    puts "    shows the verilog structures for all the concrete type from Prelude"
    puts "% dumpStructures.tcl Vector \"Vector\#(Maybe\#(int))\""
    puts "    shows the structures for the concrete types Vector\#(5,Maybe\#(int)))"
    puts ""
    exit 
}

set boolOptions [list]
set valOptions [list -p]

if { 1 == [catch [list ::utils::scanOptions $boolOptions $valOptions true OPT "$argv"] args ] } {
    puts "Error: $args"
    puts ""
    usage
}

set packName [::utils::head $args]
set types [::utils::tail $args]

if { $packName == "" } { usage }


## Set any flags for search path, e,g -p
if { [info exists OPT(-p)] } {
    Bluetcl::flags set -p $OPT(-p):+
}

Bluetcl::bpackage load $packName

if { $types == "" } {
    set types [getNonPolyType $packName]
}

foreach t $types {
    puts "-- $t -----------------------------------------------"
    showTypeSize $t

}

