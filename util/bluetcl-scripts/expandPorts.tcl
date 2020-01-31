#!/bin/sh

# \
exec $BLUESPECDIR/bin/bluetcl "$0" "$@"

# 
set major_version 2
set minor_version 0
set version "$major_version.$minor_version"

# TODO: load rather than source ?
global env
namespace import ::Bluetcl::* 

# just to make local testing a bit easier, use my local copy here before releasing
if { $env(PWD) == "/home/sallen/customers/BluespecSteve/bluetcl" } {
    source portUtil.tcl
} else {
    source $env(BLUESPECDIR)/tcllib/bluespec/portUtil.tcl
}


######################################################################
# processSwitches also sets these switches (feel free to set them yourself)
# flags set "-verilog -vdir obj -bdir obj -simdir obj -p obj:.:+"

proc usage {} {
    puts "Usage: expandPorts.tcl <ops> packageName moduleName module.v"
    puts ""
    puts "   packageName = name of .bo file to scan (for bpackage load packageName)"
    puts "   moduleName  = name of top level module (for module ports moduleName)"
    puts "   module.v    = bsc genenerate mkModule.v file for the module we are generating a wrapper for"
    puts ""
    puts "   switches from compile (see bsc help for more detail):"
    puts "      -p <path>       - path, if suppled to bsc command (i.e. -p obj:+)"
    puts "      -verilog        - compiled to verilog <default>"
    puts "      -sim            - compiled to sim directory"
    puts ""
    puts "      -include outfile - file to write include.vh file to"
    puts "      -wrapper outfile - file to write wrapper.v file to"
    puts ""
    puts "      -rename file.tcl - tcl script creating rename pin structure"
    puts "      -makerename      - create empty .rename.tcl file to edit for -rename"
    puts "      -interface name  - interface which to expand -- defaults to packageName"
    puts ""
    puts "   i.e."
    puts "   expandPorts.tcl -verilog Block mkBlock"
    puts "       where program expects to find ./Block.ba and module mkBlock in it"
    exit
}

puts "expandPorts.tcl $argv"

portUtil::processSwitches [list {p "+"} \
                                {verilog} \
                                {sim} \
                                {include "/dev/null"} \
                                {wrapper "/dev/null"} \
                                \
                                {makerename} \
                                {rename  "/dev/null"} \
                                {interface ""} \
                                \
                                {quiet} \
                                {help} \
                                {elab} \
                                {debug}]


if {$help == 1} {
    puts "expandPorts.tcl version $version"
    puts "   portUtil.tcl version [portUtil::version]"
    usage
}

# need to know if we compiled for verilog or bluesim
set vORs "-verilog"

if {$verilog == 1} { set vORs "-verilog" }
if {$sim     == 1} { set vORs "-sim" } 

set portUtil::debug $debug

# source the "rename" file which must be defined as per doctors orders
set renameList [list]
if { ($rename != "/dev/null") && ($makerename != 1) } {
    if [file exists $rename] {
        source $rename
    } else {
        puts "// RENAME Warning: -rename file '$rename' not found"
    }
}

flags set $vORs -p $p

if {$argc != 3} {
    puts "argv = $argv"
    puts "argc = $argc"
    usage
}

# unset -nocomplain verilog
set package [lindex $argv 0]
set module  [lindex $argv 1]
set verilog [lindex $argv 2]  ;# rename command line "verilog" variable here

# interface may be set by processing args
if { $interface == "{}" } {
    set interface $package
}

bpackage load $package
module   load $module

# handy command #2
set res [portUtil::createExpandedVerilogWrapper $interface $module $verilog]
set verilogWrapper [lindex $res 0]
set verilogInclude [lindex $res 1]

set v1 $version
set v2 [portUtil::version]

########################################
# output file to $package.wrapper.v
if { $wrapper != "/dev/null" } {
    set fp [open $wrapper "w"]
    puts $fp "// autocreated by expandPorts.tcl $v1 and portUtil.tcl $v2"
    foreach line $verilogWrapper {
        puts $fp $line
    }
    close $fp
}

########################################
if { $include != "/dev/null" } {
    set fp [open $include "w"]
    puts $fp "// autocreated by expandPorts.tcl $v1 and portUtil.tcl $v2"
    foreach line $verilogInclude {
        puts $fp $line
    }
    close $fp
}

########################################

# handy command #4
#  or do what you want with the full structure returned here (not expanded)

# portUtil::mergePortAndTypeInfo $package $module $verilog
