#!/bin/sh

# \
exec $BLUESPECDIR/bin/bluetcl "$0" "$@"

package require utils

proc usage {} {
    puts ""
    puts "usage: $::argv0 <options> top_package_name top_module"
    puts "Options:"
    puts "  -q             Do not print section headers"
    puts "  -p <path>      Bluespec search path"
    puts "  -bdir <dir>    Bluespec bdir directory"
    puts "  -vdir <dir>    Bluespec vdir directory"
    puts "  -generated     Print synthesized BSV modules"
    puts "  -primitives    Print Bluespec primitive modules"
    puts "  -imported      Print imported modules"
    puts "  -no-inline-fns Print modules for no-inline functions"
    puts "  -all           Alias for -generated -primitives -imported -no-inline-fns"
    puts ""
    puts " e.g: -bdir build -p build:+ -vdir rtl mkTop fpga_a"
}

set boolOptions [list -- -q -generated -primitives -imported -no-inline-fns -all]
set valOptions [list -p -bdir -vdir]

if { [catch [list ::utils::scanOptions $boolOptions $valOptions true OPT "$argv"] opts] } {
    puts stderr $opts
    usage
    exit 1
}

if {[llength $opts] == 0} {
    puts stderr "A package name argument is required"
    usage
    exit 1
}

if {[llength $opts] == 1} {
    puts stderr "A top module name is required"
    usage
    exit 1
}

if {[llength $opts] > 2} {
    puts stderr "Too many arguments"
    usage
    exit 1
}

if { [info exists OPT(-p)] } {
    Bluetcl::flags set -p $OPT(-p)
}
if { [info exists OPT(-bdir)] } {
    Bluetcl::flags set -bdir $OPT(-bdir)
}
if { [info exists OPT(-vdir)] } {
    Bluetcl::flags set -vdir $OPT(-vdir)
}

if {![info exists OPT(-all)] && ![info exists OPT(-generated)] &&
    ![info exists OPT(-no-inline-fns)] && ![info exists OPT(-primitives)] &&
    ![info exists OPT(-imported)]} {
    set OPT(-all) 1
}

set top_pkg [lindex $opts 0]
set top_mod [lindex $opts 1]

# Assume -verilog
Bluetcl::flags set -verilog

# Load the module information
Bluetcl::module load $top_pkg

# Walk the hierarchy extracting module information
set mods_to_process [list $top_pkg]
set already_done [list]
set is_noinline 0
while {[llength $mods_to_process] > 0} {
    set this_mod [utils::head $mods_to_process]
    set mods_to_process [utils::tail $mods_to_process]
    set res [Bluetcl::module submods $this_mod]
    set this_mod_type [lindex $res 0]
    if {$this_mod_type == "user" && $is_noinline != 0} {
	set this_mod_type "no-inline-fn"
    }
    array set mod_info [list $this_mod $this_mod_type]
    lappend already_done $this_mod
    set sub_mods [lindex $res 1]
    set no_inlines [lindex $res 2]
    foreach mod $sub_mods {
        set this_sub_mod [utils::snd $mod]
	if {[lsearch -exact $already_done $this_sub_mod] == -1 &&
	    [lsearch -exact $mods_to_process $this_sub_mod] == -1 } {
	    lappend mods_to_process $this_sub_mod
	}
    }
    set is_noinline 1
    foreach mod $no_inlines {
        set this_sub_mod [utils::snd $mod]
	if {[lsearch -exact $already_done $this_sub_mod] == -1 &&
	    [lsearch -exact $mods_to_process $this_sub_mod] == -1 } {
	    lappend mods_to_process $this_sub_mod
	}
    }
    set is_noinline 0
}

# Procedure to locate a file for a given module
proc lookupfile {name path exts} {
    foreach dir $path {
	foreach ext $exts {
	    set fname [join [list $name $ext] "."]
	    set fpath [file join $dir $fname]
	    if {[file exist $fpath]} {
	        return [file normalize $fpath]
	    }
	}
    }
    return "<unable to locate file for module $name>"
}

# Procedure to add a file to a list, avoiding duplication
proc addfile {name flName} {
    upvar 1 $flName file_list

    set matched 0
    foreach f $file_list {
	if {$f == $name} {
	   set matched 1
	   break
        }
    }
    if {$matched == 0} {
       lappend file_list $name
    }
}

# Identify the location of each module's file
set user_mods    [list]
set noinline_fns [list]
set primitives   [list]
set imported     [list]

set vdir [lindex [Bluetcl::flags show vdir] 1]
set bsdir $::env(BLUESPECDIR)

set libs [list [file join $bsdir "Verilog"] [file join $bsdir "Libraries"]]
set vsearch [split [lindex [Bluetcl::flags show p] 1] ":"]
set vdir_and_libs [concat $vdir $libs]
set vsearch_and_libs [concat $vsearch $libs]

foreach mod [array names mod_info] {
    set mod_type $mod_info($mod)

    # The Probe primitive has no associated Verilog module
    if {$mod_type == "primitive" && $mod == "Probe"} {
        continue
    }

    # Add the module info to the correct list
    switch -exact $mod_type {
	"user"         {addfile [lookupfile $mod $vdir_and_libs {v}] user_mods}
        "no-inline-fn" {addfile [lookupfile $mod $vdir {v}] noinline_fns}
        "primitive"    {addfile [lookupfile $mod $libs {v}] primitives}
        "import"       {addfile [lookupfile $mod $vsearch_and_libs {v vhd vhdl}] imported}
    }

    # Some primitives use other primitives
    if {$mod_type == "primitive"} {
	switch -exact $mod {
	    "MakeReset"     {addfile [lookupfile "SyncReset" $libs {v}] primitives}
	    "MakeResetA"    {addfile [lookupfile "SyncResetA" $libs {v}] primitives}
	    "SyncFIFOLevel" {addfile [lookupfile "ClockGen" $libs {v}] primitives
		             addfile [lookupfile "SyncHandshake" $libs {v}] primitives
                            }
	    "SyncFIFO"      {addfile [lookupfile "ClockGen" $libs {v}] primitives}
	    "SyncRegister " {addfile [lookupfile "ClockGen" $libs {v}] primitives
		             addfile [lookupfile "SyncHandshake" $libs {v}] primitives
                            }
        }
    }
}

if {[llength $user_mods] > 0 && ([info exists OPT(-generated)] || [info exists OPT(-all)])} {
    if {![info exists OPT(-q)]} {
        puts "# Synthesized user modules:"
    }
    foreach file $user_mods {
	puts $file
    }
}

if {[llength $noinline_fns] > 0 && ([info exists OPT(-no-inline-fns)] || [info exists OPT(-all)])} {
    if {![info exists OPT(-q)]} {
        puts "# No-inlined functions:"
    }
    foreach file $noinline_fns {
	puts $file
    }
}

if {[llength $imported] > 0 && ([info exists OPT(-imported)] || [info exists OPT(-all)])} {
    if {![info exists OPT(-q)]} {
        puts "# Imported modules:"
    }
    foreach file $imported {
	puts $file
    }
}

if {[llength $primitives] > 0 && ([info exists OPT(-primitives)] || [info exists OPT(-all)])} {
    if {![info exists OPT(-q)]} {
        puts "# Bluespec library primitives:"
    }
    foreach file $primitives {
	puts $file
    }
}

exit
