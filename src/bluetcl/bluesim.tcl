#!/bin/sh

# TCL includes the next line in this comment \
exec bluetcl "$0" -quiet -- "$@"

set major_version 2
set minor_version 0
set version "$major_version.$minor_version"

set script_name ""
set top_module ""
set creation_time 0

package require Bluesim
namespace import Bluesim::sim
namespace import Bluesim::help

proc usage {} {
    global argv0
    global script_name

    if {$script_name != ""} {
        puts "Usage: $script_name \[opts\]"
	set prefix $script_name
    } else {  
        puts "Usage: [file tail $argv0] <model> <top_module> \[opts\]"
        puts ""
        puts "   model = name of Bluesim model file to load and execute"
	puts "   top_module = name of the top module in the design"
	set prefix "[file tail $argv0] mkTop.so mkTop"
    }
    puts ""
    puts "Options:"
    puts "  -c <commands> = execute commands given as an argument"
    puts "  -f <file>     = execute script from file"
    puts "  -h            = print help and exit"
    puts "  -m <N>        = execute for N cycles"
    puts "  -v            = print version information and exit"
    puts "  -V \[<file>\]   = dump waveforms to VCD file (default: dump.vcd)"
    puts "  +<arg>        = Verilog-style plus-arg"
    puts ""    
    puts "Examples:"
    puts "  $prefix"
    puts "  $prefix -c 'sim step 40; puts \[sim time\]'"
    puts "  $prefix -f sim_cmds.tcl"
    puts "  $prefix -m 3000"
    puts "  $prefix -V sim.vcd"
    puts "  $prefix +doFoo"
    exit
}

# interpret command-line arguments

# bluetcl will remove its arguments from $argv but not update $argc
set actual_argc [llength "$argv"]
set current_arg 0

if {$actual_argc < 1} {
    puts "Error: you must supply a Bluesim model name"
    usage
}

# bluetcl will leave in "--"
if { [lindex $argv 0] eq "--" } {
    incr current_arg 1
}

if { $actual_argc < [expr $current_arg + 1] } {
    puts "Error: you must supply a Bluesim model name"
    usage
}
set model_name [lindex $argv $current_arg]
incr current_arg 1

if { $actual_argc < [expr $current_arg + 1] } {
    puts "Error: you must specify the top module name"
    usage
}
set top_module [lindex $argv $current_arg]
incr current_arg 1

set script ""
set script_file ""
set run_cmd "run"
set vcd_arg ""
set arg_list [list]
set show_version 0

set stop_at_arg $actual_argc

while {$current_arg != $stop_at_arg} {
    set arg [lindex $argv $current_arg] 
    switch -glob -- $arg {
      "-c"      { incr current_arg 1
	          if {$current_arg == $stop_at_arg} then {
		      puts "Error: -c requires a command argument"
                      usage
                  } else {
		      append script [lindex $argv $current_arg]
		      append script ";"
		      incr current_arg 1
                  }
                }
      "-cc" { puts "Error: -cc is deprecated in favor of scriptable debug"
	      puts "See entry #031 in the KPnS document."
	      usage
            }
      "--creation_time" { incr current_arg 1
  	                  if {$current_arg == $stop_at_arg} then {
	 	 	      puts "Error: --creation_time requires a numeric argument"
                              usage
                          } else {
	                      set creation_time [lindex $argv $current_arg]
 		              incr current_arg 1
                          }
                        }
      "-f"      { incr current_arg 1
	          if {$current_arg == $stop_at_arg} then {
		      puts "Error: -f requires a script filename argument"
                      usage
                  } else {
		      set script_file [lindex $argv $current_arg]
		      incr current_arg 1
                  }
                } 
      "-h"      { incr current_arg 1
                  usage
                }
      "-help"   { incr current_arg 1
                  usage
                }
      "--help"  { incr current_arg 1
                  usage
                }
      "-m"      { incr current_arg 1
	          if {$current_arg == $stop_at_arg} then {
		      puts "Error: -m requires a cycle count argument"
                      usage
                  } else {
		      set run_cmd "step [lindex $argv $current_arg]"
		      incr current_arg 1
                  }
                } 
      "-r" { puts "Error: -r is deprecated in favor of scriptable debug"
	     puts "See entry #031 in the KPnS document."
	     usage
           }
      "-s" { puts "Error: -s is deprecated in favor of scriptable debug"
	     puts "See entry #031 in the KPnS document."
	     usage
           }
      "-ss" { puts "Error: -ss is deprecated in favor of scriptable debug"
	      puts "See entry #031 in the KPnS document."
	      usage
            }
      "--script_name" { incr current_arg 1
  	                if {$current_arg == $stop_at_arg} then {
	 	 	    puts "Error: --script_name requires a string argument"
                            usage
                        } else {
	                    set script_name [lindex $argv $current_arg]
 		            incr current_arg 1
                        }
                      }
      "-v"      { incr current_arg 1
                  set show_version 1
                }
      "-V"      { incr current_arg 1
	          if { ($current_arg == $stop_at_arg) ||
		       [string match "-*" [lindex $argv $current_arg]] ||
		       [string match "+*" [lindex $argv $current_arg]] } then {
		      set vcd_arg "on"
                  } else {			  
		      set vcd_arg [lindex $argv $current_arg]
		      incr current_arg 1
                  }
                } 
      "+*"      { incr current_arg 1
	          lappend arg_list [string range $arg 1 [string length $arg]]
                }
      "default" { puts "Error: invalid option '$arg'"
	          usage
                } 
    }
}

# always load the model first
sim load $model_name $top_module

# handle version request
if {$show_version != 0} {
    set vinfo [sim version]
    set name  [lindex $vinfo 0]
    set build [lindex $vinfo 1]
    set date  [clock format [lindex $vinfo 4]]
    puts "Model generated by bsc $name (build $build)"
    puts "Model built at $date"
    sim unload
    exit
}

# check creation time (if supplied)
if {$creation_time != 0} {
    set vinfo [sim version]
    set ctime [lindex $vinfo 2]
    if {$ctime != $creation_time} then {
	set model_time [clock format $ctime]
        set script_time [clock format $creation_time]
        puts "Error: model  creation time ($model_time) does not match"
        puts "       script creation time ($script_time)"
	if {$ctime > $creation_time} then {
            set name $model_name
        } else {
	    if {$script_name != ""} then {
		set name $script_name
            } else {
                set name [file tail $argv0]
            }
        }
	puts "       Has $name been overwritten?"
	sim unload
	exit 1
    }
}

# handle any plus-args
if {[llength $arg_list] != 0} {
    eval "sim arg $arg_list"
}
 
# set up VCD if requested
if {$vcd_arg != ""} {
    eval "sim vcd $vcd_arg"
}

# if there is no script supplied, just run the model in the requested mode
if {$script == "" && $script_file == ""} {
    eval "sim $run_cmd"
} else {
    # show all clock edges, even if they have no associated logic
    sim config interactive

    # if there is a script file, execute it
    if {$script_file != ""} {
        if {[catch {source $script_file} source_err] != 0} {
            puts "$source_err"
            sim unload
            exit 1
        }    
    }

    # if there is a script, execute it
    if {$script != ""} {
        eval $script
    }
}

# unload the model, just to be safe
sim unload

# we're done!
exit 0
