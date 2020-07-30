if { [llength $argv] != 1 } {
    puts "Usage: bluetcl -exec dump_poss.tcl <modulename>"
    exit 1
}

set modname [lindex $argv 0]

package require Bluetcl

Bluetcl::flags set "-verilog"
Bluetcl::module load $modname
foreach i [Bluetcl::module methodconditions $modname] {puts $i}

exit 0
