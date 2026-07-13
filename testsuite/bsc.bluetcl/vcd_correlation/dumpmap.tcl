namespace import ::Bluetcl::*

# Dump the wiretypemap of the module named in argv, one entry per
# line, for grep-based checks in run_correlation.sh.

flags set {-verilog}
module load [lindex $argv 0]
foreach e [module wiretypemap [lindex $argv 0]] {
    puts $e
}
