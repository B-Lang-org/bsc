namespace import ::Bluetcl::*

# Coverage test: `module porttypes` and `module wiretypemap` on a
# module whose sub-interface methods have SplitPorts-collapsed arguments
# (Inner and Header structs each collapse to one packed-bits port).
#
# Verifies that the wiretypemap reports the source-level types for the
# collapsed wires (not their bit-packed representations), and that the
# internal registers / FIFOF that carry those types are visible too.

flags set {-verilog}
module load mkSplitPortsTest

puts "=== porttypes ==="
foreach e [lsort [module porttypes mkSplitPortsTest]] { puts "  $e" }

puts "=== methods ==="
# `module methods` uses the same source-type walker as porttypes and
# would crash with `getIfcHierarhcy: not in map` on the same kind of
# SplitPorts mismatch. Smoke-test that it returns something here.
if { [catch [list module methods mkSplitPortsTest] err] } {
    puts "FAIL: caught error: $err"
} else {
    puts "OK ([llength $err] top-level fields)"
}

puts "=== wiretypemap ==="
foreach e [lsort [module wiretypemap mkSplitPortsTest]] { puts "  $e" }

set tmap [module wiretypemap mkSplitPortsTest]
set typeDict [dict create]
foreach entry $tmap { dict set typeDict [lindex $entry 0] [lindex $entry 1] }

puts "=== assertions ==="

proc assertType { dictName key expectPattern } {
    upvar $dictName d
    if { [dict exists $d $key] } {
        set t [dict get $d $key]
        if { [string match $expectPattern $t] } {
            puts "PASS: $key reports type ($t)"
        } else {
            puts "FAIL: $key type is '$t', expected to match '$expectPattern'"
        }
    } else {
        puts "FAIL: $key missing from wiretypemap"
    }
}

# Sub-interface method args carry their source-level struct types
assertType typeDict sub_put_1    "*Inner*"
assertType typeDict sub_putHdr_1 "*Header*"

# Sub-interface value methods present with their declared types
assertType typeDict sub_get   "*Inner*"
assertType typeDict sub_count "Bit#(16)"

# Internal-state submodule ports are visible with rich types
assertType typeDict last_inner.D_IN   "*Inner*"
assertType typeDict last_header.Q_OUT "*Header*"
assertType typeDict inflight.D_IN     "*Inner*"
