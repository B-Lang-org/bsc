namespace import ::Bluetcl::*

# Exercise wiretypemap on all the clock / reset variants we care about:
#   * Default input clock and reset of a synthesized module
#   * EXTRA argument clocks/resets (`Clock altClk, Reset altRst`
#     passed as module args)
#   * OUTPUT clock and reset (exposed via interface) -- with the
#     associated clock-gate output too
#   * Submodule clock connection wires (the wires that go from the
#     parent's clocks into a submodule's clock ports), including
#     gates -- e.g. mkGatedClockFromCC's primitive has CLK_IN/CLK_OUT
#     plus CLK_GATE_IN/CLK_GATE_OUT
#   * Cross-clock submodules: SyncFIFOToCC has source-side and
#     dest-side clocks (sCLK / dCLK) and a source-side reset (sRST).

flags set {-verilog}
module load mkClockTest

proc dumpMap { mod }  {
    puts "Command: module wiretypemap $mod"
    foreach entry [lsort [module wiretypemap $mod]] { puts "$entry" }
    puts "---------"
}

# Each synthesized module gets its own wiretypemap.
dumpMap mkClockOut
dumpMap mkArgClock
dumpMap mkClockTest

# Assertions on the interesting entries
set tmap_out [module wiretypemap mkClockOut]
set d_out [dict create]
foreach e $tmap_out { dict set d_out [lindex $e 0] [lindex $e 1] }

set tmap_arg [module wiretypemap mkArgClock]
set d_arg [dict create]
foreach e $tmap_arg { dict set d_arg [lindex $e 0] [lindex $e 1] }

set tmap_top [module wiretypemap mkClockTest]
set d_top [dict create]
foreach e $tmap_top { dict set d_top [lindex $e 0] [lindex $e 1] }

proc assertType { name dictName key expected } {
    upvar $dictName d
    if { [dict exists $d $key] } {
        set got [dict get $d $key]
        if { $got eq $expected } {
            puts "PASS: $name $key = $expected"
        } else {
            puts "FAIL: $name $key = '$got' (expected '$expected')"
        }
    } else {
        puts "FAIL: $name missing key $key"
    }
}

puts "=== assertions ==="
# mkClockOut: output clock + clock-gate + output reset
assertType mkClockOut d_out CLK_newClk      Clock
assertType mkClockOut d_out CLK_GATE_newClk Bool
assertType mkClockOut d_out RST_N_newRst    Reset

# mkArgClock: argument clock + argument reset are input clocks/resets
assertType mkArgClock d_arg CLK_altClk      Clock
assertType mkArgClock d_arg RST_N_altRst    Reset

# mkClockTest: submodule clock connection wires (Verilog and Bluesim forms)
assertType mkClockTest d_top "maker.CLK_newClk"      Clock
assertType mkClockTest d_top "maker.CLK_GATE_newClk" Bool
assertType mkClockTest d_top "maker.RST_N_newRst"    Reset
assertType mkClockTest d_top "taker.CLK_altClk"      Clock
assertType mkClockTest d_top "taker.RST_N_altRst"    Reset
