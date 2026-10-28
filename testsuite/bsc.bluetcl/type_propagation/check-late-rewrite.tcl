namespace import ::Bluetcl::*
flags set {-verilog}
bpackage load LateRewriteTypes

foreach {mod stem expected} {
    mkSignedShiftSlice result_x_SRL_result_n_OR_INV_0xFF_SRL_result_n_ETC {Int#(8) LateRewriteTypes::Payload}
    mkSignedShiftConstSlice SEXT_result_x_BITS_7_TO_2 {Int#(8) LateRewriteTypes::Payload}
    mkUnsignedShiftSlice result_x_SRL_result_n {LateRewriteTypes::Payload}
    mkMuxSlice IF_result_p_THEN_result_x_ELSE_result_y {LateRewriteTypes::Payload}
    mkNegSlice NEG_result_x {LateRewriteTypes::Payload}
} {
    set stream [open "$mod.v" r]
    set rtl [read $stream]
    close $stream
    set wires {}
    foreach line [split $rtl "\n"] {
        if {[regexp {^\s*wire\s+\[7\s*:\s*0\]\s+([A-Za-z0-9_$]+)\s*;} $line -> wire] &&
            [string match "${stem}__q*" $wire]} {lappend wires $wire}
    }
    if {[llength $wires] != 1} {error "FAIL $mod: expected one physical full-width helper, got $wires"}
    set wire [lindex $wires 0]
    module clear
    module load $mod
    set before [module wiretypecandidates $mod]
    set found {}
    foreach row $before {
        lassign $row name types
        if {$name eq $wire} {set found $types}
    }
    foreach ty $expected {
        if {$ty ni $found} {error "FAIL $mod $wire: missing $ty in $found"}
    }
    module clear
    module load $mod
    if {[module wiretypecandidates $mod] ne $before} {error "FAIL $mod: candidates changed on reload"}
    puts "PASS $mod: physical helper retains $expected through .ba reload"
}
