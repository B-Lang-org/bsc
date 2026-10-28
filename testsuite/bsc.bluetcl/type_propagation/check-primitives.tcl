namespace import ::Bluetcl::*
flags set {-verilog}
bpackage load PrimitiveTypes
proc loadCandidates {mod} {
    module clear; module load $mod
    set rows [module wiretypecandidates $mod]
    set candidates [dict create]
    foreach row $rows { lassign $row name types; dict set candidates $name $types }
    set stream [open "$mod.v" r]; set rtl [read $stream]; close $stream
    module clear; module load $mod
    if {$rows ne [module wiretypecandidates $mod]} { error "Reload changed $mod" }
    return [list $candidates $rtl]
}
proc requireType {mod candidates rtl wire wanted} {
    set pattern [format {\m(output|input|wire|reg)\M\s+(\[[^]]+\]\s+)?%s\s*[,;]} $wire]
    if {![regexp $pattern $rtl]} {error "Missing physical declaration $mod.$wire"}
    if {![dict exists $candidates $wire] || $wanted ni [dict get $candidates $wire]} {
        error "Missing $wanted on $mod.$wire"
    }
}
proc rejectType {mod candidates wire unwanted} {
    if {[dict exists $candidates $wire] && $unwanted in [dict get $candidates $wire]} {
        error "Unexpected $unwanted on $mod.$wire"
    }
}
foreach {mod wanted} {mkUIntPlain UInt#(16) mkIntPlain Int#(16) mkUIntObserved UInt#(16) mkIntObserved Int#(16)} {
    lassign [loadCandidates $mod] candidates rtl
    if {![regexp {assign\s+(\S+)\s*=\s*result_a\s*\+\s*result_b\s*;} $rtl _ sum]} {
        error "Missing physical sum helper in $mod"
    }
    requireType $mod $candidates $rtl $sum $wanted
    puts "PASS $mod: physical intermediate $sum has $wanted"
}
set mod mkNumericUnion
lassign [loadCandidates $mod] candidates rtl
if {![regexp {assign\s+(\S+)\s*=\s*result_a\s*\+\s*result_b\s*;} $rtl _ sum]} {error "Missing shared sum"}
foreach ty {Int#(16) UInt#(16)} {requireType $mod $candidates $rtl $sum $ty}
puts "PASS: a CSE-shared sum retains both numeric interpretations"
set mod mkPrimitiveBool
lassign [loadCandidates $mod] candidates rtl
if {![regexp {assign\s+(\S+)\s*=\s*choose_a\s*==\s*choose_b\s*&&} $rtl _ condition]} {
    error "Missing physical Boolean predicate helper"
}
requireType $mod $candidates $rtl $condition Bool
puts "PASS: physical logical predicate has Bool without explicit pack"
foreach {mod wanted} {mkRawWideProduct Bit#(32) mkUnsignedWideProduct UInt#(32)} {
    lassign [loadCandidates $mod] candidates rtl
    requireType $mod $candidates $rtl result $wanted
    rejectType $mod $candidates result Int#(32)
}
puts "PASS: full-width raw multiplication never invents a signed result"
set mod mkPrimitiveRawBit
lassign [loadCandidates $mod] candidates rtl
requireType $mod $candidates $rtl result Bit#(1)
foreach ty {Bool Int#(1) UInt#(1)} {rejectType $mod $candidates result $ty}
set mod mkPrimitiveRawAdd
lassign [loadCandidates $mod] candidates rtl
requireType $mod $candidates $rtl result Bit#(16)
foreach ty {Int#(16) UInt#(16)} {rejectType $mod $candidates result $ty}
set mod mkPrimitiveShift
lassign [loadCandidates $mod] candidates rtl
requireType $mod $candidates $rtl result Int#(16)
requireType $mod $candidates $rtl result_amount Bit#(4)
foreach ty {Int#(4) UInt#(4)} {rejectType $mod $candidates result_amount $ty}
puts "PASS: raw-bit controls and shift amounts remain separate; all modules reload"
