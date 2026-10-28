namespace import ::Bluetcl::*
flags set {-verilog}
bpackage load AliasCoercionTypes
module load mkAliasCoercionTypes
proc normalizeAliasType {ty} {
    set ty [string map {:: .} $ty]
    return [string map {{Bit#(8)} {Bit 8} {Prelude.Bit 8} {Bit 8}} $ty]
}
set before [module wiretypecandidates mkAliasCoercionTypes]
set candidates [dict create]
foreach row $before {
    lassign $row wire types
    dict set candidates $wire [lsort [lmap ty $types {normalizeAliasType $ty}]]
}
set legacy [dict create]
foreach row [module wiretypemap mkAliasCoercionTypes] {
    lassign $row wire ty
    dict set legacy $wire [normalizeAliasType $ty]
}
set fh [open mkAliasCoercionTypes.v r]
set rtl [read $fh]
close $fh
set wanted {{AliasCoercionTypes.Nibbles} {AliasCoercionTypes.TaggedPayload} {Bit 8}}
for {set i 0} {$i < 32} {incr i} {
    set wire aliases_${i}_value
    set actual [dict get $candidates $wire]
    if {[lsort $actual] ne [lsort $wanted]} {
        error "$wire lost or duplicated a candidate: $actual"
    }
    if {[dict get $legacy $wire] ne {Bit 8}} {
        error "$wire selected one of its ambiguous nominal interpretations"
    }
    if {![regexp [format {output\s+\[7\s*:\s*0\]\s+%s\s*;} $wire] $rtl]} {
        error "$wire is not an emitted eight-bit output"
    }
}
puts "PASS: 32 physical aliases retain both nominal interpretations and their declared legacy type"
module clear
module load mkAliasCoercionTypes
if {[module wiretypecandidates mkAliasCoercionTypes] ne $before} {
    error "Repeated alias candidates changed after serialized reload"
}
puts "PASS: repeated alias candidate sets survive .ba reload"
