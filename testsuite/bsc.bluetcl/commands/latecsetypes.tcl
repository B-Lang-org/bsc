namespace import ::Bluetcl::*
flags set {-verilog}
bpackage load LateCseTypes
module load mkLateCseTypes
set before [module wiretypecandidates mkLateCseTypes]
set candidates [dict create]
foreach entry $before {
    lassign $entry wire types
    dict set candidates $wire [string map {:: .} $types]
}
set legacy [dict create]
foreach entry [module wiretypemap mkLateCseTypes] {
    lassign $entry wire type
    dict set legacy $wire $type
}
set stream [open mkLateCseTypes.v r]
set rtl [read $stream]
close $stream
foreach wire {simpleResult expandedResult} {
    foreach wanted {LateCseTypes.SimpleInterpretation LateCseTypes.ExpandedInterpretation} {
        if {$wanted ni [dict get $candidates $wire]} {
            error "Late equivalent wire $wire lost candidate $wanted: $candidates"
        }
    }
    if {![regexp "assign $wire = " $rtl]} {
        error "Observed wire $wire is not an emitted output"
    }
    if {[string match *Interpretation* [dict get $legacy $wire]]} {
        error "Legacy map selected an ambiguous nominal type for $wire"
    }
}
module clear
module load mkLateCseTypes
if {[module wiretypecandidates mkLateCseTypes] ne $before} {
    error "Final physical candidates changed after serialized reload"
}
puts "PASS: backend-equivalent physical outputs retain both source types after reload"
