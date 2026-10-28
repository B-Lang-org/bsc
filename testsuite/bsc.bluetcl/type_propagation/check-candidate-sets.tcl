namespace import ::Bluetcl::*
flags set {-verilog}
proc check {mod data controls wanted} {
    module clear
    module load $mod
    set rows [module wiretypecandidates $mod]
    set candidates [dict create]
    foreach row $rows {
        lassign $row name types
        dict set candidates $name [lmap ty $types {string map {:: .} $ty}]
    }
    set fd [open "$mod.v" r]; set rtl [read $fd]; close $fd
    foreach name $data {
        set pattern [format {\m(output|input|inout|wire|reg)\M\s+(\[[^]]+\]\s+)?%s\s*[,;]} $name]
        if {![regexp $pattern $rtl]} { error "Missing physical signal $mod.$name" }
        foreach ty $wanted {
            if {![dict exists $candidates $name] || $ty ni [dict get $candidates $name]} {
                error "Missing $ty on $mod.$name"
            }
        }
    }
    foreach name $controls {
        foreach ty $wanted {
            if {[dict exists $candidates $name] && $ty in [dict get $candidates $name]} {
                error "Data type $ty leaked to $mod.$name"
            }
        }
    }
    module clear; module load $mod
    if {$rows ne [module wiretypecandidates $mod]} { error "Reload changed $mod candidates" }
    puts "PASS $mod: physical result/sibling candidates, controls, and serialized reload"
}
bpackage load CandidateSetFlow
check mkArrayFlow {left middle right selected} {index load_i EN_load} {CandidateSetFlow.Nibbles CandidateSetFlow.Tagged}
check mkOutputFlow {left middle right selected} {predicate load_pp load_qq EN_load} {CandidateSetFlow.Flag CandidateSetFlow.OtherFlag}
bpackage load LateInlineTypes
foreach mod {mkLateCReg mkLateRWire} {
    check $mod {put_x put_y} {put_choose EN_put} {LateInlineTypes.Payload}
}
