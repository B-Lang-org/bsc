package require Bluetcl
Bluetcl::flags set -verilog -p +
Bluetcl::module load mkArgumentMuxTypes
set pairs [Bluetcl::module wiretypecandidates mkArgumentMuxTypes]
set candidates [dict create {*}[concat {*}$pairs]]
set expected ArgumentMuxTypes::Flag
foreach name {first_value second_value {MUX_sink$put_1__VAL_1} {MUX_sink$put_1__VAL_2}} {
    if {![dict exists $candidates $name] || $expected ni [dict get $candidates $name]} {
        error "Missing Flag interpretation on $name"
    }
}
foreach name {EN_first EN_second CAN_FIRE_first WILL_FIRE_first CAN_FIRE_second WILL_FIRE_second} {
    if {[dict exists $candidates $name] && $expected in [dict get $candidates $name]} {
        error "Data interpretation leaked into control $name"
    }
}
Bluetcl::module clear
Bluetcl::module load mkArgumentMuxTypes
if {$pairs ne [Bluetcl::module wiretypecandidates mkArgumentMuxTypes]} {
    error "Candidate sets changed on .ba reload"
}
puts "PASS: emitted argument-mux inputs preserve the port type; controls and reload are correct"
