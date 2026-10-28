namespace import ::Bluetcl::*
flags set {-verilog}
bpackage load ConditionalTypes

proc normalize {ty} { return [string map {:: .} $ty] }

proc loadCandidates {mod} {
    module clear
    module load $mod
    set candidates [dict create]
    foreach row [module wiretypecandidates $mod] {
        lassign $row name types
        dict set candidates $name [lmap ty $types {normalize $ty}]
    }
    return $candidates
}

proc assertNominals {mod candidates wire wanted} {
    if {![dict exists $candidates $wire]} {
        error "FAIL $mod: physical output $wire has no candidate entry"
    }
    set actual {}
    foreach ty [dict get $candidates $wire] {
        if {$ty in {ConditionalTypes.Nibbles ConditionalTypes.TaggedPayload}} {
            lappend actual $ty
        }
    }
    if {[lsort -unique $actual] ne [lsort -unique $wanted]} {
        error "FAIL $mod $wire: wanted nominal set $wanted, got $actual"
    }
    # Every asserted signal is a named interface port, and must occur in
    # the generated Verilog's declaration rather than only the candidate map.
    set stream [open "$mod.v" r]
    set rtl [read $stream]
    close $stream
    set pattern [format {\m(output|input|inout|wire|reg)\M\s+(\[[^]]+\]\s+)?%s\s*[,;]} $wire]
    if {![regexp $pattern $rtl]} {
        error "FAIL $mod: asserted signal $wire is absent from physical declarations"
    }
}

foreach mod {mkConditionalTypes mkConditionalCaseTypes} {
    set candidates [loadCandidates $mod]
    foreach wire {left middle right selected} {
        assertNominals $mod $candidates $wire {ConditionalTypes.Nibbles}
    }
    foreach wire {both predicate} { assertNominals $mod $candidates $wire {} }
    puts "PASS $mod: physical alternatives acquire the result layout; controls and wider concatenation do not"
}

set mod mkConditionalCseTypes
set candidates [loadCandidates $mod]
assertNominals $mod $candidates left {ConditionalTypes.Nibbles ConditionalTypes.TaggedPayload}
assertNominals $mod $candidates middle {ConditionalTypes.Nibbles}
assertNominals $mod $candidates right {ConditionalTypes.TaggedPayload}
assertNominals $mod $candidates selected {ConditionalTypes.Nibbles}
foreach wire {both predicate} { assertNominals $mod $candidates $wire {} }
puts "PASS $mod: shared physical branch unions two nominal sets; unrelated branches stay distinct"

set mod mkConditionalBoundaries
set candidates [loadCandidates $mod]
foreach wire {joined added sliced selected} {
    assertNominals $mod $candidates $wire {ConditionalTypes.Nibbles}
}
foreach wire {highInput lowInput arithmeticInput wideInput predicate} {
    assertNominals $mod $candidates $wire {}
}
puts "PASS $mod: typed alternatives do not transfer whole-value layouts to operation inputs"

set before [module wiretypecandidates $mod]
module clear
module load $mod
if {[module wiretypecandidates $mod] ne $before} {
    error "FAIL: conditional candidate sets changed after serialized module reload"
}
puts "PASS: conditional candidate sets survive .ba reload"
