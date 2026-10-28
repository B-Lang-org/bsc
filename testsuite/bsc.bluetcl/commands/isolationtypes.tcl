namespace import ::Bluetcl::*
flags set {-verilog}
bpackage load IsolationTypes

proc checkIsolation {mod expected physical} {
    module load $mod
    set before [module wiretypecandidates $mod]
    set candidates [dict create]
    foreach row $before {
        lassign $row wire types
        dict set candidates $wire [lmap ty $types {string map {:: .} $ty}]
    }
    dict for {wire wanted} $expected {
        if {![dict exists $candidates $wire]} { error "$mod lost $wire" }
        set nominals {}
        foreach ty [dict get $candidates $wire] {
            if {[string match IsolationTypes.* $ty]} { lappend nominals $ty }
        }
        if {[lsort $nominals] ne [lsort $wanted]} {
            error "$mod $wire: expected $wanted, got $nominals"
        }
    }
    set fh [open $mod.v r]
    set rtl [read $fh]
    close $fh
    set declared {}
    foreach {declaration kind names} [regexp -all -inline -line \
        {^[ \t]*(output|wire|reg)[ \t]+(?:\[[^]]+\][ \t]+)?([^;]+);} $rtl] {
        foreach name [split $names ,] { lappend declared [string trim $name] }
    }
    foreach wire $physical {
        if {$wire ni $declared} { error "$mod $wire is not physically declared" }
    }
    module clear
    module load $mod
    if {[module wiretypecandidates $mod] ne $before} {
        error "$mod candidate sets changed after serialized reload"
    }
    return $candidates
}

set candidates [checkIsolation mkSplitIsolation {
    get_left IsolationTypes.Nibbles
    child$get_left IsolationTypes.Nibbles
    child.get_left IsolationTypes.Nibbles
    get_right {}
    child$get_right {}
    child.get_right {}
} {get_left get_right child$get_left child$get_right}]
if {[dict exists $candidates get]} {
    error "Split method aggregate acquired an unsplit candidate entry"
}
puts "PASS: split-result evidence stays on its selected physical leaf and excludes its sibling"
checkIsolation mkReceiverIsolation {
    first IsolationTypes.Nibbles
    a$get IsolationTypes.Nibbles
    a.get IsolationTypes.Nibbles
    second IsolationTypes.TaggedPayload
    b$get IsolationTypes.TaggedPayload
    b.get IsolationTypes.TaggedPayload
} {first second a$get b$get}
puts "PASS: distinct child receivers retain independent nominal candidate sets"
puts "PASS: isolation candidates survive .ba reload"
