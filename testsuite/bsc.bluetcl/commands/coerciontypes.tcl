namespace import ::Bluetcl::*
flags set {-verilog}
bpackage load CoercionTypes

# Nominal qualification is the only syntax difference for these two types.
# Check the same assertions in both Bluetcl output modes.
proc normalizedType {ty} { return [string map {:: .} $ty] }

proc assertShared {mod wantedTypes} {
    module load $mod
    set byWire [dict create]
    foreach entry [module wiretypecandidates $mod] {
        lassign $entry wire tys
        set normalized {}
        foreach ty $tys { lappend normalized [normalizedType $ty] }
        dict set byWire $wire $normalized
    }
    set shared {}
    dict for {wire tys} $byWire {
        set matches 1
        foreach ty $wantedTypes {
            if {$ty ni $tys} { set matches 0 }
        }
        if {$matches} { lappend shared $wire }
    }
    if {[llength $shared] == 0} {
        error "FAIL $mod: no wire carries all interpretations $wantedTypes; map=$byWire"
    }
    set stream [open "$mod.v" r]
    set rtl [read $stream]
    close $stream
    set declared {}
    foreach {declaration kind names} [regexp -all -inline -line \
        {^[ \t]*(wire|reg)[ \t]+(?:\[[^]]+\][ \t]+)?([^;]+);} $rtl] {
        foreach name [split $names ,] { lappend declared [string trim $name] }
    }
    foreach wire $shared {
        if {$wire ni $declared} {
            error "FAIL $mod: inferred shared wire $wire is absent from emitted RTL"
        }
    }
    puts "PASS $mod: one emitted wire retains both nominal types"
    return $shared
}

proc assertSingle {mod wire wanted} {
    module load $mod
    set byWire [dict create]
    foreach entry [module wiretypemap $mod] {
        lassign $entry name ty
        dict set byWire $name [normalizedType $ty]
    }
    if {![dict exists $byWire $wire] || [dict get $byWire $wire] ne $wanted} {
        error "FAIL $mod: $wire should have unambiguous type $wanted; map=$byWire"
    }
    puts "PASS $mod: legacy map refines $wire to $wanted"
}

foreach mod {mkCseTypes mkRepackTypes} {
    set shared [assertShared $mod {CoercionTypes.Nibbles CoercionTypes.TaggedPayload}]
    set legacy [dict create]
    foreach entry [module wiretypemap $mod] {
        lassign $entry wire ty
        dict set legacy $wire [normalizedType $ty]
    }
    foreach wire $shared {
        # Backend aliasing also exposes both interpretations on the register
        # inputs. Their declared nominal types remain the legacy preference.
        if {$mod eq "mkCseTypes" && $wire in {{ns$D_IN} {ts$D_IN}}} {
            set declared [expr {$wire eq {ns$D_IN} ? "CoercionTypes.Nibbles" : "CoercionTypes.TaggedPayload"}]
            if {[dict get $legacy $wire] ne $declared} {
                error "FAIL $mod: legacy map lost declared type $declared on $wire"
            }
            continue
        }
        if {[dict exists $legacy $wire] && [dict get $legacy $wire] in {CoercionTypes.Nibbles CoercionTypes.TaggedPayload}} {
            error "FAIL $mod: legacy map arbitrarily chose a type for $wire"
        }
    }
    puts "PASS $mod: legacy map avoids choosing ambiguous internal types"
}
assertSingle mkCancellationType result CoercionTypes.Nibbles
assertSingle mkForcedPack result CoercionTypes.Nibbles
assertSingle mkForcedUnpack x CoercionTypes.Nibbles
assertSingle mkForcedUnpack {x$Q_OUT} CoercionTypes.Nibbles
assertSingle mkForcedUnpack x.Q_OUT CoercionTypes.Nibbles
assertSingle mkLeafInputType upper_bits CoercionTypes.Nibbles
assertSingle mkConstantType result CoercionTypes.Nibbles

module load mkRepackTypes
set before [module wiretypecandidates mkRepackTypes]
module clear
module load mkRepackTypes
if {[module wiretypecandidates mkRepackTypes] ne $before} {
    error "FAIL: source types changed after reloading the serialized module"
}
puts "PASS: candidate types survive clearing and reloading the .ba file"
