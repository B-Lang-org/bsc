namespace import ::Bluetcl::*

# FST twin of ../vcd_correlation/correlate.tcl: verify wiretypemap
# matches the wires recorded in FST dumps for both backends, and
# additionally confirm that each correlated module's TYPE is recorded
# in the FST itself.  FST scopes carry a "component" (module type)
# name that VCD has no place for; Bluesim and iverilog both record
# the defining module's name there.  Emits stable, sorted output for
# test diffing.
#
# Driven via env vars:
#   TOP_NAME     top-level wrapper module name (for `module load`)
#   VERI_HIER    path to the Verilog FST hierarchy dump (fstscopes)
#   SIM_HIER     path to the Bluesim FST hierarchy dump (fstscopes)
#   MOD_AT_LIST  TCL list of (module name, dut scope) pairs, as in
#                correlate.tcl

flags set {-verilog}
module load $::env(TOP_NAME)

# Parse an fstscopes hierarchy dump.  Returns {vars comps} where vars
# is a list of {scope_path name width} tuples and comps is a dict of
# scope_path -> component (module type; "-" when not recorded).
proc parseHier { path } {
    set fh [open $path r]
    set scopeStack {}
    set vars {}
    set comps [dict create]
    while {[gets $fh line] >= 0} {
        set toks [regexp -all -inline {\S+} [string trim $line]]
        if { [llength $toks] == 0 } continue
        set t0 [lindex $toks 0]
        if { $t0 eq "scope" } {
            # scope <name> <component|->
            lappend scopeStack [lindex $toks 1]
            dict set comps [join $scopeStack "."] [lindex $toks 2]
        } elseif { $t0 eq "upscope" } {
            set scopeStack [lrange $scopeStack 0 end-1]
        } elseif { $t0 eq "var" } {
            # var <width> <name> [range] [(alias)]
            # Strip a leading backslash (VCD-escaped identifier)
            set vname [lindex $toks 2]
            if { [string index $vname 0] eq "\\" } {
                set vname [string range $vname 1 end]
            }
            lappend vars [list [join $scopeStack "."] $vname [lindex $toks 1]]
        }
    }
    close $fh
    return [list $vars $comps]
}

# Cache hierarchies (we re-correlate per module)
set veriVars {}
set veriComps [dict create]
if { [info exists ::env(VERI_HIER)] && [file exists $::env(VERI_HIER)] } {
    lassign [parseHier $::env(VERI_HIER)] veriVars veriComps
}
set simVars {}
set simComps [dict create]
if { [info exists ::env(SIM_HIER)] && [file exists $::env(SIM_HIER)] } {
    lassign [parseHier $::env(SIM_HIER)] simVars simComps
}

# Compute candidate lookup keys for a given (scope, name) relative to dut
proc candidateKeys { scope name dutScope } {
    set keys [list $name]
    if { $scope ne $dutScope } {
        set relScope [string range $scope [expr {[string length $dutScope] + 1}] end]
        lappend keys "${relScope}.${name}"
        lappend keys "${relScope}\$${name}"
        if { $name eq "Q_OUT" } { lappend keys $relScope }
    }
    return $keys
}

# Correlate hierarchy vars (within the given scope) with the typeDict,
# print stable summary, return hit count
proc correlate { label vars dutScope typeDict } {
    set hits {}
    foreach v $vars {
        lassign $v scope name width
        if { $scope ne $dutScope && ![string match "${dutScope}.*" $scope] } {
            continue
        }
        foreach k [candidateKeys $scope $name $dutScope] {
            if { [dict exists $typeDict $k] } {
                lappend hits [list $k [dict get $typeDict $k]]
                break
            }
        }
    }
    set hitCount [llength $hits]
    puts "=== $label ==="
    puts "  hits:    $hitCount"
    puts "  matched wires (sorted):"
    foreach h [lsort -unique $hits] {
        puts "    [lindex $h 0] : [lindex $h 1]"
    }
    return $hitCount
}

# Confirm the module type recorded at a scope matches the expected
# module name; returns 1 when it does
proc confirmType { label comps modName dutScope } {
    if { [dict exists $comps $dutScope] } {
        set comp [dict get $comps $dutScope]
    } else {
        set comp "(no such scope)"
    }
    if { $comp eq $modName } {
        puts "  $label module type at $dutScope: $comp OK"
        return 1
    } else {
        puts "  $label module type at $dutScope: $comp (expected $modName) MISSING"
        return 0
    }
}

set totalHits 0
set typesOk 1
foreach { modName dutScope } $::env(MOD_AT_LIST) {
    set tmap [module wiretypemap $modName]
    set typeDict [dict create]
    foreach entry $tmap {
        dict set typeDict [lindex $entry 0] [lindex $entry 1]
    }
    puts "##### module: $modName  @  $dutScope #####"
    if { [llength $veriVars] > 0 } {
        incr totalHits [correlate "Verilog" $veriVars $dutScope $typeDict]
        if { ![confirmType "Verilog" $veriComps $modName $dutScope] } {
            set typesOk 0
        }
    }
    if { [llength $simVars] > 0 } {
        incr totalHits [correlate "Bluesim" $simVars $dutScope $typeDict]
        if { ![confirmType "Bluesim" $simComps $modName $dutScope] } {
            set typesOk 0
        }
    }
    puts ""
}

puts "=== summary ==="
puts "  total FST hits across all (module, scope) pairs: $totalHits"
puts "  module types recorded for all (module, scope) pairs: [expr {$typesOk ? {yes} : {NO}}]"
if { $totalHits > 0 && $typesOk } {
    puts "RESULT: PASS"
} else {
    puts "RESULT: FAIL"
}
