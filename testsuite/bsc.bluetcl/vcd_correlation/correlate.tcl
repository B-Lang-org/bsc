namespace import ::Bluetcl::*

# Verify wiretypemap matches actual VCD wires for both Verilog and
# Bluesim backends. Emits stable, sorted output for test diffing.
#
# Driven via env vars:
#   TOP_NAME     top-level wrapper module name (for `module load`)
#   VERI_VCD     path to Verilog VCD
#   SIM_VCD      path to Bluesim VCD
#   MOD_AT_LIST  TCL list of (module name, dut scope) pairs to correlate.
#                The same scope is used for both Verilog and Bluesim
#                (sub-instance scopes are named identically in both
#                backends). Multiple instances of the same module at
#                different scopes are listed as separate pairs -- one
#                wiretypemap covers all of them, which is the value of
#                the per-.ba map design.
#
# For each (module, scope) pair, runs `module wiretypemap <module>`,
# parses each VCD, and reports matched wires within that scope only.

flags set {-verilog}
module load $::env(TOP_NAME)

# Parse VCD: returns list of {scope_path name width} tuples
proc parseVCD { path } {
    set fh [open $path r]
    set scopeStack {}
    set vars {}
    while {[gets $fh line] >= 0} {
        set toks [regexp -all -inline {\S+} [string trim $line]]
        if { [llength $toks] == 0 } continue
        set t0 [lindex $toks 0]
        if { $t0 eq "\$scope" } {
            lappend scopeStack [lindex $toks 2]
        } elseif { $t0 eq "\$upscope" } {
            set scopeStack [lrange $scopeStack 0 end-1]
        } elseif { $t0 eq "\$var" } {
            # VCD format: $var <type> <width> <id> <name> [range] $end
            # If <name> starts with `\` it's a VCD-escaped identifier;
            # strip the leading backslash to match wiretypemap keys.
            set vname [lindex $toks 4]
            if { [string index $vname 0] eq "\\" } {
                set vname [string range $vname 1 end]
            }
            lappend vars [list [join $scopeStack "."] $vname [lindex $toks 2]]
        }
    }
    close $fh
    return $vars
}

# Cache VCDs (we re-correlate per module)
set veriVars {}
if { [info exists ::env(VERI_VCD)] && [file exists $::env(VERI_VCD)] } {
    set veriVars [parseVCD $::env(VERI_VCD)]
}
set simVars {}
if { [info exists ::env(SIM_VCD)] && [file exists $::env(SIM_VCD)] } {
    set simVars [parseVCD $::env(SIM_VCD)]
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

# Correlate VCD vars (within the given scope) with the typeDict,
# print stable summary, return hit count
proc correlate { label vars dutScope typeDict } {
    set hits {}
    set misses 0
    set ignored 0
    foreach v $vars {
        lassign $v scope name width
        if { $scope ne $dutScope && ![string match "${dutScope}.*" $scope] } {
            incr ignored
            continue
        }
        set matched 0
        foreach k [candidateKeys $scope $name $dutScope] {
            if { [dict exists $typeDict $k] } {
                lappend hits [list $k [dict get $typeDict $k]]
                set matched 1
                break
            }
        }
        if { !$matched } { incr misses }
    }
    set hitCount [llength $hits]
    puts "=== $label ==="
    puts "  hits:    $hitCount"
    puts "  misses:  $misses"
    puts "  ignored: $ignored"
    puts "  matched wires (sorted):"
    foreach h [lsort -unique $hits] {
        puts "    [lindex $h 0] : [lindex $h 1]"
    }
    return $hitCount
}

set totalHits 0
foreach { modName dutScope } $::env(MOD_AT_LIST) {
    set tmap [module wiretypemap $modName]
    set typeDict [dict create]
    foreach entry $tmap {
        dict set typeDict [lindex $entry 0] [lindex $entry 1]
    }
    puts "##### module: $modName  @  $dutScope #####"
    if { [llength $veriVars] > 0 } {
        incr totalHits [correlate "Verilog" $veriVars $dutScope $typeDict]
    }
    if { [llength $simVars] > 0 } {
        incr totalHits [correlate "Bluesim" $simVars $dutScope $typeDict]
    }
    puts ""
}

puts "=== summary ==="
puts "  total VCD hits across all (module, scope) pairs: $totalHits"
if { $totalHits > 0 } {
    puts "RESULT: PASS"
} else {
    puts "RESULT: FAIL"
}
