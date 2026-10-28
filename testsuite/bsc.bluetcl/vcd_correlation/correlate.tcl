namespace import ::Bluetcl::*

# The DejaGnu driver starts a fresh interpreter for each backend/map query.
# Maps are serialized as Tcl data, never as a script for the reader to eval.
switch [lindex $argv 0] {
    map {
        flags set {-verilog}
        set modName [lindex $argv 1]
        module load $modName
        foreach entry [module wiretypemap $modName] { puts $entry }
        exit
    }
    sim-maps {
        flags set {-sim}
        module load [lindex $argv 1]
        set maps [dict create]
        foreach {modName dutScope} [lindex $argv 2] {
            if {![dict exists $maps $modName]} {
                dict set maps $modName [module wiretypemap $modName]
            }
        }
        puts $maps
        exit
    }
    correlate {
        lassign [lrange $argv 1 end] topName modules veriVCD simVCD simTypeMap
        flags set {-verilog}
        module load $topName
    }
    default { error "expected map, sim-maps, or correlate mode" }
}

# Verify wiretypemap matches actual VCD wires for both backends. Emit
# stable sorted output, querying each module map and parsing each VCD once.

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
if { [file exists $veriVCD] } {
    set veriVars [parseVCD $veriVCD]
}
set simVars {}
if { [file exists $simVCD] } {
    set simVars [parseVCD $simVCD]
}

# The interpreter's loaded package is Verilog. Bluesim observations must
# come from its own build, before Verilog-only liveness/name filtering.
set simTypeMaps [dict create]
if {[llength $simVars] > 0} {
    set fh [open $simTypeMap r]
    set simTypeMaps [read $fh]
    close $fh
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
    set hitCount 0
    foreach v $vars {
        lassign $v scope name width
        if { $scope ne $dutScope && ![string match "${dutScope}.*" $scope] } {
            continue
        }
        foreach k [candidateKeys $scope $name $dutScope] {
            if { [dict exists $typeDict $k] } {
                # A VCD declaration is one hit even if the legacy map
                # contains several distinct type interpretations for it.
                incr hitCount
                foreach typ [dict get $typeDict $k] {
                    lappend hits [list $k $typ]
                }
                break
            }
        }
    }
    puts "=== $label ==="
    puts "  hits:    $hitCount"
    # NOTE: misses/ignored counts are intentionally omitted from the
    # baselined output. They reflect how many *other* wires the VCD
    # contains that we have no candidate for -- a number that varies
    # by iverilog version (iverilog 12 dumps more derived/intermediate
    # wires than 11) without changing anything about correlation
    # correctness. The matched-wires list (below) is the stable signal.
    puts "  matched wires (sorted):"
    foreach h [lsort -unique $hits] {
        puts "    [lindex $h 0] : [lindex $h 1]"
    }
    return $hitCount
}

# A module's map is shared by all of its instances. Cache it once,
# even when the same module appears at many different scopes.
set typeDictCache [dict create]
proc typeDictFor { modName backend } {
    global typeDictCache simTypeMaps
    set cacheKey [list $backend $modName]
    if { ![dict exists $typeDictCache $cacheKey] } {
        set typeDict [dict create]
        if {$backend eq "Bluesim"} {
            set entries [dict get $simTypeMaps $modName]
        } else {
            set entries [module wiretypemap $modName]
        }
        foreach entry $entries {
            dict lappend typeDict [lindex $entry 0] [lindex $entry 1]
        }
        dict for {name types} $typeDict {
            dict set typeDict $name [lsort -unique $types]
        }
        dict set typeDictCache $cacheKey $typeDict
    }
    return [dict get $typeDictCache $cacheKey]
}

set totalHits 0
foreach { modName dutScope } $modules {
    puts "##### module: $modName  @  $dutScope #####"
    if { [llength $veriVars] > 0 } {
        incr totalHits [correlate "Verilog" $veriVars $dutScope [typeDictFor $modName Verilog]]
    }
    if { [llength $simVars] > 0 } {
        incr totalHits [correlate "Bluesim" $simVars $dutScope [typeDictFor $modName Bluesim]]
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
