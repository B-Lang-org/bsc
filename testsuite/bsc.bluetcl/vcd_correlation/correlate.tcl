namespace import ::Bluetcl::*

# Verify wiretypemap matches actual VCD wires for both Verilog and
# Bluesim backends. Emits stable, sorted output for test diffing.
#
# Driven via env vars so it can be re-invoked for multiple modules:
#   MOD_NAME         name of the synthesized module to correlate
#   TOP_NAME         top-level Verilog/Bluesim wrapper module (for `module load`)
#   VERI_VCD         path to Verilog VCD
#   VERI_DUT_SCOPE   VCD scope path of the dut inside the Verilog VCD
#   SIM_VCD          path to Bluesim VCD
#   SIM_DUT_SCOPE    VCD scope path of the dut inside the Bluesim VCD

flags set {-verilog}
module load $::env(TOP_NAME)
set tmap [module wiretypemap $::env(MOD_NAME)]

# Build dict from candidate name -> IType
set typeDict [dict create]
foreach entry $tmap {
    dict set typeDict [lindex $entry 0] [lindex $entry 1]
}

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
            lappend vars [list [join $scopeStack "."] \
                               [lindex $toks 4] \
                               [lindex $toks 2]]
        }
    }
    close $fh
    return $vars
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

# Correlate VCD vars with wiretypemap and print stable summary
proc correlate { label vcdPath dutScope typeDict } {
    set vars [parseVCD $vcdPath]
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

puts "##### module: $::env(MOD_NAME) #####"

set totalHits 0
if { [info exists ::env(VERI_VCD)] && [file exists $::env(VERI_VCD)] } {
    incr totalHits [correlate "Verilog" $::env(VERI_VCD) \
                              $::env(VERI_DUT_SCOPE) $typeDict]
}
if { [info exists ::env(SIM_VCD)] && [file exists $::env(SIM_VCD)] } {
    incr totalHits [correlate "Bluesim" $::env(SIM_VCD) \
                              $::env(SIM_DUT_SCOPE) $typeDict]
}

puts "=== summary ==="
puts "  wiretypemap entries: [llength $tmap]"
puts "  total VCD hits:      $totalHits"
if { $totalHits > 0 } {
    puts "RESULT: PASS"
} else {
    puts "RESULT: FAIL"
}
