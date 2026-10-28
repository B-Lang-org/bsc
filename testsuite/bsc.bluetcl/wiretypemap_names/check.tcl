package require Bluetcl
set mode [lindex $argv 0]
if {$mode eq "sim"} {
    Bluetcl::flags set -sim -p +
} else {
    Bluetcl::flags set -verilog -p +
}
proc declaredSignals {module} {
    set f [open "${module}.v"]
    set text [read $f]
    close $f
    set names {}
    foreach line [split $text "\n"] {
        if {[regexp {^ *\m(?:input|output|wire|reg)\M +(.*); *$} $line -> declaration]} {
            regsub -all {\[[^]]*\]} $declaration {} declaration
            foreach name [split $declaration ,] {
                lappend names [string trim $name]
            }
        }
    }
    return $names
}
foreach module {mkDeclaredByteSink mkDeclaredOnlyTypes} {
    Bluetcl::module load $module
    set pairs [Bluetcl::module wiretypecandidates $module]
    set candidates [dict create {*}[concat {*}$pairs]]
    set legacy [dict create {*}[concat {*}[Bluetcl::module wiretypemap $module]]]
    if {$module eq "mkDeclaredOnlyTypes"} {
        if {$mode eq "dollar"} {
            set expected {sink_get Bit#(8) sink_1put_payload Bit#(8) sink_EN_put Bool sink_put_payload Bit#(8)}
        } else {
            set expected {{sink$get} Bit#(8) {sink$put_payload} Bit#(8) {sink$EN_put} Bool sink_put_payload Bit#(8)}
        }
    } else {
        if {$mode eq "dollar"} {
            set expected {value_D_IN Bit#(8) value_EN Bool}
        } else {
            set expected {{value$D_IN} Bit#(8) {value$EN} Bool}
        }
    }
    if {$mode ne "sim" && $mode ne "staged"} {
        set physical [declaredSignals $module]
    }
    foreach {name type} $expected {
        if {![dict exists $candidates $name] || $type ni [dict get $candidates $name] ||
            ![dict exists $legacy $name] || [dict get $legacy $name] ne $type} {
            error "Missing declared type on $module.$name"
        }
        if {$mode ne "sim" && $mode ne "staged" && $name ni $physical} {
            error "Expected signal is absent from actual Verilog declarations: $module.$name"
        }
    }
    Bluetcl::module clear
    Bluetcl::module load $module
    if {$pairs ne [Bluetcl::module wiretypecandidates $module]} {
        error "Declared candidates changed after reload"
    }
    Bluetcl::module clear
    puts "PASS: $mode $module declared types match physical names and survive reload"
}
