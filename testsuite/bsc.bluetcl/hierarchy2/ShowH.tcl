proc show_hierarchy { {k 0} { prefix ""} } {
    set D(Name) ""
    set D(Module) ""
    set D(Interface) ""
    set D(SynthPath) ""

    set children [Bluetcl::browseinst list $k]
    array set D [Bluetcl::browseinst detail $k]
    #parray D

    if { $D(Node) eq "Rule" } {
        set D(Module) Rule
        lappend D(SynthPath) $D(RuleName)
    }

    if { $D(Node) ne "ROOT" } {
        set fullpath  [join $D(BSVPath) "."]
        puts [format "%s%-15s\t -- %s %s\t%s " $prefix $D(Name) $D(Module) $D(Interface)  [join $D(SynthPath) "."]]
    }

    foreach child $children {
        set key [lindex $child 0]
        show_hierarchy  $key "$prefix    "
    }
}

set bafile  [lindex $argv 0]
set flags ""

eval Bluetcl::flags set -verilog $flags
Bluetcl::module load $bafile
show_hierarchy
