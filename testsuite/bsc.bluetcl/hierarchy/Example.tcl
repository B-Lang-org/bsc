namespace import ::Bluetcl::*

proc testCmd { args }  {
    puts "Command: $args"
    if { [catch $args err] } {
        puts "Caught error:  $err"
        set err [list]
    } else {
        foreach e $err {
            puts "$e"
        }
    }
    puts "---------"
    return $err 
}
proc testCmdA { args }  {
    puts "Command: $args"
    if { [catch $args err] } {
        puts "Caught error:  $err"
        set err [list]
    } else {
        array set X $err
        parray X
    }
    puts "---------"
    return $err 
}


proc expandTree { k } {
    set children [testCmd browseinst list $k]
    testCmdA browseinst detail $k

    foreach child $children {
        set key [lindex $child 0]
        expandTree  $key
    }
    
}

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


# Load 
testCmd flags set -verilog
testCmd module load mkExample
show_hierarchy
expandTree 0

testCmd browseinst debug
