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
proc testCmdT { args }  {
    puts "Command: $args"
    if { [catch $args err] } {
        puts "Caught error:  $err"
        set err [list]
    } else {
        asTree $err
    }
    puts "---------"
    return $err
}
proc asTree {t {ident ""} } {
    if {[string length $t] < 50} {
        puts "$ident $t"
    } elseif {[llength $t] == 1} {
        puts "$ident $t"
    } else {
        foreach e $t {
            asTree $e "    $ident"
        }
    }
}



puts [flags set {-verilog}]
puts [module load mkT]

puts {----------}

# display the ports information
testCmdT submodule ports mkT
puts {}
testCmdT submodule ports mkM

puts {----------}

# display the port types
testCmdT submodule porttypes mkT
puts {}
testCmdT submodule porttypes mkM

puts {----------}

# display the full information
# XXX this command is not used by anyone, so it's form and contents is
# XXX open to change
testCmdT submodule full mkT
puts {}
testCmdT submodule full mkM

puts {----------}
