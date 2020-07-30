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


puts [flags set {-verilog}]
puts [module load mkT]

puts {----------}

# display the port types
testCmd module porttypes mkT
puts {}
testCmd module porttypes mkM
puts {}
testCmd module porttypes mkIfcWithVec

puts {----------}

# display the full port info
puts "module ports mkT"
testCmd module ports mkT
puts {}
puts "module ports mkM"
testCmd module ports mkM
puts {}
puts "module ports mkIfcWithVec"
testCmd module ports mkIfcWithVec

puts {----------}

# XXX display other subcommands?
