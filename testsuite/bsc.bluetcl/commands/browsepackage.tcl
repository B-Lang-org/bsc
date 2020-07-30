namespace import ::Bluetcl::*

proc bluetcl_test { args } {
    puts "Command: $args"
    if { [catch $args err] } {
        puts "Caught error:  $err"
    } else {
        puts "$err"
    }
    puts "---------"
}

proc bluetcl_testL { args }  {
    puts "Command: $args"
    if { [catch $args err] } {
        puts "Caught error:  $err"
    } else {
        foreach e $err {
            puts "$e"
        }
    }
    puts "---------"
}

proc bluetcl_testLNodeL { args }  {
    puts "Command: $args"
    if { [catch $args err] } {
        puts "Caught error:  $err"
    } else {
        foreach nlist $err {
            set new_nlist {}
            foreach node $nlist {
                if { [llength $node] == 3 } {
                    if { [regexp {^[0-9]+$} [lindex $node 0]] } {
                        set node [lreplace $node 0 0 {NNN}]
                    }
                }
                lappend new_nlist $node
            }
            puts "$new_nlist"
        }
    }
    puts "---------"
}

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
    set children [testCmd browsepackage list $k]
    bluetcl_testL browsepackage detail $k

    foreach child $children {
        set key [lindex $child 0]
        expandTree  $key
    }
}




puts [bpackage load Test]

puts {----------}

testCmd browsepackage list 0
testCmd browsepackage list 1
testCmd browsepackage list 2


puts {----------}

##  Expand the current directory...
expandTree 1

# this causes an error
puts [browsepackage detail 0]


# test "nodekind" subcommand
# this causes an internal error
#puts [browsepackage nodekind 0]

puts {----------}

# test refresh (used when the loaded packages has changed)
puts [bpackage load RegFile]
puts [browsepackage refresh]
# redisplay the root
bluetcl_testL browsepackage list 0

puts {----------}

bluetcl_testLNodeL browsepackage search mkReg
bluetcl_testLNodeL browsepackage search mkRegU
bluetcl_testLNodeL browsepackage search Reg.*Load.*
