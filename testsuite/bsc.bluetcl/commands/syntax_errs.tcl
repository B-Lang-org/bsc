namespace import ::Bluetcl::*

proc expect_err {cmd} {
    if {[catch $cmd var]} then {
	puts $var
    } else {
	puts "Expected error but got result: $var"
    }
}

puts {----------}

expect_err {nosuchcmd}

puts {----------}

expect_err {bpackage Test}

puts {----------}

puts [bpackage load Test]

puts {----------}

expect_err {type}

puts {----------}

expect_err {type Baz}

puts {----------}

puts [type constr Baz]

puts {----------}

expect_err {type full [type const Baz]}

puts {----------}

puts [type full [type constr Baz]]

puts {----------}

expect_err {type full Maybe Bool}

puts {----------}

expect_err {type full {Maybe Bool}}

puts {----------}

puts [type full Maybe#(Bool)]

puts {----------}

expect_err {type ful Maybe#(Bool)}

puts {----------}

expect_err {flags set}

puts {----------}

expect_err {browsepackage list zero}



