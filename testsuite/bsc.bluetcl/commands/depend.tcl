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

testCmd depend make Test.bsv

testCmd depend make MissingFile.bsv

testCmd depend make Dep1.bsv

flags set -p subdir:+

testCmd depend make Dep1.bsv

# removed the subdir command
flags set -p .:subdir:%/Libraries
testCmd flags set -bdir BOUTDIR
testCmd depend make Dep1.bsv

## the recomp sub command
testCmd depend recomp MissingFile.bsv
testCmd depend recomp Test.bsv
testCmd depend recomp Dep1.bsv


## the recomp sub command
testCmd depend file MissingFile.bsv
testCmd depend file Test.bsv
testCmd depend file Dep1.bsv
