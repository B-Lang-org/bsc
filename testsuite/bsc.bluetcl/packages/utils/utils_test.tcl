package require utils

proc testCmd { args }  {
    global errorInfo
    puts "Command: $args"
    if { [catch [list uplevel 1 $args] err] } {
        puts "Caught error:  $err"
        puts $errorInfo
        set err [list]
    } else {
        foreach e $err {
            puts "$e"
        }
    }
    puts "---------"
    return $err
}


set open XXX

proc globalspace { x y } {
    puts "GS: $x $y"
}

proc procargs {args} {
    return [join $args "__"]
}

set gz "abcd"
set gy "edgr"
set gx "with space"
set gw {with$dollar}

set gl [list]
lappend gl $gz $gy $gx $gw


namespace eval foo {
    proc tester {} {
        set z "abcd"
        set y "edgr"
        set x "with space"
        set w {with$dollar}

        set l [list]
        lappend l $z $y $x $w

        proc two { a b c } {
            puts "$a $b $c"
            return  [join [list $a $b $c] "./."]
        }


        testCmd utils::map_ puts $l
        testCmd utils::map_ "puts stderr" $l

        testCmd utils::map "globalspace $z" $l
        testCmd utils::map "globalspace $y" $l
        testCmd utils::map "globalspace $x" $l
        testCmd utils::map "globalspace {$x}" $l
        testCmd utils::map "globalspace $w" $l
        testCmd utils::map "globalspace {$w}" $l

        puts "-----------   testing with 2 args"
        testCmd utils::map "two $z $y" $l
        testCmd utils::map "two {$z} {$y}" $l
        puts "-----------   testing with space"
        testCmd utils::map "two $x $y" $l
        testCmd utils::map "two {$x} $y" $l
        puts "-----------   testing with dollar"
        testCmd utils::map "two $w $y" $l
        testCmd utils::map "two {$w} $y" $l
    }
}


# Test in namespace context
foo::tester

testCmd  utils::map "procargs $gz" $gl
testCmd  utils::map "procargs $gz $gy $gw"  $gl
testCmd  utils::map "procargs $gz $gy {$gw}"  $gl
testCmd  utils::map "procargs $gz $gy $gx" $gl
testCmd  utils::map "procargs $gz $gy {$gx}" $gl

# two not in name space
testCmd utils::map "two zz yy" [list a b c d]

testCmd utils::filter "string match $gz" $gl
testCmd utils::filter "string match $gy" $gl
testCmd utils::filter "string match $gx" $gl
testCmd utils::filter "string match $gw" $gl
testCmd utils::filter "string match {$gx}" $gl
testCmd utils::filter "string match {$gw}" $gl
testCmd utils::filter "string match *d*" $gl
