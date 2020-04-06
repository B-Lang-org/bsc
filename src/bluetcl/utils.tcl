package provide utils 1.0

namespace eval ::utils {

namespace export \
    filter \
    find \
    fst \
    head \
    isNumber \
    lastN \
    ldisplay \
    ldisplayf \
    makeBackupFile \
    map \
    map_ \
    nub \
    omap \
    omap_ \
    osortBy \
    scanOptions \
    snd \
    tail \
    zip \
    zipWith \
    zipWith_ \
    make_related_path \
    drop_dots_in_path \
    compare_lists \


############################################################
## Utility functions
# map function, partial evaluation allowed 
# EG:  map "file readable" {a b }
#  or  map "string compare f" { bar f f ff gg }
#  function name must be in global scope or qaulified
proc map { f as } {
    set ret {}
    foreach a $as {
        lappend ret [uplevel 1 $f [list $a]]
    }
    return $ret
}

# map without return
proc map_ { f as } {
    foreach a $as {
        uplevel 1 $f [list $a]
    }
}

# map over an object list
proc omap {options list} {
    set result [list]
    foreach item $list {
        lappend result [uplevel 1 $item $options ]
    }
    return $result
}
# map over an object list
proc omap_ {options list} {
    foreach item $list {
        uplevel 1 $item $options
    }
}

# object sort by
proc osortBy {smethod objs} {
    array set XX [list]
    foreach o $objs {
        set n [uplevel 1 $o $smethod]
        set XX($n) $o
    }
    set ret [list]
    foreach e [lsort [array names XX]] {
        lappend ret $XX($e)
    }
    return $ret
}


# join elements of 2 list into a list of pairs
proc zip { as bs } {
    set ret {}
    foreach a $as b $bs {
        lappend ret [list "$a" "$b"]
    }
    return $ret
}

proc unzip { zs } {
    set as {}
    set bs {}
    foreach z $zs {
        lappend as [fst $z]
        lappend bs [snd $z]
    }
    return [list $as $bs]
}

# return first element of list
proc fst { l } { return [lindex $l 0] }
proc snd { l } { return [lindex $l 1] }

# apply f to each element of as and bs
proc zipWith { f as bs } {
    set ret {}
    foreach a $as b $bs {
        lappend ret [uplevel 1 $f [list $a] [list $b]]
    }
    return $ret
}

proc zipWith_ { f as bs } {
    foreach a $as b $bs {
        [uplevel 1 $f [list $a] [list $b]]
    }
}

proc head   { l }     {  return [lindex $l 0] }
proc tail   { l }     {  return [lrange $l 1 end] }


# remove elements from list based on pred function
proc filter { pred as } {
    set ret {}
    foreach a $as {
        if { [uplevel 1 $pred [list $a]] } {
            lappend ret "$a"
        }
    }
    return $ret
}

# returns the first element in as which satisfies the pred function
proc find { pred as } {
    set ret {}
    foreach a $as {
        if { [uplevel 1 $pred [list $a]] } {
            set ret "$a"
            break ;
        }
    }
    return $ret
}

proc nub { l } {
    set ret [list]
    array set seen [list]
    foreach x $l {
        if {[info exists seen($x)]} {
            continue
        } 
        set seen($x) 1
        lappend ret $x
    }
    return $ret
}

# display each element of a list 
proc ldisplay {as} {
    foreach a $as { puts $a }
}

# display each element of a list where as are a list of format specifier
# ldisplayf [list %s %5d %d] [list foo 12 0]
proc ldisplayf {as bs} {
    set s ""
    foreach a $as b $bs {
        set s "$s[format $a $b]"
    }
    puts $s 
}


# returns true is n is a integer decimal number
proc isNumber { n } { if { [regexp -line {^\d+$} $n match] } { return 1 } else { return 0 } }

# strip off any type qualifier
proc unQualType { t } {
    regsub -all {[A-Za-z0-9_]+::} $t "" newt
    return $newt
}

# get just the qualified part if it exists.
proc getQual { t } {
    if { 1 == [regexp {([A-Z][A-z0-9_$]*)::([^: ]*)} $t all q i ] } {
        return $q
    }
    return "" 
}


# return the right most index else 0
proc getBitLSB { name } {
    if { 0 == [regexp {\[[0-9]*:([0-9]*)\]} $name m lsb] } {
        return 0
    }
    return $lsb
}

proc listToSet { setname l } {
    upvar $setname SET
    array set SET [list]; # Defines SET as an array to handle empty set conditions
    foreach elem $l {
        set SET($elem) 1
    }
}

proc setToList { setname } { 
    upvar $setname SET
    return [array names SET] 
}

proc commonPath { pa pb } {
    set ret [list]
    set sa [split $from /]
    set sb [split $to /]
    while { true } {
        if { $sf eq [list] } break;
        if { $st eq [list] } break;
        if { [lindex $sf 0] ne [lindex $st 0] } { break }
        lappend ret [lindex $sf 0]
        set sf [lrange $sf 1 end]
        set st [lrange $st 1 end]
    }
    return $ret
}

proc mkRelativePath { from to } {
    set sf [split $from /]
    set st [split $to /]
    while { true } {
        if { $sf eq [list] } break;
        if { $st eq [list] } break;
        if { [lindex $sf 0] ne [lindex $st 0] } { break }
        set sf [lrange $sf 1 end]
        set st [lrange $st 1 end]
    }
    set up [list]
    if { $sf eq [list] } {
        lappend up .
    } else {
        foreach x $sf {
            lappend up ".."
        }
    }
    join [concat $up $st] /
}

# process options for command.
# returns unaccounted for arguments, and array of key/value argument
# boolArgs are list of present/absent arguments
# optArgs are options which take an argument
proc scanOptions { boolArgs optArgs checkAll outArray argList } {
    upvar 1 $outArray ARG
    set result {}
    while { [llength $argList] != 0 } {
        set thisArg [lindex $argList 0]
        if { [lsearch -exact $boolArgs $thisArg] != -1 } {
            set ARG($thisArg) $thisArg
            set argList [lrange $argList 1 end]
        } elseif {[lsearch -exact $optArgs $thisArg] != -1 } {
            if { [llength $argList] == 1 } {
                error "Argument $thisArg expects an argument none found" 
            }
            set ARG($thisArg) [lindex $argList 1]
            set argList [lrange $argList 2 end]
        } elseif { $checkAll } {
            if { [regexp {^-} $thisArg] == 1 } {
                error "Unknown option: $thisArg"
            } else {
                lappend result $thisArg
                set argList [lrange $argList 1 end]
            }
        } else {            
            lappend result $thisArg
            set argList [lrange $argList 1 end]
        }
            
    }
    return $result
}

############################################################
proc help2 { args } {
    showArg $args
    if { [llength $args ] == 0 } {
        ldisplay [help [help]] 
    } else {
        ldisplay [help $args]
    }
}

proc donothing {} {
}

proc lastN {value n} {
    set length [string length $value]
    if {$length <= $n} {

	return $value

    } else {
	set delta [expr $length - $n]
	return [string range $value $delta end]

    }
}

proc makeBackupFile {filename} {
    if { ! [file exists $filename] } { return }
    if { [catch "exec cp --backup=t -f $filename $filename.bak"] } {
        puts stderr "Could create a backup of file $filename continuing without backup"
    }
}

############################################################
#procs to make relative path for a directory

proc make_related_path {file {path [pwd]}} {
    if {$file == ""} {
        return ""
    }
    eval set path $path
    if {[file pathtype $file] == "absolute"} {
        set ps [drop_dots_in_path [file split $path]]
        set fs [drop_dots_in_path [file split $file]]
        # drop common path
        set com [compare_lists $ps $fs]
        set ps [lrange $ps $com end]
        set fs [lrange $fs $com end]
        set r [list]
        for { set i 0} { $i < [llength $ps] } { incr i} {
            lappend r ".."
        }
        set r [eval file join [concat "." $r $fs]]
    } else {
        set fs [drop_dots_in_path [file split $file]]
        set r [eval file join $fs]
    }
    return $r
}

proc drop_dots_in_path {p} {
    set ret [list]
    foreach e $p {
        if {$e != "."} {
            lappend ret $e
        }
    }    
    if {[llength $ret] == 0} {
        lappend ret "."
    }
    return $ret
}

proc compare_lists {p f} {
    if {[expr [llength $p] < [llength $f]]} {
        set min  [llength $p]
    } else {
        set min [llength $f]
    }
    for {set i 0} {$i < $min} {incr i} {
        if {[string compare [lindex $p $i] [lindex $f $i]]} {
            break;
        }
    }
    return $i
}




}
# end namespace
