
package provide types 1.0
package require Bluetcl
package require utils


namespace eval ::types {

# export only a few items from the package
namespace export \
    getNonPolyType \
    showTypeSize \
    getWidth \
    getLength \
    getMembers \
    processFullType \
    import_package \

}

namespace eval ::types {

    namespace import ::utils::*

# wrapper around import
proc import_package { force packs } {
    if { $force } {
        set p [eval Bluetcl::bpackage load $packs]
    } else {
        set loaded [Bluetcl::bpackage list]
        utils::listToSet Loaded $loaded
        set packsToLoad [list]
        foreach pack $packs {
            if { $pack == "" } { continue }
            if { ! [info exists Loaded($pack)] } {
                set loaded [Bluetcl::bpackage load $pack]
                utils::listToSet Loaded $loaded
            }
        }
        set p [Bluetcl::bpackage list]
    }
    return $p
}

# extract the set of types from a package, and return the
# list of type constructors
proc getTypes { package } {
    set tsfull [Bluetcl::bpackage types $package]
    set ts [filter ::types::typeIsNotKeyword $tsfull]
    set cs [map "Bluetcl::type constr" $ts]
    return $cs
}

proc getNonPolyType { pack } {
    set tsfull [lsort [Bluetcl::bpackage types $pack]]
    set ts [filter ::types::typeIsNotKeyword $tsfull]
    set cs [map "Bluetcl::type constr" $ts]
    set pairs [zip $ts $cs]

    proc equalElems { p } { return [string equal [lindex $p 0] [lindex $p 1] ]}

    set es [filter types::equalElems $pairs]
    set final [map fst $es]
    return $final
}

# XXX These are types from the prelude which are not parsed as types
proc typeIsNotKeyword { t } {
    set keywords [list Action ActionValue  "List°Cons" "->"]

    foreach k $keywords {
        if { $k == $t } {
            return false;
        }
    }
    return true;
}

# display the list of types from a package
proc showTypes { package } {
    ldisplay [getTypes $package]
}


#  recursively travserve a struct building the name size bit fields
proc showTypeSize { type } {
    set res [createBitIndexes $type]
    proc dis { ts } {
        ldisplayf [list %-25s "\t%25s" "\t%4d" " \[ %3d:" "%-3d \]"]  $ts
    }
    map_ ::types::dis $res
}

# for the field name and field type at bit position
proc showTypeField { type position } {
    set pos [lookupBitType $type $position]
    if { $pos == {} } {
        puts stderr "$type does not have a field at $position"
    } else {
        set field [fst $pos]
        set st [snd $pos]

        set upper [lindex $pos 3]
        set lower [lindex $pos 4]
        puts "$type at \[$upper:$lower\] is field \"$field\" with sub-type $st"
    }
}


# lookup the field name and field type at bit position
proc lookupBitType { type position } {
    set fields [createBitIndexes $type]

    proc lookupBitHelper { position elem } {
        return  [expr ($position >= [lindex $elem 4]) && ($position <=   [lindex $elem 3])  ]
    }
    set res [utils::find "::types::lookupBitHelper $position" $fields]
}

# returns a list of tuples {fieldName type size upperindex lowerindex}
proc createBitIndexes { type } {
    set ft [fullTypeNoAlias $type]
    set w [getWidth $ft]
    if { $w == {} } {
	puts stderr "type does not have a size: $type [fst $ft]"
        set res [list]
    } else {
	set bas [processFullType "." $ft ]
	set res [processAddIndex $bas]
    }
    return $res
}


proc processAddIndex { ts } {
    set pos 0
    set res {}
    for {set i [expr [llength $ts] - 1]} { $i >= 0 } { incr i -1} {
        set elem [lindex $ts $i]
        set w [lindex $elem 2]
        set lower $pos
        set upper [expr $pos + $w - 1]
        set pos [expr $pos + $w]
        set res [linsert $res 0 [concat $elem $upper $lower]]
    }
    return $res
}
# returns list of parts of the type { {name type size} * }
# note that name has laready been generated with fullType
# ft is the name appended to returned name
# This recurses down the structure
proc processFullType {name ft} {
    set key [lindex $ft 0]
    #puts "procfulltype $name $ft"
    switch -exact $key {
        "Primary" { return [processPrimary $name $ft] }
        "Alias"   { return [processAlias $name $ft] }
        "Struct"  { return [processStruct $name $ft]}
        "Enum"    { return [processEnum $name $ft]}
        "TaggedUnion"    { return [processTaggedUnion $name $ft]}
        "Vector"  { return [processVector $name $ft]}
        # "Interface"
        default { return [list {"." Unknown x}] }
        }
}

proc processVector { name ft } {
    set len [getLength $ft]
    if { $len != "" } {
        set etype [fullTypeWrap [getElem $ft]]
        set res {}
        for {set i [expr $len - 1]} {$i >= 0} { incr i -1 } {
            set newName [format "%s\[%d\]" $name $i]
            #puts "name is $newName"
            set res [concat $res [processFullType $newName $etype]]
        }
        return $res
    } else {
        return [list {$name Vector x}]
    }
}

proc processTaggedUnion { name ft } {
    set w [getWidth $ft]
    set t [lindex $ft 1]
    return [list [list $name $t $w]]
}
proc processEnum { name ft } {
    set w [getWidth $ft]
    set t [lindex $ft 1]
    return [list [list $name $t $w]]
}

proc processAlias { name ft } {
    set atype [lindex $ft 2]
    return [processFullType $name [fullTypeWrap $atype]]
}
proc processPrimary { name ft } {
    return [list [list $name [lindex $ft 1] [getWidth $ft]]]
}

proc processStruct { name ft } {
    set members [getMembers $ft]
    set res {}
    foreach mem $members {
        set n [lindex $mem 1]
        set t [lindex $mem 0]
        if { $name == "." } {
            set newName [join [list $name $n] "" ]
        } else {
            set newName [join [list $name $n] "."]
        }
        set ft1 [fullTypeWrap $t]
        set res [concat $res [processFullType $newName $ft1]]
    }
    return $res
}

proc fullTypeWrap { t } {
    return [Bluetcl::type full $t]
}
proc fullTypeNoAlias { t } {
    set ft [fullTypeWrap $t]
    # unwind aliases
    while { [lindex $ft 0] == "Alias"} {
        set tx [lindex $ft 2]
        set ft [fullTypeWrap $tx]
    }
    return $ft
}

## get the width field from type full command
proc getWidth {ft} {
    foreach elem $ft {
        if {[lindex $elem 0] == "width" } {
            return [lindex $elem 1]
        }
    }
    return ""
}

proc getLength {ft} {
    foreach elem $ft {
        if {[lindex $elem 0] == "length" } {
            return [lindex $elem 1]
        }
    }
    return ""
}

proc getElem {ft} {
    foreach elem $ft {
        if {[lindex $elem 0] == "elem" } {
            return [lindex $elem 1]
        }
    }
    return ""
}

proc getMembers {ft} {
    foreach elem $ft {
        if {[lindex $elem 0] == "members" } {
            return [lindex $elem 1]
        }
    }
    return ""
}

# return true is the type is an enum
proc isEnum {type} {
    set ft [fullTypeWrap $name]
    set key [lindex $ft 0]
    return [string equal $key "Enum"]
}


# close namespace
}

## Documented interface for the Types package and namespace
namespace eval Types {
    namespace export \
        import_package \
        show_type_size \
        show_type_field

    proc import_package { packname } {
        types::import_package false $packname
    }

    proc show_type_size { type } {
        types::showTypeSize $type
    }

    proc show_type_field { type position } {
        types::showTypeField $type $position
    }

    proc get_width { type } {
        set ft [types::fullTypeNoAlias $type]
        return [types::getWidth $ft]
    }
}

package provide Types 1.0
