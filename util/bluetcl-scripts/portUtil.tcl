# notes: 
#  lappend -> add hierarchy when recursing
#  concat  -> flatten out lists
#  maintain list level needs this:
#    set res [concat [list] [list $l1] [list $l2]]


package provide portUtil 1.0

package require Bluetcl
package require utils
package require types


namespace eval ::portUtil {

    namespace export createExpandedVerilogWrapper
    namespace export mergePortAndTypeInfo
    namespace export getClockRstParamPins
    namespace export createExpandedPins
    namespace export getAllPortInfo
    namespace export printMethodTypes
    namespace export listMethodInfo
    namespace export version


    # import all the functions from the utils package
    namespace import ::utils::map_
    namespace import ::utils::map
    namespace import ::utils::tail
    namespace import ::utils::isNumber
    namespace import ::utils::zipWith
    namespace import ::utils::ldisplay
    namespace import ::utils::filter

    # imports from type package
    namespace import ::types::getMembers
    namespace import ::types::getLength
    namespace import ::types::getWidth

    namespace import ::Bluetcl::*

    proc version {} { 
        set major_version 2
        set minor_version 0
        return "$major_version.$minor_version"
    }

    variable debug 0
    variable dbgspaces ""
    variable dbgproc [list]
    variable ports [list]
    variable types [list]
    variable verilogPins [list]

    # get first time
    proc take   { lst }     {  return [lindex $lst 0] }
    proc takeAt { lst inx } {  return [lindex $lst $inx] }

    proc dbg_indent { mess } {
        variable dbgspaces 
        variable dbgproc
        lappend dbgproc $mess
        set dbgspaces "$dbgspaces  "
    }
    proc dbg_undent { } {
        variable dbgspaces 
        variable dbgproc
        set dbgproc [lrange $dbgproc 0 end-1]
        regsub "  " $dbgspaces {} dbgspaces
    }
    
    proc dbg { mess } {
        variable debug
        variable dbgspaces 
        variable dbgproc

        if {$debug == 1} {
            set lvl [lindex $dbgproc end]
            puts "  // DBG: $dbgspaces$lvl: $mess"
        }
    }
    
    proc mapWithArgM { func lst { arg [list] } } {
        foreach item $lst {
            $func $item $arg
        }
    }
    
    proc mapWithArg { func lst { arg [list] } } {
        set res [list]
        foreach item $lst {
            lappend res [$func $item $arg]
        }
        return $res
    }
    
    proc showError { message } {
        puts "ERROR: $message"
        exit 1
    }

    ######################################################################
    proc makeRange { sz } {
        incr sz -1
        if {$sz > 0} {
            return "\[ $sz : 0 \] "
        } else {
            return "";
        }
    }

    ######################################################################
    proc getElem { index lst { errReturn "" } } {
        foreach item $lst {
            if {[take $item] == $index} {
                return [tail $item]
            }
        }
        return $errReturn
    }
    

    ######################################################################
    # recusively flatten down to a single list of lists
    proc flattenPinList { lst1 } {
        variable tmpList [list]

        proc process { lst2 } {
            if { [isNumber [tail $lst2]] } {
                variable tmpList
                lappend tmpList $lst2
            } else {
                # flatten each item down one layer
                map_ portUtil::process $lst2
            }
        }

        process $lst1
        return $tmpList
    }


    proc localName { x } {
        regsub "(.*::)" $x "" a 
        return $a
    }

    ######################################################################
    proc parsePrimary { info name } {
        # Primary {Bit#(numeric type a)} {width 4}
        # Primary {Int#(numeric type n)} {width 32} 
        # Primary {ActionValue#(type a)}
        # dbg "parsePrimary: $info / $name"
        
        set res [list]
        set sz [getWidth $info]
        if {$sz != ""} { 
            set res [list $name $sz]
            return $res
        } else {
            set res [list $name 0]
            # error "parsePrimary: no size info ($info) ????" 
        }
    }
    
    proc parseEnum { info name } {
        dbg "parseEnum: $info / $name"
        # Enum Test5::TEnum {members {ValA ValB ValC}} {width 4}
        set size [getWidth $info]
        return [list $name $size]
    }
    
    proc parseTaggedUnion { info name } {
        dbg "parseTaggedUnion: $info / $name"
        # TaggedUnion Test5::TS2 {members {{Bit#(3) X} {Bit#(4) Y} {Bit#(4) Z}}} {width 6} {position {Test5.bsv 16 5}}
        set members [getMembers $info]
        set size    [getWidth $info]

        puts "WARNING: tagged union '$name' treated as Bits\#\($size\)"
        # create this as a primary type since I don't know what else to do right now
        dbg " parseTaggedUnion size = $size"
        return [list $name $size]
        return $res
    }
    
    proc parseStruct { info name } {
        dbg "parseStruct: $info / $name"
        set sz      [getWidth   $info]
        set res [list]
        foreach member [getMembers $info] {
            set stype [take   $member]
            set sname [takeAt $member 1]
            set stype [localName $stype]
            lappend res [expandType $stype "$name\_$sname"]
        }
        return $res
    }
    
    proc parseVector { info name } {
        dbg "parseVector: $info / $name"
        set l [getLength $info]
	# use join because elem may or may not be a list
        set e [join [getElem "elem" $info]]  
        set res [list]
        for {set i 0} {$i<$l} {incr i} {
            lappend res [expandType $e "$name\_$i"]
        }
        return $res
    }
    
    ######################################################################
    proc expandType { fulltype {name ""} } {
        dbg_indent "expandType"
        dbg "args = $fulltype / $name"
        
        set info [typeFullAnalysis [join $fulltype]]
        
        set cmd [take $info]
        switch -glob $cmd {
            "Vector"      { set res [parseVector $info $name] }
            "Struct"      { set res [parseStruct $info $name] }
            "TaggedUnion" { set res [parseTaggedUnion $info $name] }
            "Enum"        { set res [parseEnum $info $name] }
            "Primary"     { set res [parsePrimary $info $name] }
            default       { showError "hit default for case statement with '$cmd'" }
        }
        
        dbg_undent
        return $res
    }
    
    
    ######################################################################
    ######################################################################
    ######################################################################
    # take a members list and return just the methods, flattened, etc
    #   (so that it matches the port list)
    
    proc expandToMethods { item { topname "" } } {

        dbg_indent "expandToMethods"
        dbg "args => $topname / [take $item]"
        dbg "        $item"
        
        # each item is
        # 1) interface => {interface Test7::TestN ifcA}
        # 2) method    => {method {ActionValue#(void) method1 {Int#(32) Int#(32)}}}
        set res $item
        
        if {[take $item] == "method"} {
            set outres [lindex $item 1 0]
            if {$topname == ""} {
                set name   [lindex $item 1 1]
            } else {
                set name   $topname\_[lindex $item 1 1]
            }

            # if we are here, then there are no more methods below us

            set inlist [lindex $item 1 2]
            dbg "method fields = $outres / $name / $inlist"

        } elseif {([take $item] == "Interface") || ([take $item] == "interface")} {
	    set ifctype [lindex $item 1]
            set name [lindex $item 2]
            set tpi [typeFullAnalysis $ifctype]

            if {$topname != ""} {
                set name $topname\_$name
            }

            dbg "tpi = $tpi"

            # handle vectors of interfaces
            if [regexp -line {^Vector::Vector} $ifctype match] {

                # Example: {Vector::Vector#(2, AxiDefines::AxiSlave)}
		# join is needed because the elem may or may not be a list
                set elem  [join [getElem "elem"   $tpi]]
                set num   [getElem "length" $tpi]

                dbg "tpi   => $tpi"
                dbg "elem  => $elem"

                set tpi_elem  [typeFullAnalysis $elem]

                set res [list]
                for {set i 0} {$i < $num} {incr i} {
                    lappend res [expandToMethods $tpi_elem $name\_$i]
                }

            } else {
            
                set res [list]

                # now this will be an interface with other interfaces and or methods
                foreach member [getMembers $tpi] {
                    dbg "member = $member"

                    if {[take $member] == "interface"} {
                        # expand sub interfaces
                        set nextname [lindex $member 2]
                        set hname $name\_$nextname
                        set res [concat $res [expandToMethods $member $hname]]

                    } elseif {[take $member] == "method"} {
                        # we;ve finally hit a method in this interface
                        lappend res $member

                    } else {
                        showError "expected either an interface or a method - $member"
                    }
                }
	    }

        } else {
            showError "I didn't expect to be here!"
        }

        dbg_undent
        return $res
    }
    
    # recurse through this list and make a flat list of only methods
    proc flattenToMethods { lst } { 
        dbg "flattenToMethods: $lst"

        if {[take $lst] == "method"} {
            return [list $lst]
        }

        # if { [isNumber [tail $lst]] } { return [list $lst] }

        set res [list]
        foreach item $lst {
            if {[take $lst] == "method"} {
                lappend res $item
            } else {
                set res [concat $res [flattenToMethods $item]]
            }
        }
        return $res
    }
    
    
    
    ######################################################################
    # Fix up the port information for methods
    # This used to:
    #  * remove "inhigh" enable signals
    #  * merge ready signals represented as a separate method into the
    #    method that it is a ready signal for
    # Enable signals are now removed by the Bluetcl command and RDY signals
    # are generally merged, but sometimes they can persist if Bluetcl fails
    # to find the interface type.  So this now does:
    #  * flatten the hierarchical info into a flat list
    #  * merge ready signals (out of paranoia)
    #
    # Merging assumes that RDY signals follow the method:
    #  {method ifcA_method1 {clock default_clock} {reset no_reset} {args {{ifcA_method1_in1 {port ifcA_method1_in1} {size 32}} {ifcA_method1_in2 {port ifcA_method1_in2} {size 32}}}} {enable EN_ifcA_method1}} 
    # {method RDY_ifcA_method1 {clock no_clock} {reset no_reset} {args {}} {result RDY_ifcA_method1}}
    
    proc fixPorts { ports_hier } {

        proc flattenIfcs { fields } {
	    proc flattenField { field } {
		set tag [lindex $field 0]
		if { $tag == "interface" } {
		    flattenIfcs [lindex $field 2]
		} else {
		    # strip out the hierarchical name
		    #set res [lreplace $field 1 2 [lindex $field 2]]
		    set res [lreplace $field 1 1]
		    return [list $res]
		}
	    }

	    set res [list]
	    set max [llength $fields]
	    for {set i 0} {$i < $max} {incr i} {
		set field [lindex $fields $i]
		set res [concat $res [flattenField $field]]
	    }
	    return $res
        }

	# Flatten the port info
	set ports [flattenIfcs $ports_hier]

	# Merge any ready signals (just in case)
        set res [list]
        set max [llength $ports]
        for {set i 0} {$i < $max} {incr i} {
            set line1 [lindex $ports $i]
            if { [expr $i + 1] < $max }  {
                set line2 [lindex $ports [expr $i + 1]]
                set method1 [lindex $line1 1]
                if {[lindex $line2 1] == "RDY_$method1"} {
                    # extract just the resulting info and merge it in?
                    
                    # TODO: assert args = "args"
                    # move result from line2 into args of line1
                    lappend line1 [list ready [getElem "result" $line2]]
                    incr i
                }
            }
            
            lappend res $line1
        }
        
        return $res
    }
    
    ######################################################################
    # take these two lines and merge the type stuff info theport stuff
    #   methods => {members {method {Test1a::TS method2 {Int#(32) Int#(32)}}}}
    #   ports   => method method2 {clock no_clock} {reset no_reset} {args {{method2_in1 {port method2_in1} {size 32}} {method2_in2 {port method2_in2} {size 32}}}} {result method2} {ready amIready}
    proc mergeTypesPorts { meth portInfo } {
        dbg "mergeTypesPorts"
        
        dbg "arg1 => $meth"
        dbg "arg2 => $portInfo"
        
        if {$meth     == ""} { showError "mergeTypesPorts null \$meth" }
        if {$portInfo == ""} { showError "mergeTypesPorts null \$portInfo" }
        
        if {([take $meth] != "method") || ([take $portInfo] != "method")} { 
            puts "ERROR: method   = $meth"
            puts "ERROR: portInfo = $portInfo"
            showError "non matching methods"
        }
        
        dbg "method arg = $meth"
        dbg "method prt = $portInfo"
        
        set mInfo    [lindex  $meth 1]
        set res      [lrange  $portInfo 0 3]  ;# TODO is there more ?
        set args     [take    [getElem "args" $portInfo]]
        
        set outtype  [lindex $mInfo    0]
        set mname    [lindex $mInfo    1]
        set intypes  [lindex $mInfo    2]
        
        ########################################
        # update each argument to add the proper type information
        set arglist [list]
        foreach arg $args {
            if {$arg != {} } {
                # only one type per args, there should be one type per individual arg
                lappend arg [list type [take $intypes]]   ;# get first entry onto arglist
                lappend arglist $arg
                set intypes [tail $intypes]               ;# shift that entry off
            }
        }
        lappend res [list args $arglist]
        
        ########################################
        set enable  [getElem "enable" $portInfo]
        if { $enable != "" } {
            lappend res [list enable $enable [list type "Bit\#(1)"]]
        }
        
        ########################################
        set result  [getElem "result" $portInfo]
        if { $result != "" } {
            # arg1 => method {ActionValue#(Bit#(4)) method9 Bit#(4)}
            # arg2 => method ifcB_method9 ........{args} {result ifcB_method9}
            
            # let's add a size parameter here to make this more complete at this level
            # make sure both exist... if no type then make it void
            # parse out ActionValues
            if {[regexp {ActionValue\#\((.+)\)} $outtype match datatype]} {
                set ft [typeFullAnalysis $datatype]
                set size [getWidth $ft]
            } elseif {$outtype == "" } {
                set outtype "void"
                set size 0
            } else {
                set ft [typeFullAnalysis $outtype]
                set size [getWidth $ft]
            }
            
            lappend res [list result $result [list type $outtype] [list size $size]]
        }
        
        ########################################
        set ready  [getElem "ready" $portInfo]
        if { $ready != "" } {
            lappend res [list ready $ready [list type  "Bit\#(1)"]]
        }
        
        dbg_undent
        return $res
    }
    
    
    ######################################################################
    # % map_ puts [lindex $res2 0 1]
    # 
    # method method2 {clock no_clock} {reset no_reset} {args {{method2_in1 {port method2_in1} {size 32}} {method2_in2 {port method2_in2} {size 32}}}} {result method2}
    # method RDY_method2 {clock no_clock} {reset no_reset} {args {}} {result RDY_method2}
    # method method3 {clock default_clock} {reset no_reset} {args {{method3_in1 {port method3_in1} {size 32}} {method3_in2 {port method3_in2} {size 12}}}} {enable EN_method3}
    # method RDY_method3 {clock no_clock} {reset no_reset} {args {}} {result RDY_method3}
    #
    # % map_ puts [getMembers [type full $package]]
    #
    # method {Test1a::TS method2 {Int#(32) Int#(32)}}
    # method {ActionValue#(void) method3 {Int#(32) Test1a::TS}}
    
    proc mergePortAndTypeInfo { package module } {
        variable debug
        # first expand types down to methods... but don't expand structure, etc just yet
        if { [catch "typeFullAnalysis $package"  fulltype] } {
            error "Cannot find the interface \"$package\" for analysis"
        }
        if { [lindex $fulltype 0] != "Interface" } {
            error "\"$package\" does not appear to be of type interface" 
        }

        set members  [getMembers $fulltype] 
        # members is a list of one of these
        # 1) interface => {interface Test7::TestN ifcA}
        # 2) method    => {method {ActionValue#(void) method1 {Int#(32) Int#(32)}}} 
        set methodsT  [map portUtil::expandToMethods $members]
        set methods   [portUtil::flattenToMethods $methodsT]
        
        if {$debug} {
            puts "/* ========== methods =========="
            map_ puts $methods
            puts "*/"
        }
        
        # collect all the ports we have, merge them so they line up 
        set modinfo   [module ports $module]
        set origports [lindex $modinfo 0 1]
        set ports     [fixPorts $origports]


        ############################################################
        if {$debug} {
            puts "/* ========== ports =========="
            map_ puts $ports
            puts "*/"
        }
        
        # merge them into one list so I know what port is what type
        # if method returns a vector, then yikes,, expand out this method to sequential ports
        if {[llength $methods] != [llength $ports]} {
            puts "// METHODS"
            map_ puts $methods
            puts "// PORTS"
            map_ puts $ports
            showError "unexpected methods / ports array length mismatch! [llength $methods] [llength $ports]"
        }

        set portInfo [zipWith portUtil::mergeTypesPorts $methods $ports]
        
        # add extra pins onto the end (parameters that are not part of methods, etc)
        # these are wires, treated as inputs only ?  what about interface parameters ?

        return $portInfo
    }
    
    ######################################################################
    proc createExpandedPins { item } {
        proc renamePin { pin } {
            global renameList
            set newname [getElem $pin $renameList]
            if {$newname != ""} {
                return $newname
            } else {
                return $pin
            }
        }

        set enable [getElem "enable" $item]
        set ready  [getElem "ready"  $item]
        set result [getElem "result" $item]
        set args   [take [getElem "args" $item]]
        
        set res [list]
        
        if {$ready != ""} {
            # {ready RDY_ifcA_method2 {type Bit#(1)}}
            set pin [take $ready]
            
            set outpin [renamePin $pin]
            lappend res [list "output" [list $pin 1] [list [list $outpin 1]]]
        }
        
        if { $enable != "" } {
            # {enable EN_ifcA_method2 {type Bit#(1)}}
            set pin [take $enable]
            
            set outpin [renamePin $pin]
            lappend res [list "input" [list $pin 1]  [list [list $outpin 1]]]
        }
        
        if {$result != ""} {
            # {result ifcA_method2 {type Int#(32)} {size 32}}
	    # join is needed because type may or may not be a list
	    # (Maybe#(Bool) vs. {Vector#(32, Bool)}).  We want to pass
	    # just the type string -- without braces -- to expandType.
            set type     [join [getElem "type" $result]]
            set size     [getElem "size" $result]
            set pin      [take $result]

            set outpin   [renamePin $pin]
            dbg "result type is $type"
            dbg "   length = [llength $type] / [lindex $type 0]"
            if {[regexp -line {^\{*ActionValue\#\((.+)\)\}*$} $type match val]} {
                set newpins  [expandType $val $outpin]
            } else {
                set newpins  [expandType $type $outpin]
            }

            dbg "createExpandedPins: $pin $size"
            lappend res [list "output" [list $pin $size] [list $newpins]]
        }
        
        foreach arg $args {
            # methods
            # {{ifcB_method9_in1 {port ifcB_method9_in1} {size 4} {type Bit#(4)}}}
            set size     [getElem "size" $arg]
            set type     [getElem "type" $arg]
            set pin      [getElem "port" $arg]
            if { $size >= 1 } {
                set outpin   [renamePin $pin]
                set newpins  [expandType $type $outpin]
                lappend res [list "input" [list $pin $size] [list $newpins]]
            }
        }
        
        # return { original expanded }
        return [list $item $res]
    }
    
    ######################################################################
    proc getClockRstParamPins  { module } {
        set modinfo  [module ports $module]
        return [take [getElem "args" $modinfo]]        
    }
    
    ######################################################################
    # this only works on merged list:
    proc listMethodInfo { item } {
        set meth   [takeAt $item 1]
        set enable [getElem "enable" $item]
        set ready  [getElem "ready"  $item]
        set result [getElem "result" $item]
        
        set res [list]
        
        ########################################
        lappend res "  // ===================="
        lappend res "  // Method = $meth"
        if {$ready != ""} {
            set type [getElem "type" $ready]
            lappend res  [format "  //   ready  => %-20s %3d   %s"  [take $ready] 1 $type]
        }
        
        ########################################
        if {$enable != ""} {
            set type [getElem "type" $enable]
            lappend res [format  "  //   enable => %-20s %3d   %s"  [take $enable] 1 $type]
        }
        
        ########################################
        if {$result != ""} {
            set type [getElem "type" $result]
            # puts [type full $type]
            set size [getElem "size" $result]
            if {$size == ""} { set size 0 }
            lappend res [format "  //   result => %-20s %3d   %s"  [take $result] $size $type]
        }

        ########################################
        set args [take [getElem "args" $item]]
        if {$args != ""} {
            foreach inp $args {
                set port [getElem "port" $inp]
                set type [getElem "type" $inp]
                set size [getElem "size" $inp]
                lappend res [format "  //   input  => %-20s %3d   %s"  $port $size $type]
            }
        }
        
        return $res
    }
    
    ######################################################################
    # change this hierarchy of pins into a verilog concat statement
    proc toVerilogConcat { pins } {
        set lst [flattenPinList $pins]
        set res [list]
        foreach pin $lst {
            lappend res [take $pin]
        }
        return $res
    }
    
    proc processSwitches { lst } {
        global argv argc

        ##############################
        # get rid of everything before the "--" , if it exists
        set args [list]
        foreach arg $argv {
            if {$arg == "--"} {
                set args [list]
            } else {
                lappend args $arg
            }
        }
        
        ##############################
        # set default value for switches
        foreach item $lst {
            set opt [take $item]
            global $opt
            if { [llength $item] > 1 } {
                set $opt [tail $item]
            } else {
                set $opt 0
            }
        }
        
        ##############################
        set newargs [list]
        while { [llength $args] > 0 } {
            set arg  [take $args]
            set args [tail $args]
            
            if { [regexp -line {^\-(\w+)$} $arg match sw] } {
                # command switch see if it is one in the list
                set option [getElem $sw $lst "<notfound>" ]
                if { $option == "<notfound>" } {
                    showError "illegal command line option: $sw"
                }
                
                global $sw
                if { [llength $option] == 1 } {
                    set $sw [take $args]
                    set args [tail $args]
                } else {
                    set $sw 1
                }
                
            } else {
                lappend newargs $arg
            }
        }
        set argv $newargs
        set argc [llength $newargs]
    }
    
    ######################################################################
    proc createExpandedVerilogWrapper { package module verilog } {
        
        # read verilog file to get final pin information
        if { 1 } {
            variable verilogPins
            
            if {[file exists $verilog] == 0} {
                showError "verilog file '$verilog' doesn't exist"
            }
            set fp [open $verilog "r"]
            while { [gets $fp line] } {
                if [regexp -line {^// ([\w_]+)\s+(I|O)\s+(\d+)} $line match pin dir sz] {
                    lappend verilogPins $pin
                } elseif [regexp -line {^module ([\w_]+)\(} $line match pin] {
                    variable module 
                    set module $pin
                }
            }
            close $fp;
        }
        
        # walk port info, when ports are pimary types, just match one to one
        # when port is a different type, expand it and connect pin in bsv verilog
        # to each individual field in top layer bsv..
        
        # this is one structure with pin and type information
        set normalPortInfo     [portUtil::mergePortAndTypeInfo   $package $module ]
        set expandedPortInfo   [map portUtil::createExpandedPins $normalPortInfo]
        
        foreach i1 $expandedPortInfo {
            foreach i2 $i1 {
                foreach i3 $i2 {
                    dbg "  expandedPortInfo: $i3"
                }
            }
        }

        # map_ puts $normalPortInfo
        # create verilog wrapper file 
        # port list first 
        
        global env
        set includeFile [list]
        set lines       [list]
        
        ######################################################################
        set portlist  [list]
        set portio    [list]
        set wires     [list]
        set modport   [list]
        set includeWires [list]
        set includeRenames [list]
        set modPort [list]
        set oldPort [list]
        
        # this is all the extra pins not part of "methods", clocks, reset, etc
        set modulePins [portUtil::getClockRstParamPins $module]
        
        # do clock, reset, parameter pins first
        foreach pin $modulePins {
            
            switch -glob [lindex $pin 0] {
                "clock" { 
                    set name  [portUtil::getElem "osc" $pin]
                    set oname [renamePin $name]
                    
                    lappend portlist $oname 
                    lappend portio  "  input $oname;"
                    lappend modport "   .$name\( $oname \)"

                    lappend oldport        "   .$name\( $name \)"
                    lappend includeWires   "  wire   $oname;"
                    if {$oname != $name } {
                        lappend includeWires   "  wire   $name;"
                        lappend includeRenames "  assign $name = $oname;"
                    }
                }
                "reset" { 
                    set name  [portUtil::getElem "port" $pin]
                    set oname [renamePin $name]
                    
                    lappend portlist $oname 
                    lappend portio "  input $oname;"
                    lappend modport "   .$name\( $oname \)"

                    lappend oldport "   .$name\( $oname \)"
                    lappend includeWires   "  wire   $oname;"
                    if {$oname != $name } {
                        lappend includeWires   "  wire   $name;"
                        lappend includeRenames "  assign $name = $oname;"
                    }
                }
                "port" {
                    set name [lindex $pin 1]
                    set size [portUtil::getElem "size" $pin]
                    set oname [renamePin $name]
                    if { $size >= 1 } { 
                        lappend portlist $oname 
                        lappend portio  "  input  [makeRange $size]$oname;"
                        lappend modport "   .$name\( $oname \)"
                        
                        lappend oldport "   .$name\( $oname \)"
                        lappend includeWires   "  wire   [makeRange $size]$oname;"
                        if {$oname != $name } {
                            lappend includeWires   "  wire   [makeRange $size]$name;"
                            lappend includeRenames "  assign $name = $oname;"
                        }
                    }
                }
                default { 
                    showError "unknown output pininfo: $pin"
                }
            }
        }
        lappend portio   ""
        
        ############################################################
        # now do method pins
        
        foreach itemx $expandedPortInfo {
            set orig [lindex $itemx 0]
            set newi [lindex $itemx 1]
            
            # add method info for documentation before wires and ports
            set i [listMethodInfo $orig] 
            set portio       [concat $portio       "\n" $i ]
            set includeWires [concat $includeWires "\n" $i ]
            
            set expandedFrom [list]
            foreach pins $newi {
                set dir      [lindex $pins 0]
                set oldpin   [lindex $pins 1 0]
                set oldSize  [lindex $pins 1 1]
                set newpins  [lindex $pins 2]
                
                # don't forget about Bit#(0) and void
                if {$oldSize <= 0} { continue }

                # connect original (old) pin to concat of new pins...
                # returns list of {pinname size}
                set flatlist  [flattenPinList $newpins]
                set flatlist  [filter portUtil::sizeGtZero $flatlist]
                set pinsonly  [map portUtil::take $flatlist]

                # create expanded {newpin, size}
                set renamedPins [map portUtil::renamePin $pinsonly]

                # for wrapper
                set newgroup [join $renamedPins ","] 
                if { [regexp {,} $newgroup] } {
                    lappend modport "   .$oldpin\( { $newgroup } \)"
                } else {
                    lappend modport "   .$oldpin\( $newgroup \)"
                }
                
                # for include file
                lappend oldport "   .$oldpin\( $oldpin \)"
                
                # now expand each new pin out for new top level verilog block
                set pinlst [portUtil::flattenPinList $newpins]
                
                if {$oldpin != $newgroup} {
                    lappend includeWires   "  wire   [makeRange $oldSize]$oldpin;"

                    if {$dir == "output"} {

                        ########################################
                        # blow out all 
                        set h [expr $oldSize - 1]
                        foreach i $flatlist {
                            dbg "i = $i"
                            set name [take $i]
                            set size [tail $i]
                            set l [expr $h - $size + 1]
                            lappend includeRenames "  assign $name = $oldpin\[$h:$l\];"
                            lappend expandedFrom $oldpin\[$h:$l\]
                            set h [expr $h - $size]
                        }
                        # lappend includeRenames "  assign { $newgroup } = $oldpin ;"
                    } else {

                        ########################################
                        # blow out all new pins 
                        set h [expr $oldSize - 1]
                        foreach i $flatlist {
                            dbg "i = $i"
                            set name [take $i]
                            set size [tail $i]
                            set l [expr $h - $size + 1]
                            lappend includeRenames "  assign $oldpin\[$h:$l\] = $name;"
                            lappend expandedFrom ""
                            set h [expr $h - $size]
                        }
                        # lappend includeRenames "  assign { $newgroup } = $oldpin ;"
                        # kusp 8887771507

                    }

                } else {
                    lappend expandedFrom   ""
                }
                
                # lappend includeRenames ""

                ########################################
                foreach pin $pinlst {
                    
                    # this is an output pin, flattened good
                    # for portio declaration for now
                    set name [lindex $pin 0]
                    set size [lindex $pin 1]
                    
                    if { $size >= 1 } {
                        set oname [renamePin $name]
                        
                        # create include file lines
                        lappend portlist  $oname
                        
                        set fromComment   [take $expandedFrom]
                        set expandedFrom  [tail $expandedFrom]
                        
                        if {$fromComment != ""} {
                            set fromComment "  // $fromComment"
                        }
                        
                        lappend portio "  $dir  [makeRange $size]$oname;$fromComment"
                        
                        dbg "size = $size for $oname"
                        if {$dir == "output"} {
                            lappend wires "  wire   [makeRange $size]$oname;$fromComment"
                        }
                        lappend includeWires "  wire   [makeRange $size]$oname;$fromComment"
                    }
                }
            }
            lappend portio ""
            lappend includeWires ""
        }        
        
        ############################################################
        # help user along by making a shell rename file ?
        global makerename rename
        if {$makerename == 1} {
            if { $rename != "/dev/null" } {
                set fp [open $rename "w"]
            } else {
            set fp [open ".rename.tcl" "w"]
            }
            foreach oname $portlist {
                puts $fp "  lappend newList \[list $oname x \]"
            }
            close $fp;
        }
        
        ############################################################
        set portlist [join $portlist ",\n    "]

        lappend lines "module $module\_expanded (\n    $portlist );"
        lappend lines ""
        lappend lines [join $portio "\n"]
        lappend lines ""
        lappend lines [join $wires "\n"]
        lappend lines ""
        lappend lines "  $module _$module ( "
        lappend lines [join $modport ",\n"]
        lappend lines "  );\n"
        lappend lines "endmodule\n"
        
        ############################################################
        # add module instantiation to include file ?
        
        #         lappend includeFile "`ifndef __EXPANDPORTS_INWIRE__"
        #         lappend includeFile "`define __EXPANDPORTS_INWIRE__ reg"
        #         lappend includeFile "`endif"        
        #         lappend includeFile "`ifndef __EXPANDPORTS_OUTWIRE__"
        #         lappend includeFile "`define __EXPANDPORTS_OUTWIRE__ wire"
        #         lappend includeFile "`endif"        
        
        lappend includeFile ""
        set     includeFile [concat $includeFile $includeWires]
        lappend includeFile ""        
        lappend includeFile "`ifndef __EXPANDPORTS_NO_RENAMES__"
        set     includeFile [concat $includeFile $includeRenames]
        lappend includeFile "`endif"
        lappend includeFile ""
        lappend includeFile "`ifndef __EXPANDPORTS_DONT_CREATE_DUT__"
        lappend includeFile "  $module _$module ( "
        lappend includeFile [join $oldport ",\n"]
        lappend includeFile "  );"
        lappend includeFile "`endif"
        
        return [list $lines $includeFile]
    }
    
    proc printMethodTypes { package module } {
        set normalPortInfo  [portUtil::mergePortAndTypeInfo   $package $module]
        foreach item [map portUtil::listMethodInfo $normalPortInfo] {
            map_ puts $item
        }
    }
    
    proc getAllPortInfo { package module } {
        set normalPortInfo  [portUtil::mergePortAndTypeInfo   $package $module]
        return [map portUtil::createExpandedPins $normalPortInfo]
    }
    
    # returns true if the second element in pair is > 0
    proc sizeGtZero { elem } {
        set sz [utils::snd $elem]
        return [expr ($sz != 0)]
    }

    proc typeFullAnalysis { type } {
        set info [type full $type] 
        switch -exact [lindex $info 0] {
            "Alias" { set res [typeFullAnalysis  [lindex $info 2]] }
            default { set res $info }
        }
        return $res 
    }
}
