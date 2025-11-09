####################
# Top level testing functions
#
# proc bluetcl_pass { script }
#
# proc bluetcl_run_compare_pass { source {expected ""} {expected_bh ""} {sedfilter ""}  }
#
# proc bluetcl_run_compare_pass_bug { source {expected ""} {expected_bh ""} {sedfilter ""} {bug ""} }
#
# proc bluetcl_compare { source {expected ""} {sedfilter ""} }
#
# proc bluetcl_opt_pass { source {options {}} {outfile {""}} }
#
####################
proc bluetcl_exec_pass { cmdline outname } {
    set stat [bluetcl_exec $cmdline $outname]
    incr_stat "bluetcl_exec_pass"
    if {$stat} {
        pass "`$outname' executes"
    } else {
        fail "`$outname' should execute"
    }
}
proc bluetcl_exec_fail { cmdline outname } {
    set stat [bluetcl_exec $cmdline $outname]
    incr_stat "bluetcl_exec_fail"
    if {! $stat} {
        pass "`$outname' fails as executes"
    } else {
        fail "`$outname' should not have executed"
    }
}
# worker function
proc bluetcl_exec { cmdline outname } {
    global bluetcl
    global srcdir
    global subdir

    bluetcl_initialize

    set here [absolute $srcdir]
    cd [file join $here $subdir]
    set output [make_bluetcl_output_name $outname]
    set cmd "$bluetcl $cmdline >& $output"
    verbose "Executing: $cmd" 4
    set status [exec_with_log "bluetcl_exec" $cmd 2]
    cd $here
    return [expr $status == 0]
}
# DO run and compare output
proc bluetcl_exec_compare_pass { cmdline outname {expected ""} {sedfilter ""} } {

    bluetcl_exec_pass $cmdline $outname

    set output [make_bluetcl_output_name $outname]
    bluetcl_compare $output $expected $sedfilter
}
# DO run and compare output
proc bluetcl_exec_compare_fail { cmdline outname {expected ""} {sedfilter ""} } {

    bluetcl_exec_fail $cmdline $outname

    set output [make_bluetcl_output_name $outname]
    bluetcl_compare $output $expected $sedfilter
}


# worker bee
proc make_bluetcl_output_name { source } {
    set src [file tail $source]
    set src [regsub -all { } $src "_"]
    set filename "$src.bluetcl-out"
    return $filename
}

# worker bee
proc make_bluetcl_bh_output_name { source } {
    set src [file tail $source]
    set src [regsub -all { } $src "_"]
    set filename "$src.bluetcl-bh-out"
    return $filename
}


# For historical reasons, we do not tag BSV syntax output with -bsv
# the way we tag BH syntax output with -bh
proc make_bluetcl_bsv_output_name { source } {

    return [make_bluetcl_output_name $source]

}

# worker bee
proc run_bluetcl_bsv { source } {
    global bluetcl
    global srcdir
    global subdir

    bluetcl_initialize

    set here [absolute $srcdir]
    cd [file join $here $subdir]
    set output [make_bluetcl_bsv_output_name $source]
    set cmd "$bluetcl $source >& $output"
    verbose "Executing: $cmd" 4
    set status [exec_with_log "run_bluetcl_bsv" $cmd 2]
    cd $here
    return [expr $status == 0]
}

proc run_bluetcl_bh { source } {
    global bluetcl
    global srcdir
    global subdir

    bluetcl_initialize

    set here [absolute $srcdir]
    cd [file join $here $subdir]
    set output [make_bluetcl_bh_output_name $source]
    # The source file has to be the first argument for the
    # Tcl interpreter to pick it up.
    set cmd "$bluetcl $source -bh >& $output"
    verbose "Executing: $cmd" 4
    set status [exec_with_log "run_bluetcl_bh" $cmd 2]
    cd $here
    return [expr $status == 0]
}

# Do a bluetcl run (BSV syntax) and report status
proc bluetcl_bsv_pass { source } {
    global xfail_flag

    set current_xfail $xfail_flag

    incr_stat "bluetcl_bsv_pass"

    if [run_bluetcl_bsv $source] then {
	pass "`$source' executes with BSV syntax"
    } else {
	fail "`$source' should execute with BSV syntax"
    }
}

# Do a bluetcl run (BH syntax) and report status
proc bluetcl_bh_pass { source } {
    global xfail_flag

    set current_xfail $xfail_flag

    incr_stat "bluetcl_bh_pass"

    if [run_bluetcl_bh $source] then {
	pass "`$source' executes with BH syntax"
    } else {
	fail "`$source' should execute with BH syntax"
    }
}

# Do bluetcl runs and report status (both syntaxes)
proc bluetcl_pass { source } {
    bluetcl_bsv_pass $source
    bluetcl_bh_pass $source
}

# Do bluetcl run and compare output (BSV syntax)
proc bluetcl_run_bsv_compare_pass { source {expected ""} {sedfilter ""} } {

    bluetcl_bsv_pass $source

    set output [make_bluetcl_bsv_output_name $source]

    bluetcl_compare $output $expected $sedfilter

}

# Do bluetcl run and compare output (BH syntax)
proc bluetcl_run_bh_compare_pass { source {expected ""} {sedfilter ""} } {

    bluetcl_bh_pass $source

    set output [make_bluetcl_bh_output_name $source]

    bluetcl_compare $output $expected $sedfilter

}

# Do bluetcl runs and compare output (both syntaxes)
proc bluetcl_run_compare_pass { source {expected_bsv ""} {expected_bh ""} {sedfilter ""} } {

    bluetcl_run_bsv_compare_pass $source $expected_bsv $sedfilter

    bluetcl_run_bh_compare_pass $source $expected_bh $sedfilter

}

# Do bluetcl run and compare output (BSV syntax, does not match because of known bug)
proc bluetcl_run_bsv_compare_pass_bug { source {expected ""} {sedfilter ""} {bug ""} } {

    global env
    global target_triplet

    bluetcl_bsv_pass $source

    set output [make_bluetcl_bsv_output_name $source]

    setup_xfail $target_triplet $bug
    bluetcl_compare $output $expected $sedfilter

}

# Do bluetcl run and compare output (BH syntax, does not match because of known bug)
proc bluetcl_run_bh_compare_pass_bug { source {expected ""} {sedfilter ""} {bug ""} } {

    global env
    global target_triplet

    bluetcl_bh_pass $source

    set output [make_bluetcl_bh_output_name $source]

    setup_xfail $target_triplet $bug
    bluetcl_compare $output $expected $sedfilter

}

# RUN bluetcl with options specifying outfile (can be a module rather than tclfile
proc bluetcl_opt_pass { source {options {}} {outfile {""}} } {

    incr_stat "bluetcl_opt_pass"

    set stat [bluetcl_opt_run $source $options $outfile]
    if [run_bluetcl $source] then {
	pass "`$source' executes"
    } else {
	fail "`$source' should execute"
    }

}

# worker bee for above
proc bluetcl_opt_run { source {options {}} {outfile {""}} } {
    global bluetcl
    global srcdir
    global subdir

    bluetcl_initialize

    set here [absolute $srcdir]
    cd [file join $here $subdir]
    if { $outfile == "" } {
        set output [make_bluetcl_output_name $source]
    } else {
        set output $outfile
    }

    set cmd "$bluetcl $source $options >& $output"
    verbose "Executing: $cmd" 4
    set status [exec_with_log "run_bluetcl_opt" $cmd 2]
    cd $here
    return [expr $status == 0]
}

# Compare tcl output after applying some sed filters
proc bluetcl_compare { output {expected ""} {bre {}} {ere {}}} {

    append bre { -e {/^Welcome/d} -e {/^Version/d}}

    if { [which_os] == "Darwin" } {
	append ere { -e {1,/^$/{;N;N;N;N;/\nWARNING: This version of tcl is included in macOS for compatibility with legacy software. \nIn future versions of macOS the tcl runtime will not be available by \ndefault, and may require you to install an additional package.\n$/d;}}}
    }

    if {[string compare $expected ""] == 0} {
	set expected "$output.expected"
    }

    compare_file_filtered $output $expected $bre $ere
}

####################
# Initialization

global bluetcl_initialized

set bluetcl_initialized 0

proc bluetcl_initialize {} {

    global bluetcl_initialized
    global bluetcl

    if {!$bluetcl_initialized} {
        set bluetcl_initialized 1
        set bluetcl [which_bluetcl]
    }
}

####################
