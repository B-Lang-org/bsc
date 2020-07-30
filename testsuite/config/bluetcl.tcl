####################
# Top level testing functions
#
# proc bluetcl_pass { script }
#
# proc bluetcl_run_compare_pass { source {expected ""} {sedfilter ""}  }
#
# proc bluetcl_run_compare_pass_bug { source {expected ""} {sedfilter ""} {bug ""} }
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
    set status [exec_with_log "run_bluetcl" $cmd 2]
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
proc run_bluetcl { source } {
    global bluetcl
    global srcdir
    global subdir

    bluetcl_initialize

    set here [absolute $srcdir]
    cd [file join $here $subdir]
    set output [make_bluetcl_output_name $source]
    set cmd "$bluetcl $source >& $output"
    verbose "Executing: $cmd" 4
    set status [exec_with_log "run_bluetcl" $cmd 2]
    cd $here
    return [expr $status == 0]
}

# Do a bluetcl run, and report status
proc bluetcl_pass { source } {
    global xfail_flag

    set current_xfail $xfail_flag

    incr_stat "bluetcl_pass"

    if [run_bluetcl $source] then {
	pass "`$source' executes"
    } else {
	fail "`$source' should execute"
    }
}

# DO run and compare output
proc bluetcl_run_compare_pass { source {expected ""} {sedfilter ""} } {

    bluetcl_pass $source

    set output [make_bluetcl_output_name $source]

    bluetcl_compare $output $expected $sedfilter
}

# DO run and compare output (does not match because of known bug)
proc bluetcl_run_compare_pass_bug { source {expected ""} {sedfilter ""} {bug ""} } {

    global env
    global target_triplet

    bluetcl_pass $source

    set output [make_bluetcl_output_name $source]

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
