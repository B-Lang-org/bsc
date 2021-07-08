set tclFiles [lindex $argv 0]
set packFiles [lindex $argv 1]

#puts "tclFiles are: $tclFiles"
#puts "packages are: $packFiles"

if { [llength $tclFiles] != 0 } {
    eval auto_mkindex . $tclFiles
} else {
    set ti [open "tclIndex" "w"]
    puts $ti "# No files to index"
    close $ti
}

# eval pkg_mkIndex -verbose . $packFiles
# the pkg_mkIndex command sucks so lets roll our own

# All we need to do for the basic case is get the package provide directives
proc getpackagename { f } {
    set fp [open $f "r"]
    set ret [list]
    while { [gets $fp line] >= 0 } {
        if { [regexp -line {^package[\s]+provide[\s]+([\w]+)\s+([\d]+\.[\d]+)} $line l name ver]} {
                lappend ret [list $name $ver]
            }
    }
    close $fp;
    return $ret
}

# Expand out the glob patterns
set files [list]
foreach pat $packFiles {
    lappend files [glob $pat]
}

set outfp [open "pkgIndex.tcl" "w"]
puts $outfp "#  Automatically generated do not edit"
foreach f $files {
    set prs [getpackagename $f]
    foreach nv $prs {
        set root [lindex $nv 0]
        set ver [lindex $nv 1]
        if { $root == "" } { continue }

            set s [format {package ifneeded %s %s [list source [file join $dir %s]]} $root $ver $f]
            puts $outfp $s
    }
}
close $outfp
