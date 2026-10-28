namespace import ::Bluetcl::*

flags set {-verilog}
module load mkPixelStash

# The other wiretypemap test sorts its output. Keep the raw candidate
# order here, including the relative order of external ports, rules,
# and repeated primitive port types, to catch changes in deduplication.
set entries [module wiretypemap mkPixelStash]
if {[llength $entries] != [llength [lsort -unique $entries]]} {
    error "wiretypemap contains duplicate (name, type) entries"
}
foreach entry $entries {
    puts $entry
}
