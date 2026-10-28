namespace import ::Bluetcl::*

flags set {-verilog}
module load mkWireTypeMapEmpty
if {[module wiretypemap mkWireTypeMapEmpty] ne {}} {
    error "empty module has wire types"
}
puts "empty module: no entries"

module load mkWireTypeMapMany
set entries [module wiretypemap mkWireTypeMapMany]
if {[llength $entries] != [llength [lsort -unique $entries]]} {
    error "wiretypemap contains duplicate (name, type) entries"
}
set resultEntry [lsearch -inline -index 0 -exact $entries total]
if {$resultEntry eq {}} {
    error "missing total output type"
}
set bit32 [lindex $resultEntry 1]
for {set i 0} {$i < 128} {incr i} {
    set inst values_$i
    foreach name [list $inst ${inst}\$Q_OUT ${inst}.Q_OUT] {
        if {[lsearch -exact $entries [list $name $bit32]] < 0} {
            error "missing register type for $name"
        }
    }
}
puts "repeated instances: 128 registers with all three output aliases"
puts "register type: $bit32"

module clear
module load mkWireTypeMapMany
if {[module wiretypemap mkWireTypeMapMany] ne $entries} {
    error "wiretypemap changed after reloading the module"
}
puts "reload: stable ordered map with unique pairs"
