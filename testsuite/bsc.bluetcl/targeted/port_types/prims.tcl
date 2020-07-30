namespace import ::Bluetcl::*

puts [flags set {-verilog}]
puts [module load sysPrims]

puts {----------}

set ports [submodule ports sysPrims]
set porttypes [submodule porttypes sysPrims]

set len [llength $ports]
for {set i 0} {$i < $len} {incr i} {
    puts [lindex $ports $i]
    puts [lindex $porttypes $i]
    puts {----------}
}

