namespace import ::Bluetcl::*

puts [flags set {-verilog}]
puts [module load mkSplitPortTypes]

puts {----------}
puts "module porttypes mkSplitPortTypes"
foreach e [module porttypes mkSplitPortTypes] {
    puts $e
}

puts {----------}
puts "module ports mkSplitPortTypes"
foreach e [module ports mkSplitPortTypes] {
    puts $e
}
