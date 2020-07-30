namespace import ::Bluetcl::*

puts [flags set {-verilog}]

puts {----------}

puts [module load mkS]

puts [schedule urgency mkS]
puts [schedule execution mkS]
puts [schedule methodinfo mkS]
puts [schedule pathinfo mkS]
puts [schedule warnings mkS]
puts [schedule errors mkS]

puts {----------}

puts [module load mkM]

puts [schedule urgency mkM]
puts [schedule execution mkM]
puts [schedule methodinfo mkM]
puts [schedule pathinfo mkM]
puts [schedule warnings mkM]
puts [schedule errors mkM]

puts {----------}

