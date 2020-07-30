namespace import ::Bluetcl::*

puts [flags set {-verilog}]

puts {----------}

# The .ba file will load, but it will fail to load the .bo
if { [catch {puts [module load mkTestSchedErr]} fid] } {
    puts $fid
}

puts {----------}

puts [schedule urgency mkTestSchedErr]
puts [schedule execution mkTestSchedErr]
puts [schedule methodinfo mkTestSchedErr]
puts [schedule pathinfo mkTestSchedErr]
puts [schedule warnings mkTestSchedErr]
puts [schedule errors mkTestSchedErr]

puts {----------}

