# Test script for the hierarchy navigation and lookup commands

# step one cycle
sim step

# print the current instance location
puts "sim pwd"
puts [sim pwd]
puts "-------"

# list the values at this level of hierarchy
puts "sim ls"
puts [sim ls]
puts "-------"

# list the CAN_FIREs in all mid* instances
puts "sim ls mid?.CAN_FIRE_*"
puts [sim ls mid?.CAN_FIRE_*]
puts "-------"

# move down to the mid2 instance
puts "sim cd mid2"
sim cd mid2
puts "-------"

# print the new instance location
puts "sim pwd"
puts [sim pwd]
puts "-------"

# list the rules at this level of hierarchy
puts "sim ls RL_*"
puts [sim ls RL_*]
puts "-------"

# list the CAN_FIREs and WILL_FIREs
puts "sim ls CAN_FIRE_* WILL_FIRE_*"
puts [sim ls CAN_FIRE_* WILL_FIRE_*]
puts "-------"

# lookup the symbol for WILL_FIRE_*
set wfs [sim lookup "WILL_FIRE_*"]

# describe the WILL_FIRE symbols
puts "sim describe <WILL_FIRES>"
puts [eval sim describe $wfs]
puts "-------"

# record the symbol for the current directory
set mid2 [sim lookup ""]

# move back to the top
puts "sim cd"
sim cd
puts "-------"

# lookup the symbol for mid1.count
set mid1_count [sim lookup "mid1.count"]

# print the location again
puts "sim pwd"
puts [sim pwd]
puts "-------"

# print some values
foreach wf $wfs {puts [sim get $wf]}
puts [sim get $mid1_count]

# print a value obtained using a relative lookup
puts [sim get [sim lookup "count" $mid2]]

# step 6 cycles and print some values again
sim step 6
foreach wf $wfs {puts [sim get $wf]}
puts [sim get [sim lookup "count" $mid2]]

# step once and print again
sim step 
foreach wf $wfs {puts [sim get $wf]}
puts [sim get [sim lookup "count" $mid2]]

# save symbol for mid2.count
set mid2_count [sim lookup "count" $mid2]

# cd to level1.level2.count
puts "sim cd level1.level2.count"
sim cd level1.level2.count
puts "-------"

# print the location again
puts "sim pwd"
puts [sim pwd]
puts "-------"

# step once and print again
sim step 
puts [eval sim get $wfs $mid2_count [sim lookup ""]]

# move up 2 levels
puts "sim up 2"
sim up 2
puts "-------"

# print the location again
puts "sim pwd"
puts [sim pwd]
puts "-------"

# move up to the top
puts "sim cd ."
sim cd .
puts "-------"

# print the location again
puts "sim pwd"
puts [sim pwd]
puts "-------"

# move down using an absolute path
puts "sim cd .level1.level2"
sim cd .level1.level2
puts "-------"

# print the location again
puts "sim pwd"
puts [sim pwd]
puts "-------"

# move up one level
puts "sim up"
sim up
puts "-------"

# print the location again
puts "sim pwd"
puts [sim pwd]
puts "-------"

# end of script

