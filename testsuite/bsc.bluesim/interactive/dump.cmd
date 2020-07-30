# Test script for the dump command

puts "Dump 
# dump -- should be no active dumps
dump

# step ten cycles -- should be no dump output
step 11

# enable dumping of rules and state
dump rules on
dump state

# check that dump identifies the active dumps
dump

# step ten cycles -- should be rule and state dump output
step 10

# turn off state dumping and on cycle dumping
dump state off
dump cycles

# check that dump identifies the active dumps
dump

# step ten cycles -- should be rule and state dump output
step 10

# turn off all dumping
dump off

# check that dump identifies the active dumps
dump

# step ten cycles -- should be no dump output
step 10

# turn on VCD dumping
dump vcd test.vcd

# check that dump identifies the active dumps
dump

# step ten cycles -- should be no dump to screen, only to VCD
step 10

# turn off VCD dumping
dump vcd off

# check that dump identifies the active dumps
dump

# step ten cycles -- should be no dump output
step 10

# turn on VCD dumping
dump vcd

# check that dump identifies the active dumps
dump

# step ten cycles -- should be no dump to screen, only to VCD
step 10

# end of script

