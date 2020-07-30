# Test script for working with async simulation

# start running asynchronously
sim run async

# print a string (should happened before any sim output)
puts "Started running..."

# wait for the simulation time to reach 1 billion
while {[sim time] < 1000000000} { after 100 }

# stop the simulation and record the time
set t1 [sim stop]

# advance 10 cycles synchronously and record the new time
sim step 10
set t2 [sim time]

# check that the difference in times is 100, as expected
puts [expr $t2 - $t1]

# continue running asynchronously
sim run async

# wait for the simulation to complete
puts [sim sync]

# show clocks
puts [sim clock]

# end of script
