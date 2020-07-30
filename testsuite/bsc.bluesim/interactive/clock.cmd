# Test script for the clock command

# show clocks
puts [sim clock]

# change to the faster clock domain
sim clock {clk2$CLK_OUT}

# show clocks
puts [sim clock]

# step three cycles in one domain
sim step 3

# show clocks
puts [sim clock]

# change to default domain
sim clock CLK

# show clocks
puts [sim clock]

# step ten cycles in default domain
sim step 10

# show clocks
puts [sim clock]

# end of script

