# Test script for handling aperiodic clocks

# show clocks
puts [sim clock]

# step three cycles in the default domain
sim step 3

# show clocks
puts [sim clock]

# step 2 more cycles in the default domain
sim step 2

# show clocks
puts [sim clock]

# change to the other (aperiodic) domain
sim clock {mc$CLK_OUT}

# show clocks
puts [sim clock]

# step ten cycles in aperiodic domain
sim step 10

# show clocks
puts [sim clock]

# end of script

