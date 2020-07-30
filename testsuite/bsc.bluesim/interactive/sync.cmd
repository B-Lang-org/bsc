# Test script for the sync command
# This is making sure that calling sync when there is no
# simulation active is still safe.  There is a separate
# test for the functionality of sync with an active simulation.

# step one cycle
sim step

# call sync (unnecessarily)
sim sync

# step ten cycles
sim step 10

# end of script

