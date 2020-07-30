# Test script for the dealing with interface methods

# move into gcd instance
sim cd gcd

# record symbol handles
set EN_start [sim lookup EN_start]
set num1 [sim lookup start_num1]
set num2 [sim lookup start_num2]
set RDY_result [sim lookup RDY_result]
set result [sim lookup result]
set x [sim lookup the_x]
set y [sim lookup the_y]

# step and watch values
while {[sim time] < 1000} {
  sim step
  puts "---- [sim time] ----"
  puts [sim get $EN_start $num1 $num2]
  puts [sim get $RDY_result $result]
  puts [sim get $x $y]
}

# end of script

