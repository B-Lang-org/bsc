sim cd gcd

# get handles for signals we're interested in
foreach name [list EN_start start_num1 start_num2 RDY_result result the_x the_y] {
  set hdl_of($name) [sim lookup $name]
}

# step and watch values
while {true} {
  if [catch {sim step}] {break}
  puts "---- State at [sim time] ----"
  foreach name [array names hdl_of] {
    set label "$name:"
    set value [sim get $hdl_of($name)]
    puts [format "%-15s %s" $label $value]    
  }
  puts "--------------------"
}
