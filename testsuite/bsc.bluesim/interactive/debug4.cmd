# show the clock edges at the current simulation time
proc showclk {} {
  set t [sim time]
  set clks [sim clock]
  foreach clk $clks {
    set name [lindex $clk 2]
    set cycles [lindex $clk 7]
    set val [lindex $clk 8]
    set edge_at [lindex $clk 9]
    if {$edge_at == $t} {
       if {$val == 1} then {
       	  puts "/$name ($cycles) at $edge_at"
       } else {
       	  puts "\\$name ($cycles) at $edge_at"
       } 
    }
  }
}

while {true} {
  if [catch {sim nextedge}] {break}
  showclk
}
