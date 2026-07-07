sim vcd sysFstSw.vcd
sim step 10
sim fst sysFstSw.fst
sim step 10
puts [sim fst]
sim vcd on
sim step 10
puts [sim vcd]
