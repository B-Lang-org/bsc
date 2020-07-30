(* synthesize *)
module sysUpdateUndefinedList();

  List#(int) l = ?;

  for(Integer i = 0; i < 4; i = i + 1)
    l[i] = fromInteger(i);

  rule test;
    $display(l[0]);
  endrule
 
endmodule