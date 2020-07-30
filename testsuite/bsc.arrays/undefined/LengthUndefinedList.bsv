(* synthesize *)
module sysLengthUndeterminedList();

 List#(int) l = ?;

 rule test;
   $display(listLength(l));
 endrule

endmodule
