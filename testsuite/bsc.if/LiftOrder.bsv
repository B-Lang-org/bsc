// make sure lifting does not disturb the order of foreign function calls
(* synthesize *)
module sysLiftOrder(Empty);

  Reg#(Bool) b <- mkReg(False);

  Action a1 = b ? $display("True") : $display("False");
  Action a2 = b ? $display("True 2") : $display("False 2");

  rule test;
     a1;
     $display("In middle");
     a2;
     $finish(0);
  endrule

endmodule

