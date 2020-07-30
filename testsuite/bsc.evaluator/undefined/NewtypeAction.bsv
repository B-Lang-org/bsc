typedef union tagged 
  { Action MyAction; } MyAction;

(* synthesize *)
module sysNewtypeAction();

  MyAction m1 = tagged MyAction ($display("m1"));
  MyAction m2 = ?;

  Reg#(Bool) b <- mkReg(False);

  MyAction m = b ? m1 : m2;
 
  rule test(m matches tagged MyAction .a);
    a;
    b <= !b;
    if (b) $finish(0);
  endrule

endmodule
