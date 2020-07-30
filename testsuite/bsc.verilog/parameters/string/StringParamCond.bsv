interface Sub;
  method Action tick;
endinterface

(* synthesize *)
module mkStringParamCondSub#(parameter String a, parameter String b)(Sub);

  Reg#(UInt#(17)) r <- mkReg(0);

  String cond = (r == 0) ? a : b;

  rule test;
    $display("r %0d",r);
    $display(cond,UInt#(5)'(17));
    if (r == 4) $finish(0);     
  endrule

  method Action tick;
     r <= r + 1;
  endmethod

endmodule

(* synthesize *)
module sysStringParamCond();

  Sub foo <- mkStringParamCondSub("This is seventeen in decimal: ", "This is seventeen in hex: %h");
  
  rule tick;
    foo.tick;
  endrule

endmodule

