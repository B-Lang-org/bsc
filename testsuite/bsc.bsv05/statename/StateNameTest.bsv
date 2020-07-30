export sysStateNameTest;

(* synthesize *)
module sysStateNameTest(Empty);
   Reg#(Bit#(16)) a();
   mkReg#(11) b(a);
endmodule 
