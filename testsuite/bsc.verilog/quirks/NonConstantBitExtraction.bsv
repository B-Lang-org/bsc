(* synthesize *)
module sysNonConstantBitExtraction();

   Reg#(Bit#(3)) idx <- mkReg(0);
   Reg#(Bit#(3)) vec <- mkReg('1);

   // M = size of the expression being extracted from
   // N = size of the result of extraction

   rule doDisplay (idx < 3);
     // M > N
     Bit#(2) res1 = vec[idx:0];
     $display("2bit: %b", res1);

     // M < N
     Bit#(4) res2 = vec[idx:0];
     $display("4bit: %b", res2);

     // M == N
     Bit#(3) res3 = vec[idx:0];
     $display("3bit: %b", res3);

     idx <= idx + 1;
   endrule

   rule doFinish (idx == 3);
     $finish(0);
   endrule

endmodule

