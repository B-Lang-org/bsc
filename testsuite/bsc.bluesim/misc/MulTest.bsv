Int#(43) a = 43'b0000000000000000000000011111111011101100000;
Int#(23) b = 23'b00101001110010111100000;

// This testcase showed a bug in which C++ overload resolution and promotion
// caused the wrong WideData constructor to be called.

(* synthesize *)
module sysMulTest();
   
   Reg#(Int#(43)) r <- mkReg(a);
   Reg#(Int#(23)) s <- mkReg(b);

   Int#(66) prod1 = signedMul(r,s); 
   Int#(66) prod2 = signedMul(s,r);
   
   Reg#(UInt#(8)) count <- mkReg(0);
   
   rule test;
      $display("r = %0d", r);
      $display("s = %0d", s);
      $display("r * s = %0d",prod1);
      $display("s * r = %0d",prod2);
      count <= count + 1;
   endrule

   rule done (count > 1);
      $finish(0);
   endrule
   
endmodule
