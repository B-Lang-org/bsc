interface TbIfc;
   (* always_ready *)
   method UInt#(16) num1();
   (* always_ready *)
   method UInt#(16) num2();
   method Action start();

   method Action result(UInt#(16) r);
endinterface

(* synthesize *)
module mkTbGCD(TbIfc);

  Reg#(UInt#(16)) count1 <- mkReg(3);
  Reg#(UInt#(16)) count2 <- mkReg(7);
  Reg#(UInt#(16)) tbresult <- mkReg(0);

  rule done (count2 > 100);
     $finish(0);
  endrule

  method num1 = count1;
  method num2 = count2;
  method Action start();
      count1 <= count1 + 3;
      count2 <= count2 + 2;
  endmethod

  method Action result(UInt#(16) r);
     tbresult <= r;
     $display("result = %d", r);
  endmethod

endmodule
