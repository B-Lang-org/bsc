interface MyCounter;
   method Action incA;
   method UInt#(32) getA;
   method Action resetA;
endinterface

(* synthesize *)
module mkMyCounter(MyCounter);
   Reg#(UInt#(32)) a <- mkReg(0);
      
   rule clearA(a == 100);
     a <= 0;
   endrule

   method Action incA;
      a <= a + 1;
   endmethod

   method getA = a;

   method Action resetA;
      a <= 0;
   endmethod

endmodule

(* synthesize *)
module sysMECombSched();     
   
   MyCounter mc <- mkMyCounter;
   
   Reg#(Bool) switch <- mkReg(False);
   
   rule flip;
      switch <= !switch;
   endrule
   
   rule r1(switch);
      mc.resetA;
   endrule
   
   (* mutually_exclusive = "r1, r2" *)
   rule r2(!switch);
      mc.incA;
   endrule
   
endmodule

   
   
      
