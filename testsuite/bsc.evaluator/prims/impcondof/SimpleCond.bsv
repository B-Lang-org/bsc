interface Test;
   method Action test(Bit#(32) v);
   method Bit#(32) test2(Bit#(32) v);
endinterface

module mkTest(Test);
   Reg#(Bool) r <- mkReg(True);
   Reg#(Bool) r2 <- mkReg(True);
   
   rule flip;
      r <= !r;
      if(!r) r2 <= !r2;
   endrule
   
   method Action test(v) if(r);
   endmethod
   
   method test2(v) if(r2);
      return(v);
   endmethod
   
endmodule

function String showBool(Bool b);
   return(b ? "True" : "False");
endfunction

(* synthesize *)
module sysSimpleCond();
   
   Test dut <- mkTest;

   Bool cond = impCondOf(dut.test);
   Bool cond2 = impCondOf(dut.test2);
   
   rule check;
      $display("cond: ", showBool(cond));
      $display("cond2: ", showBool(cond2));
      if(!cond && !cond2) $finish(0);
   endrule
   
endmodule
