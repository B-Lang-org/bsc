(* synthesize *)
module sysTestEnableFail();
   Reg#(Bool) b <- mkReg(True);

   // the EN for this will be not constant True
   Wire#(Bool) w1 <- mkBypassWire;
   // the EN for this will be constant False
   //Wire#(Bool) w2 <- mkBypassWire;
   // a submodule to test multiple methods in the same warning
   SubIfc i <- mkSub;
   
   rule r (b);
      w1 <= True;
   endrule
      
   rule r2 (b);
      i.m1;
      i.m2;
   endrule
endmodule

interface SubIfc;
   method Action m1();
   method Action m2();
endinterface

(* synthesize *)
(* always_enabled *)
module mkSub(SubIfc);
   Reg#(Bool) r1 <- mkRegU;
   Reg#(Bool) r2 <- mkRegU;

   method m1 = r1._write(True);
   method m2 = r2._write(True);
endmodule

