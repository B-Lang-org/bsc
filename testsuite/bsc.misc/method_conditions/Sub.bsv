interface Ifc;
   method Action am1(Bit#(8) x);
   method Action am2();
   method ActionValue#(Bit#(8)) avm1(Bit#(8) x);
   method ActionValue#(Bit#(8)) avm2();
   method Bit#(8) vm1(Bit#(8) x);
   method Bit#(8) vm2();
endinterface

(* synthesize *)
module mkUserSub (Ifc);
   // Need to make sure that the RDY signals are not constant True
   Reg#(Bool) rdy <- mkReg(True);

   method am1(x)  if (rdy) = noAction;
   method am2()   if (rdy) = noAction;
   method avm1(x) if (rdy) = actionvalue return(?); endactionvalue;
   method avm2()  if (rdy) = actionvalue return(?); endactionvalue;
   method vm1(x)  if (rdy) = ?;
   method vm2()   if (rdy) = ?;
endmodule

import "BVI"
module mkBVISub (Ifc);
   method       am1  (IN1) enable(EN1) ready(RDY1);
   method       am2  ()    enable(EN2) ready(RDY2);
   method OUT1  avm1 (IN2) enable(EN3) ready(RDY3);
   method OUT2  avm2 ()    enable(EN4) ready(RDY4);
   method OUT3  vm1  (IN3)             ready(RDY5);
   method OUT4  vm2  ()                ready(RDY6);

   schedule am1 C am1;
   schedule am2 C am2;
   schedule avm1 C avm1;
   schedule avm2 C avm2;
   schedule (vm1, vm2) CF (vm1, vm2);
   schedule am1 CF (am2, avm1, avm2);
   schedule am2 CF (avm1, avm2);
   schedule avm1 CF avm2;
   schedule (vm1, vm2) SB (am1, am2, avm1, avm2);
endmodule

