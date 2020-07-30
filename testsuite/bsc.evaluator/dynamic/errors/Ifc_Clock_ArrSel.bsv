interface Ifc;
   interface Clock clk_out;
endinterface

(* synthesize *)
module sysIfc_Clock_If(Clock c1, Clock c2, Clock c3, Ifc ifc);

   Reg#(Bit#(2)) idx <- mkReg(0);

   Clock cs[4];
   cs[0] = c1;
   cs[1] = c2;
   cs[2] = c3;
   cs[3] = noClock;

   interface clk_out = cs[idx];

endmodule

