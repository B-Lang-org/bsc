interface Ifc;
   interface Clock clk_out;
endinterface

(* synthesize *)
module sysIfc_Clock_Case(Clock c1, Clock c2, Clock c3, Ifc ifc);

   Reg#(Bit#(2)) idx <- mkReg(0);

   Clock c;
   case (idx)
      0 : c = c1;
      1 : c = c2;
      2 : c = c3;
      default : c = noClock;
   endcase

   interface clk_out = c;

endmodule

