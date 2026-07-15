// Test module arguments: a parameter is not a port at all; a port
// argument feeding only a register D_IN is "reg"; a port argument
// with no hardware use is "unused".

interface APkgProps_Args;
   method Bit#(8) get();
endinterface

(* synthesize *)
module sysAPkgProps_Args #(parameter Bit#(4) cfg,
                           Bit#(8) in_r,
                           Bit#(8) in_u)
                          (APkgProps_Args);
   Reg#(Bit#(8)) r <- mkRegU;

   rule capture;
      r <= in_r;
   endrule

   method get = r;
endmodule
