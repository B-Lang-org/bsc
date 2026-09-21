// Fixtures for the -verilog -c codegen mode (.ba -> .v)

(* synthesize *)
module mkGenSub(Reg#(Bit#(8)));
   Reg#(Bit#(8)) rg <- mkReg(0);
   return rg;
endmodule

(* synthesize *)
module mkGenTop(Empty);
   Reg#(Bit#(8)) sub <- mkGenSub;
   rule bump;
      sub <= sub + 1;
   endrule
endmodule

// A module whose elaboration differs by backend (via genC), so its .ba
// records the backend it was elaborated for
(* synthesize *)
module mkGenC(Reg#(Bit#(8)));
   Reg#(Bit#(8)) rg <- mkReg(genC ? 1 : 0);
   return rg;
endmodule
