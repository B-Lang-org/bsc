package HoleBsv;

(* synthesize *)
module mkHoleBsv();
   Reg#(Bit#(8)) r <- mkReg(__);
   rule incr;
      r <= r + __;
   endrule
endmodule

endpackage
