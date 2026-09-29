// _dm mint family via -opt-if-mux
(* synthesize *)
(* options = "-opt-if-mux" *)
module sysStableOptIfMux();
   Reg#(Bit#(8)) r <- mkReg(0);
   Reg#(Bool) p <- mkReg(False);
   Reg#(Bool) q <- mkReg(True);
   Reg#(Bool) s <- mkReg(False);
   rule tick;
      r <= (p && q) ? r + 1 : (s ? r + 2 : r + 3);
      p <= !q; q <= !s; s <= !p;
   endrule
endmodule
