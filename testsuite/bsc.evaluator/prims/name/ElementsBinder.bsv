module mkEBSub(Empty);
   Reg#(Bool) r <- mkReg(False);
endmodule

module mkEBSub2(Empty);
   Reg#(Bool) q <- mkReg(False);
   rule upd;
      q <= !q;
   endrule
endmodule

module mkEBInner(Empty);
   Reg#(Bool) x <- mkReg(False);
   Empty _elements <- mkEBSub;
   Empty s <- mkEBSub2;
   (* descending_urgency = "tick,s.upd" *)
   rule tick;
      x <= !x;
   endrule
endmodule

(* synthesize *)
module sysElementsBinder(Empty);
   Empty i <- mkEBInner;
endmodule
