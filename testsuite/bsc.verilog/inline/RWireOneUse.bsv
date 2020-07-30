// This RWire's wget and whas output ports are only used in one place.
// When the RWire is inlined, the signals for those ports should remain
// in the output Verilog (as inlining will not expose any optimization).

(* synthesize *)
module sysRWireOneUse (Empty);

   Reg#(Bit#(8)) x <- mkRegU;
   Reg#(Bit#(8)) y <- mkRegU;

   RWire#(Bit#(8)) rw <- mkRWire;

   // Give a condition to the setting of the RWire, so that we
   // can see the rw$whas signal in the output Verilog.
   // The condition can't be the rule predicate, though, because
   // then the rwire port disappears as it is just an alias for
   // CAN_FIRE_rule1 (and optimization removed aliases).
   rule rule1;
      if (x > 64)
	 rw.wset(x + y);
   endrule

   rule rule2 (isValid(rw.wget));
      y <= validValue(rw.wget);
   endrule

endmodule

