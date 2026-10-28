package InternSameNameSub;

// In BSV because Classic has no syntax for naming rules in a scheduling
// attribute.  ra_1 doesn't conflict with rb, so the attribute has no effect
// and ra is chosen over rb by default.  d keeps rb out of the block of
// consecutive rules holding ra_1, so ra_1 is looked up by name in the module.
module mkSubB#(Reg#(Bool) p, Reg#(Bool) q)(Empty);
   Reg#(Bool) c <- mkReg(False);
   rule ra; p <= !q; endrule
   rule ra_1; c <= !c; endrule
   Reg#(Bool) d <- mkReg(False);
   (* descending_urgency = "rb, ra_1" *)
   rule rb; q <= !p; endrule
endmodule

endpackage
