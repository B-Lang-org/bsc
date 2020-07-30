
(* synthesize *)
module sysRuleNeverFires(Empty);
  Reg#(Bit#(32)) r();
  mkRegU the_r(r);

  rule always_fires
   (True); r <= r + 2;
  endrule: always_fires

  rule never_fires
   (True); r <= r + 1;
  endrule: never_fires

endmodule: sysRuleNeverFires
