(* synthesize *)
module sysRuleAttributeErrors();

  Reg#(UInt#(13)) a <- mkRegU;
  Reg#(UInt#(13)) b <- mkRegU;

  Rules block1 = 
    rules
      (* descending_urgency="a,b" *)
      rule one;
        a <= a + 1;
      endrule
    endrules;

  addRules(block1);

  Rules block2 = 
    rules
      (* mutually_exclusive="c,d" *)
      rule two;
        b <= b + 1;
      endrule
      (* execution_order="f,g" *)
      rule three;
        a <= a + 2;
        b <= b + 1;
      endrule
    endrules;

   addRules(block2);

   (* conflict_free="a,g" *)
   rule four;
     a <= a - b;
   endrule

endmodule


