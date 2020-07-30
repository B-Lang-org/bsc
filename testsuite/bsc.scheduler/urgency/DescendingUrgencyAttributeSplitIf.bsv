
module sysDescendingUrgencyAttributeSplitIf (Empty);

  Reg#(Bool) p();
  mkReg#(True) p_r(p);

  Reg#(Bool) q();
  mkReg#(True) q_r(q);

  Reg#(Bit#(8)) count();
  mkReg#(0) count_r(count);


  rule test_rule_1;
    count <= count + 2;
  endrule
  (* descending_urgency="test_rule_2, test_rule_1" *)
  rule test_rule_2;
    if (p)
      if (q)
        count <= count + 4;
      else
        count <= count + 5;
    else
      count <= count + 3;
  endrule

endmodule

