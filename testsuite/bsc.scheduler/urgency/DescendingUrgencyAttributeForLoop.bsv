import List::*;

module sysDescendingUrgencyAttributeForLoop (Empty);

  List#(Reg#(Bit#(8))) count;
  count <- mapM(constFn(mkReg(0)),upto(1,3));

  for (Integer i = 0; i<3; i = i + 1)
    rule test_rule_2;
      (count[i]) <= (count[i])._read + 2;
    endrule

  (* descending_urgency="test_rule_1, test_rule_2_2, test_rule_2_1, test_rule_2" *)
  rule test_rule_1;
    (count[0]) <= (count[0])._read + 1;
    (count[1]) <= (count[1])._read + 1;
    (count[2]) <= (count[2])._read + 1;
  endrule

endmodule
