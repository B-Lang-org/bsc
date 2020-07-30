

module sysDescendingUrgencyAttribute2 (Empty);

  Reg#(Bit#(8)) count();
  mkReg#(0) count_r(count);

  rule test_rule_1;
    count <= count + 2;
  endrule

  (* descending_urgency="test_rule_2, test_rule_1" *)
  rule test_rule_2;
    count <= count + 3;
  endrule

endmodule

