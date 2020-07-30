package Nested_Rules;

module mkNested_Rules();

    Reg#(Bit#(8)) count();
    mkReg#(0) count_r(count);

    (* descending_urgency = "test_rule_1_test_rule_1a, test_rule_1_test_rule_1b" *)
    rule test_rule_1 (count <=60);
      rule test_rule_1a (count <= 30);
        count <= count + 1;
      endrule
      rule test_rule_1b (count <= 60);
        count <= count + 2;
      endrule
    endrule
    
endmodule : mkNested_Rules

endpackage : Nested_Rules


