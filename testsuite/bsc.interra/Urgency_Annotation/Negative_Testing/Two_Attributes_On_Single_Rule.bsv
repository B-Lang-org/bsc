//2 attributes on a single rule.
// should not give an error; consequent attributes should be treated
// as if they had been separated with a comma in the same attribute

package Two_Attributes_On_Single_Rule;

module mkTwo_Attributes_On_Single_Rule();

    Reg#(Bit#(8)) count();
    mkReg#(0) count_r(count);

    rule test_rule_1 (count <=60);
        count <= count + 2;
        $display ("Executing Rule1"); //Should be displayed 15 times
    endrule

    (*descending_urgency="test_rule_2, test_rule_1" *)
    (*descending_urgency="test_rule_2, endsim" *)
    rule test_rule_2 (count >= 30);
        count <= count + 1;
        $display ("Executing Rule2"); //Should be displayed 30 times.
    endrule

    rule endsim (count == 60);
        $finish (2'b00);
    endrule

endmodule : mkTwo_Attributes_On_Single_Rule

endpackage : Two_Attributes_On_Single_Rule
