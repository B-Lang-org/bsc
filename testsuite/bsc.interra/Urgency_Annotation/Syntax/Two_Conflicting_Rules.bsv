//2 Conflicting Rules with the descendancy attribute.

package Two_Conflicting_Rules;

module mkTwo_Conflicting_Rules();

    Reg#(Bit#(8)) count();
    mkReg#(0) count_r(count);

    rule test_rule_1 (count <=60);
        count <= count + 2;
        $display ("Executing Rule1"); //Should be displayed 15 times
    endrule

    (*descending_urgency="test_rule_2, test_rule_1" *)
    rule test_rule_2 (count >= 30);
        count <= count + 1;
        $display ("Executing Rule2"); //Should be displayed 30 times.
    endrule

    rule endsim (count == 60);
        $finish (2'b00);
    endrule

endmodule : mkTwo_Conflicting_Rules

endpackage : Two_Conflicting_Rules
