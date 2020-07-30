//5 Conflicting Rules with cyclic descendancy attributes.
//This should report an error.

package Cyclic_Urgency_Five_Rules;

module mkCyclic_Urgency_Five_Rules();

    Reg#(Bit#(8)) count();
    mkReg#(0) count_r(count);

    (*descending_urgency="test_rule_1, test_rule_2" *)
    rule test_rule_1 (count <=60);
        count <= count + 2;
        $display ("Executing Rule1"); 
    endrule

    (*descending_urgency="test_rule_2, test_rule_3" *)
    rule test_rule_2 (count >= 30);
        count <= count + 1;
        $display ("Executing Rule2"); 
    endrule

    (*descending_urgency="test_rule_3, test_rule_1",
      descending_urgency="test_rule_3, test_rule_4" *)
    rule test_rule_3;
        count <= count + 4;
    endrule
 
    (*descending_urgency="test_rule_4, test_rule_1", 
     descending_urgency="test_rule_4, test_rule_5" *)
    rule test_rule_4;
        count <= count + 4;
    endrule

    rule test_rule_5;
        count <= count + 4;
    endrule



    rule endsim (count == 60);
        $finish (2'b00);
    endrule

endmodule : mkCyclic_Urgency_Five_Rules

endpackage : Cyclic_Urgency_Five_Rules
