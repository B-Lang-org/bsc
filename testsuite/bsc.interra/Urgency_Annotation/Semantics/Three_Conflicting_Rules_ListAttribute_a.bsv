
//3 conflicting rules with the desdending_urgency attribute in a list.

package Three_Conflicting_Rules_ListAttribute_a;

module mkThree_Conflicting_Rules_ListAttribute_a();

    Reg #(Bit #(8)) count ();
    mkReg #(0) count_r(count);

    (*descending_urgency = "test_rule_1, test_rule_2, test_rule_3" *)
    
    rule test_rule_1 (count < 20);
        count <= count + 1;
        $display ("Executing Rule1"); //Should be displayed 20 times
    endrule
    
    rule test_rule_2 (count < 40);
        count <= count + 1;
        $display ("Executing Rule2");  //Should be displayed 20 times
    endrule

    rule test_rule_3 (count < 50);
        count <= count + 1;
        $display ("Executing Rule3");  //Should be displayed 10 times
    endrule

    rule endsim (count == 100);
        $finish (2'b00);
    endrule

endmodule
   
endpackage
