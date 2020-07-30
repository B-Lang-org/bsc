
//Make sure a rule that has a false condition is removed from the list.

package Remove_Rules_a;

module mkRemove_Rules_a();

    Reg #(Bit #(8)) count ();
    mkReg #(0) count_r(count);

    (*descending_urgency = "test_rule_1, test_rule_2" *)
    
    rule test_rule_1 (count < 20);
        count <= count + 1;
        $display ("Executing Rule1"); //Should be displayed 20 times
    endrule
    
    (*descending_urgency = "test_rule_2, test_rule_3" *)
    rule test_rule_2 (count < 40);
        count <= count + 1;
        $display ("Executing Rule2");  //Should be displayed 20 times
    endrule

    (*descending_urgency = "test_rule_3, test_rule_1" *)
    rule test_rule_3 (False);
        count <= count + 1;
        $display ("Executing Rule3");  
    endrule

    rule endsim (count == 100);
        $finish (2'b00);
    endrule

endmodule
   
endpackage
