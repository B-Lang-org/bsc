
//6 conflicting rules with the desdending_urgency attribute in a list.
//Descending Attribute applied over the module

package Six_Conflicting_Rules_ListAttribute_b;

(*descending_urgency = "test_rule_1, test_rule_2, test_rule_3, test_rule_4, test_rule_5, test_rule_6 " *)
module mkSix_Conflicting_Rules_ListAttribute_b();

    Reg #(Bit #(8)) count ();
    mkReg #(0) count_r(count);

    
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
    
    rule test_rule_4 (count < 60);
        count <= count + 1;
        $display ("Executing Rule4");  //Should be displayed 10 times
    endrule
    
    rule test_rule_5 (count < 70);
        count <= count + 1;
        $display ("Executing Rule5");  //Should be displayed 10 times
    endrule

    rule test_rule_6 (count < 80);
        count <= count + 1;
        $display ("Executing Rule6");  //Should be displayed 10 times
    endrule



    rule endsim (count == 100);
        $finish (2'b00);
    endrule

endmodule
   
endpackage
