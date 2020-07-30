
//Make sure a rule that has a false condition is removed from the list.
//Urgency attribute specified over the module

package Remove_Rules_b;

(*descending_urgency = "test_rule_1, test_rule_2",
  descending_urgency = "test_rule_2, test_rule_3",
  descending_urgency = "test_rule_3, test_rule_1" *)
module mkRemove_Rules_b();

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

    rule test_rule_3 (False);
        count <= count + 1;
        $display ("Executing Rule3");  
    endrule

    rule endsim (count == 100);
        $finish (2'b00);
    endrule

endmodule
   
endpackage
