//Incorrect List in the descending_urgency attribute.
//Parser should report an error 

package Incorrect_Attribute_List1;

module mkIncorrect_Attribute_List1();

    Reg#(Bit#(8)) count();
    mkReg#(0) count_r(count);

    rule test_rule_1 (count <=60);
        count <= count + 2;
        $display ("Executing Rule1"); //Should be displayed 15 times
    endrule

    String dummy = "Test";
    (*descending_urgency="test_rule_2, test_rule_1, dummy" *)
    rule test_rule_2 (count >= 30);
        count <= count + 1;
        $display ("Executing Rule2"); //Should be displayed 30 times.
    endrule

    rule endsim (count == 60);
        $finish (2'b00);
    endrule

endmodule : mkIncorrect_Attribute_List1

endpackage : Incorrect_Attribute_List1
