//Method name in an attribute list.
//Should report a proper error.

package Method_Name_in_Attribute;

interface Test_IFC;
    method Action start;
endinterface

module mkMethod_Name_in_Attribute(Test_IFC);

    Reg#(Bit#(8)) count();
    mkReg#(0) count_r(count);

    (*descending_urgency="test_rule_1, test_rule_2" *)
    rule test_rule_1 (count <=60);
        count <= count + 2;
        $display ("Executing Rule1"); //Should be displayed 15 times
    endrule

    (*descending_urgency="test_rule_2, start" *)
    rule test_rule_2 (count >= 30);
        count <= count + 1;
        $display ("Executing Rule2"); //Should be displayed 30 times.
    endrule

    rule endsim (count == 60);
        $finish (2'b00);
    endrule

    method Action start;
        count <= count + 1;
    endmethod

endmodule : mkMethod_Name_in_Attribute

endpackage : Method_Name_in_Attribute
