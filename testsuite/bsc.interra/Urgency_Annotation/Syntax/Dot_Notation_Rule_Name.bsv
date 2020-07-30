//The submodule's rule referred to using the dot notation

package Dot_Notation_Rule_Name;

interface Test_IFC;
   method Action start ();
   method Bit #(8) result ();
endinterface : Test_IFC

module mkTest_Dot_Rule_Name(Test_IFC);

    Reg#(Bit#(8)) count();
    mkReg#(0) count_r(count);

    rule test_rule_1 (count <=60);
        count <= count + 2;
        $display ("Executing Rule1"); //Should be displayed exactly 31 times.
    endrule

    rule test_rule_2 (count > 60 && count < 80);
        count <= count + 1;
        $display ("Executing Rule2"); //Should be displayed 18 times.
    endrule

    method Action start;
        count <= count + 5;
    endmethod : start

    method result ();
        return (count);
    endmethod : result

endmodule : mkTest_Dot_Rule_Name

module mkDot_Notation_Rule_Name();
    
     Test_IFC dut ();
     mkTest_Dot_Rule_Name the_dut (dut);

     (* descending_urgency = "the_dut.test_rule_2, true",
        descending_urgency = "the_dut.test_rule_1, true" *)
     rule true;
         dut.start();
         $display ("Calling Method");  //Should be displayed 4 times.
     endrule

     rule disp;
         $display ("Count = %d", dut.result);
     endrule
      
     rule endsim (dut.result >= 100);
         $finish (2'b00);
     endrule

endmodule : mkDot_Notation_Rule_Name

endpackage : Dot_Notation_Rule_Name
