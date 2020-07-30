//The submodule's rule referred to using the dot notation. Hierarchy of four sub-modules

package Hierarchy4_Dot_Notation_Rule_Name;

interface Test_IFC;
   method Action start ();
   method Bit #(8) result ();
endinterface : Test_IFC

module mkTest1(Test_IFC);

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

endmodule : mkTest1

module mkTest2(Test_IFC);
    Test_IFC dut ();
    mkTest1 the_dut2 (dut);
    
    method Action start;
        dut.start();
    endmethod : start

    method result();
        return (dut.result);
    endmethod : result
endmodule : mkTest2

module mkTest3(Test_IFC);
    Test_IFC dut ();
    mkTest2 the_dut3 (dut);
    
    method Action start;
        dut.start();
    endmethod : start

    method result();
        return (dut.result);
    endmethod : result
endmodule : mkTest3


module mkTest4(Test_IFC);
    Test_IFC dut ();
    mkTest3 the_dut4 (dut);
    
    method Action start;
        dut.start();
    endmethod : start

    method result();
        return (dut.result);
    endmethod : result
endmodule : mkTest4



(* synthesize *)
module mkTestbench_Hierarchy4_Dot_Notation_Rule_Name();
    
     Test_IFC dut ();
     mkTest4 the_dut (dut);

     (* descending_urgency = "the_dut.the_dut4.the_dut3.the_dut2.test_rule_2, true",
        descending_urgency = "the_dut.the_dut4.the_dut3.the_dut2.test_rule_1, true" *)
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

endmodule : mkTestbench_Hierarchy4_Dot_Notation_Rule_Name

endpackage : Hierarchy4_Dot_Notation_Rule_Name
