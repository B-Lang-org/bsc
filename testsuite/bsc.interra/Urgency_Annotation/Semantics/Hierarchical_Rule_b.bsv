//Two conflicting rules, with exactly one of them in a sub-module
//Attribute on a module.

package Hierarchical_Rule_b;

interface Test_IFC;
   method Action start ();
   method Bit #(8) result ();
endinterface : Test_IFC

module mkTest_Hierarchy_Rule_b(Test_IFC);

    Reg#(Bit#(8)) count();
    mkReg#(0) count_r(count);

    rule test_rule_1 (count <=60);
        count <= count + 2;
        $display ("Executing Rule1"); //Should be displayed exactly 31 times.
    endrule

    method Action start;
        count <= count + 5;
    endmethod : start

    method result ();
        return (count);
    endmethod : result

endmodule : mkTest_Hierarchy_Rule_b

(* descending_urgency = "the_dut.test_rule_1, true" *)
module mkHierarchical_Rule_b();
    
     Test_IFC dut ();
     mkTest_Hierarchy_Rule_b the_dut (dut);

     
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

endmodule : mkHierarchical_Rule_b

endpackage : Hierarchical_Rule_b
