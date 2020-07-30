//2 conflicting Rules, with one of them in a submodule that uses
//the synthesis pragma.
//This package should not compile

package Synthesized_Submodule_With_Conflicting_Rules;

interface Test_IFC;
   method Action start ();
   method Bit #(8) result ();
endinterface : Test_IFC

(* synthesize *)
module mkTest_SSWCR(Test_IFC);

    Reg#(Bit#(8)) count();
    mkReg#(0) count_r(count);

    rule test_rule_1 (count <=60);
        count <= count + 2;
        $display ("Executing Rule1"); 
    endrule

    rule test_rule_2 (count > 60 && count < 80);
        count <= count + 1;
        $display ("Executing Rule2");
    endrule

    method Action start;
        count <= count + 5;
    endmethod : start

    method result ();
        return (count);
    endmethod : result

endmodule 

module mkSynthesized_Submodule_With_Conflicting_Rules();
    
     Test_IFC dut ();
     mkTest_SSWCR the_dut (dut);

     (* descending_urgency = "the_dut.test_rule_2, true",
        descending_urgency = "the_dut.test_rule_1, true" *)
     rule true;
         dut.start();
         $display ("Calling Method");  
     endrule

     rule disp;
         $display ("Count = %d", dut.result);
     endrule
      
     rule endsim (dut.result >= 100);
         $finish (2'b00);
     endrule

endmodule : mkSynthesized_Submodule_With_Conflicting_Rules

endpackage : Synthesized_Submodule_With_Conflicting_Rules
