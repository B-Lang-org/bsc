//2 Rules conflicting with each other and also with a method.
//The descending_urgency attribute is applied over the module..

package Method_Rules_Conflict_b;

interface Test_IFC;
   method Action start ();
   method Bit #(8) result ();
endinterface : Test_IFC

(* synthesize ,
   descending_urgency = "test_rule_2, test_rule_1" *)
module mkTest_Method_Rules_Conflict_b(Test_IFC);

    Reg#(Bit#(8)) count();
    mkReg#(0) count_r(count);

    rule test_rule_1 (count <=60);
        count <= count + 2;
        $display ("Executing Rule1"); //Should be displayed exactly 8 times.
    endrule
    
    rule test_rule_2 (count >= 15);
        count <= count + 1;
        $display ("Executing Rule2"); //Should be displayed exactly 15 times.
    endrule

    method Action start if (count >30);
        count <= count + 5;
    endmethod : start

    method result ();
        return (count);
    endmethod : result

endmodule : mkTest_Method_Rules_Conflict_b

module mkMethod_Rules_Conflict_b();
    
     Test_IFC dut ();
     mkTest_Method_Rules_Conflict_b the_dut (dut);

     rule true;
         dut.start();
         $display ("Calling Method"); //Should be displayed exactly 14 times 
     endrule

     rule disp;
         $display ("Count = %d", dut.result);
     endrule
      
     rule endsim (dut.result >= 100);
         $finish (2'b00);
     endrule

endmodule : mkMethod_Rules_Conflict_b

endpackage : Method_Rules_Conflict_b
