//Rule conflicting with a method.

package Method_Rule_Conflict;

interface Test_IFC;
   method Action start ();
   method Bit #(8) result ();
endinterface : Test_IFC

(* synthesize *)
module mkTest_Method_Rule_Conflict(Test_IFC);

    Reg#(Bit#(8)) count();
    mkReg#(0) count_r(count);

    rule test_rule_1 (count <=60);
        count <= count + 2;
        $display ("Executing Rule1"); //Should be displayed exactly 16 times.
    endrule

    rule test_rule_2 (count > 60);
        count <= count + 1;
        $display ("Executing Rule2"); //Should never be displayed .
    endrule

    method Action start if (count >30);
        count <= count + 5;
    endmethod : start

    method result ();
        return (count);
    endmethod : result

endmodule : mkTest_Method_Rule_Conflict

module mkMethod_Rule_Conflict();
    
     Test_IFC dut ();
     mkTest_Method_Rule_Conflict the_dut (dut);

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

endmodule : mkMethod_Rule_Conflict

endpackage : Method_Rule_Conflict
