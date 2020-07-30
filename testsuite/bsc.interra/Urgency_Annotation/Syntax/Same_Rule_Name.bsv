package Same_Rule_Name;

import Vector :: *;

interface Test_IFC;
   method Action start ();
   method Bit #(8) result ();
endinterface : Test_IFC

(* synthesize *)
module mkSame_Rule_Name(Test_IFC);

    Reg#(Bit#(8)) count();
    mkReg#(0) count_r(count);

 
    Rules r1 = 
    
    rules
    
    
    rule test_rule_1 (count <=10);
        count <= count + 2;
        $display ("Executing Rule1"); 
    endrule
    
    rule test_rule_2 (count <= 20);
        count <= count + 1;
        $display ("Executing Rule2"); 
    endrule
    
    endrules ;

    Rules r2 = rules 

    (* descending_urgency = "test_rule_1_0, test_rule_2_0" *)
    rule test_rule_1 (count <=30);
        count <= count + 2;
        $display ("Executing Rule3"); 
    endrule
    
    rule test_rule_2 (count <= 40);
        count <= count + 1;
        $display ("Executing Rule4"); 
    endrule
    endrules;

    Vector #(2, Rules) my_list = cons (r1, cons (r2, nil));
    addRules (joinRules(my_list));

    method Action start ;
        count <= count + 5;
    endmethod : start
    
    method result ();
        return (count);
    endmethod : result

endmodule 

module mkTestbench_Same_Rule_Name();
    
     Test_IFC dut ();
     mkSame_Rule_Name the_dut (dut);

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

endmodule 

endpackage
