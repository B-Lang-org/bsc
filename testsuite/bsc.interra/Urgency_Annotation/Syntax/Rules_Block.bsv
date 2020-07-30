package Rules_Block;


(* synthesize *)
module mkRules_Block();

    Reg#(Bit#(8)) count();
    mkReg#(0) count_r(count);

 
    Rules r1 = 
    
    (* descending_urgency = "test_rule_1, test_rule_2" *)
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


endmodule : mkRules_Block
endpackage : Rules_Block

