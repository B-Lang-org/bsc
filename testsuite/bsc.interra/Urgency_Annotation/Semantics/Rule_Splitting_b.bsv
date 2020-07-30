//This package needs to be compiled with -expand-if flag.
//Attribute applied over the module

package Rule_Splitting_b;


interface Test_IFC;
   method Action start ();
   method Bit #(8) result ();
endinterface : Test_IFC


    (* descending_urgency = "test_rule_1, test_rule_2" *)
module mkRule_Splitting_b();

    Reg#(Bit#(8)) count1();
    mkReg#(0) count1_r(count1);

    Reg#(Bit#(8)) count2();
    mkReg#(0) count2_r(count2);

    
    rule test_rule_1 (count1<=10);
        if (count2 <= 4)
        begin
          count2 <= count2 + 1;
          $display ("Executing Rule1a"); //Should be displayed 5 times
        end
        else if (count2 <= 6)
        begin
          $display ("Executing Rule1b"); //Should be displayed 2 times
          count2 <= count2 + 1;
        end
        else if (count2 <= 5)
        begin
          $display ("Executing Rule1c");//Should never be displayed
          count2 <= count2 +1;
          count1 <= 0;
        end
    endrule
    
    rule test_rule_2 (count1 <= 20);
        if (count2 <= 12)
        begin
           count2 <= count2 + 1;
           $display ("Executing Rule2a");//Should be displayed 6 times
        end
        else
        begin
           $display ("Executing Rule2b"); //Should be displayed 10 times
           count1 <= count1 + 1;
        end
    endrule
    

endmodule : mkRule_Splitting_b

endpackage : Rule_Splitting_b
