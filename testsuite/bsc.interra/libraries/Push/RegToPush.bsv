package RegToPush;

import Push :: *;


interface Design_IFC;
   method Action push (Bit #(8) in_a);
   method ActionValue #(Bit #(8)) result();
endinterface :Design_IFC
       
module mkDesign_RegToPush (Design_IFC);

    Reg #(Bit #(8)) reg1();
    mkReg #(0) the_reg1(reg1);

    Push #(Bit #(8)) output_a = regToPush (reg1);
            
    method push(in_a);
       action
          output_a.push(in_a);
       endaction
   endmethod: push

    method result();
       actionvalue
           noAction;
           return reg1;
       endactionvalue
    endmethod: result

endmodule : mkDesign_RegToPush


module mkTestbench_RegToPush ();
    Design_IFC dut();
    mkDesign_RegToPush the_dut (dut);
    
    Reg #(Bit #(8)) count_in();
    mkReg #(0) the_count_in (count_in);
    
    Reg #(Bit #(8)) count_out();
    mkReg #(0) the_count_out (count_out);
    
    Reg #(Bool) fail();
    mkReg #(False) the_fail (fail);
    
    rule always_push (True);
        count_in <= count_in + 1;
        dut.push (count_in);
        $display ("Count_in = %d", count_in);
    endrule

    rule always_pop (True);
        Bit #(8) result <- dut.result;
        count_out <= count_out + 1;
        $display ("Popped Out Value = %d", result);
        if (result != count_out-1 && count_out >=1)
            fail <= True;
    endrule
        
  
    rule endsim (count_in == 8'b11111111);
        if (fail ) 
           $display("Simulation Fails");
        else
           $display("Simulation Passes");
        $finish(2'b00);
    endrule
endmodule : mkTestbench_RegToPush

endpackage : RegToPush
