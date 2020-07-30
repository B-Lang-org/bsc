package Buffer;

import Pull :: *;

       
module mkDesign1 (Pull #(Bit #(8)));
    Reg #(Bit #(8)) counter();
    mkReg #(0) the_counter (counter);
    
    method pull();
       actionvalue
         counter <= counter + 1;
         return counter * counter;
       endactionvalue
   endmethod: pull
endmodule : mkDesign1

module mkDesign_Buffer (Pull #(Bit #(8)));
    Pull #(Bit #(8)) src();
    mkDesign1 the_src(src);
    Pull #(Bit #(8)) des();
    buffer #(0, src) the_des(des);
    return des;
endmodule : mkDesign_Buffer

module mkTestbench_Buffer ();
    Pull #(Bit #(8)) dut();
    mkDesign_Buffer the_dut (dut);
    
    Reg #(Bit #(8)) counter();
    mkReg #(0) the_counter (counter);
    
    Reg #(Bit #(8)) counter_buffer();
    mkReg #(0) the_counter_buffer (counter_buffer);
    
    Reg #(Bool) fail();
    mkReg #(False) the_fail (fail);
    
    rule always_fire (True);
        counter <= counter + 1;
        counter_buffer <= counter;
        Bit #(8) data_stream <- dut.pull;
        $display("Pulled Value:%d", data_stream);
        if (counter_buffer * counter_buffer != data_stream)
           fail <= True;
    endrule

    rule endsim (counter_buffer == 15);
        if (fail ) 
           $display("Simulation Fails");
        else
           $display("Simulation Passes");
        $finish(2'b00);
    endrule
endmodule : mkTestbench_Buffer

endpackage : Buffer
