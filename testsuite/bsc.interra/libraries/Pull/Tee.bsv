package Tee;

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

module mkDesign_Tee (Pull #(Bit #(8)));
    function Action f (Bit #(8) indata);
      $display ("Peeking:%d", indata);
    endfunction : f
    Pull #(Bit #(8)) src();
    mkDesign1 the_src(src);
    Pull #(Bit #(8)) des = tee (f, src);
    return des;
endmodule : mkDesign_Tee

module mkTestbench_Tee ();
    Pull #(Bit #(8)) dut();
    mkDesign_Tee the_dut (dut);
    
    Reg #(Bit #(8)) counter();
    mkReg #(0) the_counter (counter);
    
    Reg #(Bool) fail();
    mkReg #(False) the_fail (fail);
    

    rule always_fire (True);
        counter <= counter + 1;
        Bit #(8) data_stream <- dut.pull;
        $display("Pulled Value:%d", data_stream);
        if (counter*counter != data_stream)
           fail <= True;
    endrule

    rule endsim (counter == 15);
        if (fail ) 
           $display("Simulation Fails");
        else
           $display("Simulation Passes");
        $finish(2'b00);
    endrule
endmodule : mkTestbench_Tee

endpackage : Tee
