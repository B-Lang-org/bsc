package Bind;

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

module mkDesign2 #(Pull #(Bit #(8)) indata) (Pull #(Bit #(4)));
    method pull();
       actionvalue
           Bit #(8) temp <- indata.pull;
           return temp [3:0];
       endactionvalue
    endmethod: pull
endmodule : mkDesign2

module mkDesign_Bind (Pull #(Bit #(4)));
    Pull #(Bit #(4)) des();
    bind #(mkDesign1, mkDesign2) the_des(des);
    return des;
endmodule : mkDesign_Bind

module mkTestbench_Bind ();
    Pull #(Bit #(4)) dut();
    mkDesign_Bind the_dut (dut);
    
    Reg #(Bit #(4)) counter();
    mkReg #(0) the_counter (counter);
    
    Reg #(Bool) fail();
    mkReg #(False) the_fail (fail);
    
    rule always_fire (True);
        counter <= counter + 1;
        Bit #(4) data_stream <- dut.pull;
        $display("Pulled Value:%d", data_stream);
        if (counter * counter != data_stream)
           fail <= True;
    endrule

    rule endsim (counter == 15);
        if (fail ) 
           $display("Simulation Fails");
        else
           $display("Simulation Passes");
        $finish(2'b00);
    endrule
endmodule : mkTestbench_Bind

endpackage : Bind
