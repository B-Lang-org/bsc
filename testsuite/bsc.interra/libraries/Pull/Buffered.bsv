package Buffered;

import Pull :: *;

function Bit #(8) f (Bit #(8) in_data);
    Bit #(8) sqrt;
    case (in_data)
      0 : sqrt = 0;
      1 : sqrt = 1;
      4 : sqrt = 2;
      9 : sqrt = 3;
      16 : sqrt = 4;
      25 : sqrt = 5;
      36 : sqrt = 6;
      49 : sqrt = 7;
      64 : sqrt = 8;
      81 : sqrt = 9;
      100 : sqrt = 10;
      121 : sqrt = 11;
      144 : sqrt = 12;
      169 : sqrt = 13;
      196 : sqrt = 14;
      225 : sqrt = 15;
      default: sqrt = 16;
      endcase
    return sqrt;
endfunction : f
       

       
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

module mkDesign_Buffered (Pull #(Bit #(8)));
    Pull #(Bit #(8)) src();
    mkDesign1 the_src(src);
    Pull #(Bit #(8)) des();
    buffered #(f, src) the_des(des);
    return des;
endmodule : mkDesign_Buffered

module mkTestbench_Buffered ();
    Pull #(Bit #(8)) dut();
    mkDesign_Buffered the_dut (dut);
    
    Reg #(Bit #(8)) counter_buffered();
    mkReg #(0) the_counter_buffered (counter_buffered);
    
    Reg #(Bit #(8)) counter();
    mkReg #(0) the_counter (counter);
    
    Reg #(Bool) fail();
    mkReg #(False) the_fail (fail);
    
    rule always_fire (True);
        counter <= counter + 1;
        counter_buffered <= counter;
        Bit #(8) data_stream <- dut.pull;
        $display("Pulled Value:%d", data_stream);
        if (counter_buffered != data_stream && counter > 0) //Init Value should be ignored
           fail <= True;
    endrule

    rule endsim (counter == 15);
        if (fail ) 
           $display("Simulation Fails");
        else
           $display("Simulation Passes");
        $finish(2'b00);
    endrule
endmodule : mkTestbench_Buffered

endpackage : Buffered
