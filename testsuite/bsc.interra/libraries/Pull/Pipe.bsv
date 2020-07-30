package Pipe;

import Pull :: *;
import FIFO :: *;

function  Bit #(8) shift (Nat a, Bit #(8) b);
    return (b << a);
endfunction

interface MkDesign_IFC;
    method ActionValue #(Bit#(8)) get;
endinterface : MkDesign_IFC

module mkDesign1 (Pull #(Bit #(8)));
    Reg #(Bit #(8)) counter();
    mkReg #(0) the_counter (counter);
    
    method pull();
       actionvalue
         counter <= counter + 1;
         return counter ;
       endactionvalue
   endmethod: pull
endmodule : mkDesign1


//(* synthesize *)
module mkDesign_Pipe(MkDesign_IFC);

    FIFO #(Bit #(8)) a0 <- mkFIFO ;
    Pull #(Bit #(8)) pull_a0 <- mkDesign1;


    Pull #(Bit #(8)) shifter();
    pipe #(buffered (shift(1), pull_a0),buffered (shift (2))) the_shifter (shifter);


    method get ();
      actionvalue
        Bit #(8) first <- shifter.pull;
        return first;
      endactionvalue
    endmethod : get

endmodule : mkDesign_Pipe

module mkTestbench_Pipe ();
   
     MkDesign_IFC dut();
     mkDesign_Pipe the_dut (dut);

     Reg #(Bit #(8)) counter <- mkReg (0);
     Reg #(Bit #(8)) count_in <- mkReg (0);
     Reg #(Bool) fail <- mkReg (False);

     rule always_fire1 (True);
         counter <= counter + 1;
     endrule

    rule always_fire2 (True);
         count_in <= count_in + 1;
         Bit #(8) value_out <- dut.get();
         Bit #(8) expected_value = (count_in-2) * 8;
         
         $display ("Clock Cycle Number = %d, Value Got = %d, Expected Value = %d", counter, value_out, expected_value);

         if (count_in > 1 && expected_value != value_out)
            fail <= True;
         
    endrule

    rule end_sim (counter == 20);
         if (fail)
             $display ("Simulation Fails");
         else
             $display ("Simulation Passes");
         $finish (2'b00);
    endrule
       

endmodule : mkTestbench_Pipe 
          
     

endpackage : Pipe
