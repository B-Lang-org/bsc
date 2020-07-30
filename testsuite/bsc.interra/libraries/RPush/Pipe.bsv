package Pipe;

import RPush :: *;
import Push :: *;
import FIFO :: *;

function  Bit #(8) shift (Nat a, Bit #(8) b);
    return (b << a);
endfunction

interface MkDesign_IFC;
    method Action put (Bit #(8) invalue);
    method Action clr ();
    method ActionValue #(Bit#(8)) get;
endinterface : MkDesign_IFC

//(* synthesize *)
module mkDesign_Pipe (MkDesign_IFC);

    FIFO #(Bit #(8)) a0 <- mkFIFO ;
    RPush #(Bit #(8)) push_a0 = fifoToRPush (a0);
    
    RPush #(Bit #(8)) shifter();
    pipe #(RPush :: buffered (shift (2)), RPush :: buffered (shift (1), push_a0)) the_shifter (shifter);

    method put (invalue);
       action
        shifter.push (invalue);
       endaction
    endmethod : put
    
    method clr ();
       action
        shifter.clear ();
       endaction
    endmethod : clr

    method get ();
      actionvalue
        a0.deq();
        return a0.first();
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

     rule always_fire2 (counter <= 8);
         Bit #(8) value_in=0;
         case (counter)
         0 : value_in = 5;
         1 : value_in = 20;
         2 : value_in = 50;
         3 : value_in = 82;
         4 : value_in = 106;
         5 : value_in = 48;
         6 : value_in = 79;
         7 : value_in = 38;
         8 : value_in = 42;
         endcase
         if (counter !=4)
         begin
             dut.put(value_in);
             $display ("Clock Cycle Number = %d, Pushing Value = %d", counter, value_in);
         end
         else
         begin
             dut.clr();
             $display ("Clock Cycle Number = %d, Clearing Pipeline.", counter);
         end
    endrule

    rule always_fire3 (True);
         count_in <= count_in + 1;
         Bit #(8) value_out <- dut.get();
         Bit #(8) expected_value=0;
         
         case (count_in)
         0 : expected_value = 5 << 3;
         1 : expected_value = 20 << 3;
       //  2 : expected_value = 50 << 3;
       //  3 : expected_value = 82 << 3;
         2 : expected_value = 48 << 3;
         3 : expected_value = 79 << 3;
         4 : expected_value = 38 << 3;
         5 : expected_value = 42 << 3;
         endcase
        
         $display ("Clock Cycle Number = %d, Value Got = %d, Expected Value = %d", counter, value_out, expected_value);

         if (counter > 2 && expected_value != value_out)
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
