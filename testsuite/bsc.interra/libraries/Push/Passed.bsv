package Passed;

import Push :: *;
import FIFO :: *;

function Bit #(16) square (Bit #(8) in_a);
    return zeroExtend (in_a) * zeroExtend (in_a);
endfunction : square
       

interface Design_IFC;
   method Action push (Bit #(8) in_a);
   method ActionValue #(Bit #(16)) result();
endinterface :Design_IFC
       
module mkDesign_Passed (Design_IFC);

    FIFO #(Bit #(16)) fifo1();
    mkSizedFIFO #(16) the_fifo1(fifo1);

    Push #(Bit #(8)) output_a();
    passed #(square, fifoToPush(fifo1)) the_output_a (output_a);
            
    method push(in_a);
       action
          output_a.push(in_a);
       endaction
   endmethod: push

    method result();
       actionvalue
           fifo1.deq;
           return fifo1.first;
       endactionvalue
    endmethod: result

endmodule : mkDesign_Passed 


module mkTestbench_Passed  ();
    Design_IFC dut();
    mkDesign_Passed the_dut (dut);
    
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
        Bit #(16) result <- dut.result;
        count_out <= count_out + 1;
        $display ("Popped Out Value = %d", result);
        if (result != square (count_out))
            fail <= True;
    endrule
        
  
    rule endsim (count_in == 8'b11111111);
        if (fail ) 
           $display("Simulation Fails");
        else
           $display("Simulation Passes");
        $finish(2'b00);
    endrule
endmodule : mkTestbench_Passed 

endpackage : Passed
