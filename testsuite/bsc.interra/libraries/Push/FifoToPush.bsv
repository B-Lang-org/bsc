package FifoToPush;

import Push :: *;
import FIFO :: *;


interface Design_IFC;
   method Action push (Bit #(8) in_a);
   method ActionValue #(Bit #(8)) result();
endinterface :Design_IFC
       
module mkDesign_FifoToPush (Design_IFC);

    FIFO #(Bit #(8)) fifo1();
    mkSizedFIFO #(8) the_fifo1(fifo1);

    Push #(Bit #(8)) output_a = fifoToPush (fifo1);
            
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

endmodule : mkDesign_FifoToPush


module mkTestbench_FifoToPush ();
    Design_IFC dut();
    mkDesign_FifoToPush the_dut (dut);
    
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
        if (result != count_out)
            fail <= True;
    endrule
        
  
    rule endsim (count_in == 8'b11111111);
        if (fail ) 
           $display("Simulation Fails");
        else
           $display("Simulation Passes");
        $finish(2'b00);
    endrule
endmodule : mkTestbench_FifoToPush

endpackage : FifoToPush
