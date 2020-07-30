//Signal from Enable to Ready, both methods are then called in the 
//separate rules, with wrong urgency order.
//Should report an error with -verilog flag

package En2Rdy2;

import FIFO :: *;

interface En2Rdy2Interv;
    method Action start();
    method Bit #(8) result();
    method Bit #(1) rdy_result();
endinterface

import "BVI" Imported_Verilog =
    module mksubEn2Rdy2v (En2Rdy2Interv);
      method start() enable(En_start);
      method Result result();
      method Rdy_result rdy_result();
      path (En_start, Rdy_result);
      schedule (result, rdy_result) CF (result, rdy_result);
      schedule start SBR rdy_result;   
    endmodule


interface En2Rdy2Inter;
    method Action start ();
    method Bit #(8) result();
endinterface

(* synthesize *)
module [Module] mksubEn2Rdy2(En2Rdy2Inter);

    En2Rdy2Interv dut();
    mksubEn2Rdy2v the_dut (dut);
    
    method Action start ();
        dut.start;
    endmethod
    
    method result if (dut.rdy_result == 1);
        return (dut.result);
    endmethod
   
endmodule

(* synthesize,
   descending_urgency = "fire2, fire1" *)
module [Module] mkEn2Rdy2 ();
    
    En2Rdy2Inter dut();
    mksubEn2Rdy2 the_dut(dut);
   
    rule fire1;
        dut.start;
    endrule

    rule fire2;
        Bit #(8) temp = dut.result();
        $display ("Temp = %d", temp);
    endrule
       
endmodule
    

endpackage
