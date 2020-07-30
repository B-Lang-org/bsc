//Signal from Enable to Ready of the same method.
//Should report an error with -verilog flag.

package En2Rdy3;

import FIFO :: *;

interface En2Rdy3Interv;
    method Action start();
    method Bit #(1) rdy_start();
    method Bit #(8) result();
    method Bit #(1) rdy_result();
endinterface

import "BVI" Imported_Verilog = 
    module mkEn2Rdy3v (En2Rdy3Interv);
        method start() enable(En_start);
        method Rdy_start rdy_start();
        method Result result();
        method Rdy_result rdy_result();
        path (En_start, Rdy_start);
    endmodule    

interface En2Rdy3Inter;
    method Action start ();
    method Bit #(8) result();
endinterface

(* synthesize *)
module [Module] mkEn2Rdy3(En2Rdy3Inter);
    
    En2Rdy3Interv dut();
    mkEn2Rdy3v the_dut (dut);
    
    method Action start() if (dut.rdy_start == 1);
        dut.start ();
    endmethod

    method result();
        return (dut.result);
    endmethod
endmodule


endpackage
