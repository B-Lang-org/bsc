//In the sub-module, signal from Enable of one method 
//goes through combinational logic to ReturnValue of the same method.
//In the toplevel module, a path is created from the return value
//to the enable signal
//Should report an error with -verilog flag

package En2ReturnValue2;

import FIFO :: *;

interface En2ReturnValue2Interv;
   method Action start();
   method Bit #(8) result();
endinterface

import "BVI" Imported_Verilog = 
   module mkEn2ReturnValue2v (En2ReturnValue2Interv);
       method start() enable(En_start);
       method Result result();
       path (En_start, Result);
       schedule start SB result;
   endmodule
   
interface En2ReturnValue2Inter;
    method ActionValue #(Bit #(8)) start ();
endinterface


(* synthesize *)
module [Module] mksubEn2ReturnValue2(En2ReturnValue2Inter);
    
    En2ReturnValue2Interv dut();
    mkEn2ReturnValue2v the_dut(dut);
    
    method start;
     actionvalue
        dut.start;
        return (dut.result);
     endactionvalue
    endmethod
    
   
endmodule

(* synthesize *)
module mkEn2ReturnValue2 ();
    
    En2ReturnValue2Inter dut();
    mksubEn2ReturnValue2 the_dut(dut);
  

    RWire #(Bit #(8)) inwire();
    mkRWire the_inwire (inwire);
    
    rule fire (inwire.wget matches tagged Just {.y});
       Bit #(8) temp <- dut.start();
       inwire.wset (temp);
    endrule
       
endmodule
    

endpackage
