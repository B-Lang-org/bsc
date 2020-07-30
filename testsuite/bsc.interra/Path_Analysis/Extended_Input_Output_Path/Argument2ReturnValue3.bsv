//Signal from Argument to Return value of the same method, 
//The combinational loop is completed at the top level
//Uses a Pure Function
//Should report an error with -verilog flag

package Argument2ReturnValue3;

import FIFO :: *;

interface Argument2ReturnValue3Inter;
    method Bit #(8) start (Bit #(8) inp);
endinterface

(* synthesize *)

module mksubsubArgument2ReturnValue3(Argument2ReturnValue3Inter);
    
    method start (inp);
        return (inp);
    endmethod
    
endmodule

(* synthesize *)

module mksubArgument2ReturnValue3(Argument2ReturnValue3Inter);
    
    
    Argument2ReturnValue3Inter dut();
    mksubsubArgument2ReturnValue3 the_dut(dut);
    
    method start (inp);
        return (dut.start (inp));
    endmethod
    
endmodule

(* synthesize *)

module mkArgument2ReturnValue3 ();
    
    Argument2ReturnValue3Inter dut();
    mksubArgument2ReturnValue3 the_dut(dut);
  
    RWire #(Bit #(8)) inwire();
    mkRWire the_inwire (inwire);
    
    rule always_fire;
         inwire.wset (dut.start(unJust (inwire.wget))); 
    endrule

       
endmodule
    

endpackage
