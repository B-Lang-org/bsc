// Module that divides a signal by three.
// Needs combinational feedback
// RWire.wset and RWire.wget are used in a single rule.
// Should report an error with -verilog flag
// Cycle from argument of a method to its return value

package ArgMethod2ReturnValue2;

import GetPut :: *;

(* synthesize *)
module mkArgMethod2ReturnValue2 (Put #(Bool));
    Reg #(Bool) signal();
    mkReg #(False) the_signal (signal);

    Reg #(Bool) out_signal();
    mkReg #(False) the_out_signal (out_signal);
    
    Reg #(Bool) flopA();
    mkReg #(False) the_flopA (flopA);
    
    Reg #(Bool) flopB();
    mkReg #(False) the_flopB (flopB);

    RWire #(Bool) combout();
    mkRWire the_combout (combout);
    
    RWire #(Bool) inK();
    mkRWire the_inK (inK);
    
    rule setflopB;
       flopB <= flopA;
    endrule

    rule setflopA;
       flopA <= unJust(combout.wget);
    endrule

    rule setcombout;
       Bool temp = ! (flopA || flopB ) ;
       combout.wset (temp);
    endrule

    rule setinK;
       Maybe #(Bool) t1a = inK.wget;
       Bool t1;
       if (t1a matches tagged Just {.x})
          t1 = x;
       else
          t1 = False;
       Bool t2 = (signal || !flopB) && (flopA || t1);
       inK.wset (t2);
    endrule

    rule setout_signal;
        out_signal <= unJust (inK.wget);
    endrule
    
    method Action put (in1);
        signal <= in1;
    endmethod

endmodule


endpackage
