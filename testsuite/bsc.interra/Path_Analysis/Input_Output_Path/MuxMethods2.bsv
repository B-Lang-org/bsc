package MuxMethods2;

interface ArithIO ;
 
    method Action setwire(Bool a);
    method Bit #(8) func1(Bit #(8) a, Bit #(8) b);
    method Bit #(8) func2(Bit #(8) a, Bit #(8) b);
    
endinterface: ArithIO

(* synthesize *)
module mkMuxMethods2(ArithIO);

    RWire #(Bit #(8)) x();
    mkRWire the_x (x);

    method Action setwire(a);
        noAction;
    endmethod
    
    method func1(a, b) ;
        return (a+b);
    endmethod 
    
    method func2(a, b) ; 
        return (a+1);
    endmethod


endmodule

(* synthesize *)
module mkTop(ArithIO);
    
    ArithIO dut();
    mkMuxMethods2 the_dut (dut);

    RWire #(Bool) internal_wire();
    mkRWire the_internal (internal_wire);
   
    method Action setwire (a);
        internal_wire.wset (a);
    endmethod
  
    method func1 (a,b) if (unJust (internal_wire.wget));
        return (dut.func1 (a,b));
    endmethod

    method func2 (a,b) if (!unJust (internal_wire.wget));
        return (dut.func1 (a,b ));
    endmethod

endmodule

endpackage
