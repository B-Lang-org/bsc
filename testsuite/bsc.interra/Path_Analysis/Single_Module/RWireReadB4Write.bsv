//Should report an error with -verilog flag

package RWireReadB4Write;


interface Inout;
  method Bit #(8) outgate;
endinterface


(* synthesize *)
module mkRWireReadB4Write(Inout);
   
    RWire #(Bit #(8)) x();
    mkRWire the_x (x);
    
    rule flip (unJust (x.wget) >  0);
        x.wset (0);
    endrule

    rule alwaysfire;
        x.wset (1);
    endrule

    method Bit #(8) outgate ();
      Bit #(8) invar = 0;
      if (x.wget matches tagged Just {.y})
       invar = y;
      return invar;
  endmethod


endmodule

endpackage
