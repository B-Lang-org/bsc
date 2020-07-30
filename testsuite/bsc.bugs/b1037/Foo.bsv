package Foo;

`define SIZE 0

import Probe::*;

(* synthesize *)
module sysFoo (Empty);

   Probe#(Bit#(`SIZE)) p <- mkProbe;

   rule r;
       Bit#(`SIZE) x = ?;
      p <= x;
      $display( "Rule fired and finished" ) ;
      $finish(0) ;
   endrule

   
   
endmodule

endpackage: Foo
