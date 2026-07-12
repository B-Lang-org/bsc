package Bar;

import Foo::*;

(* synthesize *)
module mkBar(Counter);
   Counter inner <- mkFoo;

   method Action bump();
      inner.bump();
   endmethod

   method Bit#(8) value();
      return inner.value();
   endmethod
endmodule

endpackage
