
interface IfcIdFnAV#(type b) ;
   method ActionValue#(a) idfn (a x) ;
//   method Action idfn2 (a x) ;
endinterface

`define testBVI 1
`ifndef testBVI
 
(* synthesize *)
module mkFoo ( IfcIdFnAV#(int) );
   method ActionValue#(int) idfn( x ) ;
      return x + 1 ;
   endmethod
endmodule

`else
import "BVI" RWire =
   module mkIdFnAVRW (IfcIdFnAV#(a))
      provisos (Bits#(a,sa));
      parameter width = valueOf(sa);
      default_clock clk();
      default_reset rst();
      method idfn (WVAL) enable (WSET);
   endmodule
`endif



