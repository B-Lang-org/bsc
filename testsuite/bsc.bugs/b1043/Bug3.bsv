interface IfcIdFnAV#(type a) ;
   method ActionValue#(a) idfn (a x) ;
endinterface

interface IfcVIdFn#(type a) ;
   method Action vIn  (a x) ;
   method a      vOut ();
endinterface: IfcVIdFn



module mkIdFnAVRW ( IfcIdFnAV#(a) )
      provisos (Bits#(a,sa));

   IfcVIdFn#(a) _ifc <- vMkIdFnAVRW ;

   method ActionValue#(a) idfn( a x ) ;
      _ifc.vIn( x);
      return _ifc.vOut ;
   endmethod

endmodule


import "BVI" RWire =
   module vMkIdFnAVRW ( IfcVIdFn#(a) )
      provisos (Bits#(a,sa));
      parameter width = valueOf(sa);
      default_clock clk();
      default_reset rst();
      method  vIn (WVAL) enable (WSET);
      method WGET vOut ;
      path (WSET, WGET) ;
   endmodule



(* synthesize *)
module mkTest ( IfcIdFnAV#(int) );
   IfcIdFnAV#(int) a2  <- mkIdFnAVRW ;
   return a2;
endmodule


