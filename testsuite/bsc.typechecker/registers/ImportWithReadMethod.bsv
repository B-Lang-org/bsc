
interface IFC#(type a_type);
   method a_type foo(a_type x);
   method a_type _read();
endinterface

import "BVI" Mod =
module mkA( IFC#(a_type) ifc )
   provisos (Bits#(a_type, sizeOfa)) ;

   parameter width = valueOf( sizeOfa ) ;

   method DOUT _read() ;
   method DOUT foo(DIN) ;

endmodule
   
