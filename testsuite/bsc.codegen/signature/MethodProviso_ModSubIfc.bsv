typedef enum { X, Y, Z} L;

instance Bits#(L,2);
endinstance
 
interface SubIFC#(type m);
   method Bit#(m) fn(Bool x) provisos(Bits#(L,m));
endinterface

interface IFC#(type m);
   interface SubIFC#(m) s;
endinterface

(* synthesize *)
module sysMethodProviso_ModSubIfc #(IFC#(2) x) ();
   interface SubIFC s;
      method fn(x) = ?;
   endinterface
endmodule
