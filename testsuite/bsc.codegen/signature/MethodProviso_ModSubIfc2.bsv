typedef enum { X, Y, Z} L;

instance Bits#(L,2);
endinstance
 
interface SubIFC#(type m);
   method Bit#(m) fn(Bool x) provisos(Bits#(L,m));
endinterface

// In this variant, we choose not make this parameterized
interface IFC;
   interface SubIFC#(2) s;
endinterface

(* synthesize *)
module sysMethodProviso_ModSubIfc2 #(IFC x) ();
   interface SubIFC s;
      method fn(x) = ?;
   endinterface
endmodule
