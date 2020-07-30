typedef enum { X, Y, Z} L;

/*
instance Bits#(L,2);
endinstance
*/

interface SubIFC;
   method Bit#(2) fn(Bool x) provisos(Bits#(L,2));
endinterface

interface IFC;
   interface SubIFC s;
endinterface

(* synthesize *)
module sysMethodProviso_ModSubIfc_NotBound #(IFC x) ();
   interface SubIFC s;
      method fn(x) = ?;
   endinterface
endmodule
