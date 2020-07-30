typedef enum { X, Y, Z} L;

instance Bits#(L,2);
endinstance
 
interface IFC#(numeric type m);
   method Bit#(m) fn(Bool x) provisos(Bits#(L,m));
endinterface

(* synthesize *)
module sysMethodProviso_ModIfc (IFC#(2));
   method fn(x) = ?;
endmodule
