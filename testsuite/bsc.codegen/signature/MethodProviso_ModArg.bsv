typedef enum { X, Y, Z} L;

instance Bits#(L,2);
endinstance
 
interface IFC#(type m);
   method Bit#(m) fn(Bool x) provisos(Bits#(L,m));
endinterface

(* synthesize *)
module sysMethodProviso_ModArg #(IFC#(2) x) ();
endmodule
