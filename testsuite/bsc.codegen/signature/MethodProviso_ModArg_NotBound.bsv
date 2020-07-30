typedef enum { X, Y, Z} L;

/*
instance Bits#(L,2);
endinstance
*/

interface IFC;
   method Bit#(2) fn(Bool x) provisos(Bits#(L,2));
endinterface

(* synthesize *)
module sysMethodProviso_ModArg_NotBound #(IFC x) ();
endmodule
