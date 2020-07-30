import Vector::*;

typedef Bit#(SizeOf#(dataT)) Syn#(type dataT);

function Syn#(dataT) fn()
 provisos ( Bits#(dataT,szT) );
   return unpack(0);
endfunction

(* synthesize *)
module sysSizeOfBool (Reg#(Syn#(Bool)));
   Syn#(Bool) init_val = fn;
   Reg#(Syn#(Bool)) rg <- mkReg(init_val);
   return rg;
endmodule

