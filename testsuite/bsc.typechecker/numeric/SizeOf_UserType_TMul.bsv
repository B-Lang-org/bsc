import Vector::*;

typedef Bit#(TMul#(n, SizeOf#(dataT))) Syn#(type n, type dataT);

function Syn#(n,dataT) fn()
 provisos ( Bits#(dataT,szT) );
   return unpack(0);
endfunction

typedef struct {
  Bool f1;
  UInt#(32) f2;
} T deriving (Eq, Bits);

(* synthesize *)
module sysSizeOf_UserType_TMul (Reg#(Syn#(4,T)));
   Syn#(4,T) init_val = fn;
   Reg#(Syn#(4,T)) rg <- mkReg(init_val);
   return rg;
endmodule

