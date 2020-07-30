package Bug;
import Vector::*;

typedef Bit#(64) TypeAddrBits;
typedef Vector#(3, Bit#(32)) TypeData;
typedef struct {
  Bool valid;
  Bool isStore; 
  TypeAddrBits addr;
} TypeIreq  deriving (Eq, Bits);
typedef Vector#(3, Bit#(32)) TypeXData;

typedef Maybe#(TypeIreq) TypeMaybeIreq;
typedef Maybe#(TypeData) TypeMaybeData;

import  "BDPI" xbuf = function ActionValue#(TypeXData) xbuf(TypeIreq r, TypeXData d);

interface MemInterface;
   method ActionValue#(TypeXData) xbufWrite(TypeIreq r, TypeXData d);
endinterface: MemInterface      

(* synthesize *)
module mkMem(MemInterface);
   method ActionValue#(TypeXData) xbufWrite(TypeIreq r, TypeXData d);
      TypeXData retData <- xbuf(r,d);
      return retData;
   endmethod
 endmodule: mkMem

(* synthesize *)
module mkBug(Empty);
   Reg#(Bit#(32)) cycle <- mkReg(0);
   MemInterface memUnit <- mkMem();
   Reg#(TypeXData) xwrite <- mkReg(replicate(0));

   rule initrl ;
     cycle <= cycle + 1;
     TypeIreq xw = TypeIreq {valid:True, isStore:True,  addr:'h256};
     TypeXData     xd = replicate(1);
     if (xwrite[0]==0) begin
	TypeXData  xwd <- memUnit.xbufWrite(xw, xd);
        xwrite <= xwd;
     end

     $display("cycle = %d  xw= %h %h ",cycle,xwrite[0], xwrite[1]);
     if (cycle > 15) $finish(0);
   endrule

endmodule: mkBug


endpackage: Bug
