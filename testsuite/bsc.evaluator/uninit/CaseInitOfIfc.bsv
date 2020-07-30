typedef enum { A, B, C } Alpha deriving (Eq, Bits);

interface IFC;
   method Action set (Bool x1, Bool x2, Bool x3);
   method Bool m (Alpha x);
endinterface

(* synthesize *)
module sysCaseInitOfIfc (IFC);
   Reg#(Bool) rg1 <- mkReg(True);
   Reg#(Bool) rg2 <- mkReg(True);
   Reg#(Bool) rg3 <- mkReg(True);

   method Action set (Bool x1, Bool x2, Bool x3);
      rg1 <= x1;
      rg2 <= x2;
      rg3 <= x3;
   endmethod

   method Bool m (Alpha x);
      Reg#(Bool) rg;    // note, not initialized
      case (x) matches  // this case is complete, but does BSC see that?
	 A : rg = rg1;
	 B : rg = rg2;
	 C : rg = rg3;
      endcase
      return (rg);      // implied _read
   endmethod
endmodule


