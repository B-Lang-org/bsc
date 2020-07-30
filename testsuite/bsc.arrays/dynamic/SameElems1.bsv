import Vector::*;

typedef  Bit#(8)  T;

(* synthesize *)
module sysSameElems1();

   Reg#(T) rg <- mkRegU;
   Vector#(3, Reg#(T)) arr = replicate(rg);

   // An index which can select out of bounds
   Reg#(Bit#(4)) idx <- mkReg(0);

   rule doUpd;
      // Test that this reduces to only one element,
      // but still includes a bounds test
      // (because out of range selection is noAction for type Action)
      //
      arr[idx] <= 17;
   endrule
endmodule

