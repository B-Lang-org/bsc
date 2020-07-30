import Vector::*;

typedef  Bit#(8)  T;

(* synthesize *)
module sysSameElems2();

   Vector#(3, Action) arr;
   // Test when the elements are structurally the same,
   // but are not actually the same heap references
   //
   arr[0] = $display("Hi.");
   arr[1] = $display("H" + "i.");
   arr[2] = action
              noAction;
              $display("Hi" + ".");
            endaction;

   // An index which can select out of bounds
   Reg#(Bit#(4)) idx <- mkReg(0);

   rule doUpd;
      // Test that this reduces to only one element,
      // but still includes a bounds test
      // (because out of range selection is noAction for type Action)
      //
      arr[idx];
   endrule
endmodule

