package WrapperDictsUse;

import Vector::*;
import WrapperDicts::*;

(* synthesize *)
module sysWrapperDictsUse(Empty);
   EncodedRegs encoded <- mkEncodedRegs;
   DerivedRegs derived <- mkDerivedRegs;
   Reg#(Bool) written <- mkReg(False);

   rule writeValues (!written);
      $display("%0d %0d %0d", encoded.regs[0].value,
               pack(encoded.regs[0]), pack(derived.regs[0]));
      encoded.regs[0] <= Encoded { value: 8'h23 };
      encoded.regs[3] <= Encoded { value: 8'h45 };
      derived.regs[0] <= Derived { hi: 3, lo: 4 };
      derived.regs[3] <= Derived { hi: 5, lo: 6 };
      written <= True;
   endrule

   rule readValues (written);
      $display("%0d %0d %0d %0d %0d %0d",
               encoded.regs[0].value, pack(encoded.regs[0]),
               pack(derived.regs[0]), encoded.regs[3].value,
               pack(encoded.regs[3]), pack(derived.regs[3]));
      $finish(0);
   endrule
endmodule

endpackage
