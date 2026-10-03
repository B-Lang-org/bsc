package WrapperRedirectUse;

import Vector::*;
import WrapperRedirectSeed::*;
import WrapperRedirect::*;

(* synthesize *)
module sysWrapperRedirectUse(Empty);
   BoolRegs dut <- mkWrapperRedirect;
   BoolRegs second <- mkWrapperRedirectSecond;
   Reg#(Bool) written <- mkReg(False);

   rule writeValues (!written);
      $display("%0d %0d %0d %0d", dut.regs[0], dut.regs[1],
               second.regs[0], second.regs[1]);
      dut.regs[0] <= True;
      dut.regs[1] <= False;
      second.regs[0] <= False;
      second.regs[1] <= True;
      written <= True;
   endrule

   rule readValues (written);
      $display("%0d %0d %0d %0d", dut.regs[0], dut.regs[1],
               second.regs[0], second.regs[1]);
      $finish(0);
   endrule
endmodule

endpackage
