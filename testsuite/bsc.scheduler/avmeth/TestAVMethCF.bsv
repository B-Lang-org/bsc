// Test how BSC compiles two uses of an AV method which is CF with itself

interface Ifc;
   method ActionValue#(Bool) m(Bool b);
endinterface

import "BVI"
module mkTestAVMethCF(Ifc);
   method BOUT m(BIN) enable(EN) ready(RDY);
   schedule m CF m;
endmodule

(* synthesize *)
module sysTestAVMethCF();
   let dut <- mkTestAVMethCF();

   rule rA;
      let v1 <- dut.m(True);
      $display(v1);
   endrule 

   rule rB;
      let v2 <- dut.m(False);
      $display(v2);
   endrule
endmodule

