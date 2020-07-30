// Test how BSC compiles two uses of an AV method which is SBR with itself

interface Ifc;
   method ActionValue#(Bool) m(Bool b);
endinterface

import "BVI"
module mkAVMethSBR(Ifc);
   method BOUT m(BIN) enable(EN) ready(RDY);
   schedule m SBR m;
endmodule

(* synthesize *)
module sysTestAVMethSBR();
   let dut <- mkAVMethSBR();

   rule rA;
      let v1 <- dut.m(True);
      $display(v1);
   endrule 

   rule rB;
      let v2 <- dut.m(False);
      $display(v2);
   endrule
endmodule

