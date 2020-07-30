import Vector::*;
import BuildVector::*;

(* synthesize *)
module sysTestBuildVector();
   Vector#(4,Bool)     v1 = vec(True,False,True,True);
   Vector#(2,UInt#(8)) v2 = vec(7,32);
   Vector#(3,Bool)     v3 = vec(False,True,True);
   Vector#(1,UInt#(4)) v4 = vec(3);

   Reg#(Bool) done <- mkReg(False);

   rule r (!done);
      $display("v1[0] -> %b", v1[0]);
      $display("v1[1] -> %b", v1[1]);
      $display("v1[2] -> %b", v1[2]);
      $display("v1[3] -> %b", v1[3]);
      $display("v2[0] -> %d", v2[0]);
      $display("v2[1] -> %d", v2[1]);
      $display("v3[0] -> %b", v3[0]);
      $display("v3[1] -> %b", v3[1]);
      $display("v3[2] -> %b", v3[2]);
      $display("v4[0] -> %d", v4[0]);

      done <= True;
   endrule

   rule r2 (done);
      $finish(0);
   endrule
endmodule

