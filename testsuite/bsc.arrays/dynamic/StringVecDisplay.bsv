import Vector::*;

(* synthesize *)
module sysStringVecDisplay();
   Vector#(4, String) strs;
   strs[0] = "Hello";
   strs[1] = "World!";
   strs[2] = "Hi";
   strs[3] = "Bye";

   Reg#(UInt#(2)) idx <- mkReg(0);

   rule r;
      $display("str = %s", strs[idx]);
   endrule
endmodule

