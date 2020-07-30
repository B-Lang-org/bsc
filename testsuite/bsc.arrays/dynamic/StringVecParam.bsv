import Vector::*;

(* synthesize *)
module mkStringVecParam_Sub #(parameter String str)();
   rule r;
      $display(str);
   endrule
endmodule

(* synthesize *)
module sysStringVecParam #(parameter UInt#(2) idx)();
   Vector#(4, String) strs;
   strs[0] = "Hello";
   strs[1] = "World!";
   strs[2] = "Hi";
   strs[3] = "Bye";

   let s <- mkStringVecParam_Sub(strs[idx]);
endmodule
