import Vector::*;

(* synthesize *)
module mkTest();

   Vector#(5, Bool) b;
   b[0] = True;

   Integer i;  
   for(i = 0; !b[1]; i = i + 1) begin
   end

   rule test;
     $display(i);
   endrule
   
endmodule
