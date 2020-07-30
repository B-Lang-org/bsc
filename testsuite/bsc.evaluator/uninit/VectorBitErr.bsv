import Vector::*;

(* synthesize *)
module sysVectorBitErr();
   Vector#(3, Bit#(16)) v;
   v[0] = 0;
   for (Integer i = 0; i < 16; i = i + 1) begin
      v[1][i] = fromInteger(i  % 2);
   end
   
   rule test;
      $display("v[0]=%0d", v[0]);
      $display("v[1]=%0b", v[1]);
      $display("v[2]=%0h", v[2]);
      $finish(0);
   endrule
   
endmodule

   
	 
