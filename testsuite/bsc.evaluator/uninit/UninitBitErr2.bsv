(* synthesize *)
module sysUninitBitErr2();
   Bit#(5) x;
   for (Integer i = 1; i < 5; i = i + 1) begin
      x[i] = pack (i > 2);
   end

   rule test;
     $display(x);
     $finish(0);
   endrule

endmodule
   
 
