(* synthesize *)
module sysUninitBitErr1();
   Bit#(5) x;
   for (Integer i = 0; i < 4; i = i + 1) begin
      x[i] = pack (i > 2);
   end

   rule test;
     $display(x);
     $finish(0);
   endrule

endmodule
   
 
