(* synthesize *)
module sysUninitBitErr5();
   Bit#(5) x;
   if (False)
      x = 0;

   rule test;
     $display(x[3]);
     $finish(0);
   endrule

endmodule
   
 
