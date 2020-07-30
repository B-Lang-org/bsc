(* synthesize *)
module sysUninitBitErr3();
   Bit#(5) x;
   if (False)
      x = 0;

   rule test;
     $display(x);
     $finish(0);
   endrule

endmodule
   
 
