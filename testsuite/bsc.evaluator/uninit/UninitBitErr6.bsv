(* synthesize *)
module sysUninitBitErr6();
   Bit#(5) x;
   if (False)
      x = 0;

   rule test;
     $display(x[3:2]);
     $finish(0);
   endrule

endmodule
   
 
