(* synthesize *)
module sysUninitBitErr4();
   Bit#(5) x;
   x[1] = 1;
   x[2] = 1;
   x[3] = 1;

   rule test;
     $display(x[4]);
     $finish(0);
   endrule

endmodule
   
 
