(* synthesize *)
module sysUninitBitOK1();
   Bit#(5) x;
   x [4] = message("x4",1);
   x [3] = message("x3",1);
   x [2] = message("x2",0);
   x [1] = message("x1",0);
   x [0] = message("x0",1);
   
   Bit#(6) y;
   y[5] = 1;
   y[4] = 0;
   y[3] = 0;
   y[2] = 0;
   y[1] = 0;
   y[0] = 0;

   rule test;
     $display(x);
     $display(y);
     $finish(0);
   endrule

endmodule
   
 
