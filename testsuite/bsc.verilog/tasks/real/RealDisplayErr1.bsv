(* synthesize *)
module sysRealDisplayErr1();
   
   Real r = 98.0;
   
   // to demonstrate that adding padding is a valid thing to do
   Bit#(64) other = 98;
   
   rule test;
      $display("%h", r);
      $display("%h", other);
      $display;
      
      $display("%s", r);
      $display("%s", other);
      $display;
      
      $display("%d", r);
      $display("%d", other);
      $display;
      
      $display("%o", r);
      $display("%o", other);
      $display;
      
      $display("%b", r);
      $display("%b", other);
      
      $finish(0);
   endrule
   
endmodule
