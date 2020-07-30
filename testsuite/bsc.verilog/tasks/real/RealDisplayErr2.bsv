(* synthesize *)
module sysRealDisplayErr2();
   
   String s = "c";
   Int#(64) i = 17;
   UInt#(23) u = 97;
   Integer j = -94;
   Bit#(28) x = 28'hbeedead;
   
   rule test;
      $display("%1.3f", s);
      $display;
      
      $display("%g", i);
      $display;
      
      $display("%2.2e", u);
      $display;
      
      $display("%2e %f %7g", j, 17.2, x);
      $finish(0);
   endrule
   
endmodule

