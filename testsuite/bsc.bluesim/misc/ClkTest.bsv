(* synthesize *)
(* default_clock_osc = "clk", default_reset = "rst" *)
module sysClkTest();
   
   Reg#(UInt#(8)) count <- mkReg(0);
   
   rule incr;
      count <= count + 1;
      $display("tick!");
   endrule
   
   rule done (count > 100);
      $finish(0);
   endrule
   
endmodule
