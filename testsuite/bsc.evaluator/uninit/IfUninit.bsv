(* synthesize *)
module sysIfUninit();
   Reg#(Bool) r <- mkReg(False);
   
   rule test;
      Bit#(5) x;
      if (r) begin
	 x = 7;
      end
      else begin 
	 x = 5;
      end
      $display("%0d", x);
      $finish(0);
   endrule
   
endmodule
