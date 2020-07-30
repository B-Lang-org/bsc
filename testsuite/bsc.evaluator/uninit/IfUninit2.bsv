(* synthesize *)
module mkTest();
   Reg#(Bool) r <- mkReg(False);
   
   rule test;
      Bit#(5) x;
      
      if (r) begin
	 x = 7;
      end
      
      if (!r) begin 
	 x = 5;
      end
      
      $display(x);
      $finish(0);
      
   endrule
   
endmodule
