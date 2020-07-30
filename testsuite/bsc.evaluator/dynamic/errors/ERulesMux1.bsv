(* synthesize *)
module sysERulesMux1();

   Reg#(Bool) b <- mkReg(True);

   Reg#(Bool) c1 <- mkReg(True);
   Reg#(Bool) c2 <- mkReg(True);

   if (b) begin
      rule r1 (c1);
	 $display("r1");
      endrule
   end
   else begin
      rule r2 (c2);
	 $display("r2");
      endrule
   end

endmodule
