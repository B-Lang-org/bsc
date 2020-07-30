(* synthesize *)
module sysCaseDummy1();
   Reg#(Bit#(4)) rg <- mkReg(0);
   
   rule incr;
      Bit#(4) res = case (rg)
		       4'b0100: return 3;
		       4'b0101: return 4;
		       4'b0110: return 5;
		       4'b0111: return 6;
		       _      : return 7;
		    endcase;
      $display("%d", res);
      rg <= rg + 1;
      if (rg == 4'b1111)
	 $finish(0);
   endrule
endmodule

