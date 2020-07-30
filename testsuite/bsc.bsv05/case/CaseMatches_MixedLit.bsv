(* synthesize *)
module sysCaseMatches_MixedLit ();
   Reg#(Bit#(4)) rg <- mkReg(0);
   
   rule incr;
      Bit#(4) res = case (rg) matches
		       4'b00??: return 1;
		       4'b1???: return 2;
		       4'b0100: return 3;
		       4'b0101: return 4;
		       4'b0110: return 5;
		       4'b0111: return 6;
		    endcase;
      $display("%d", res);
      rg <= rg + 1;
      if (rg == 4'b1111)
	 $finish(0);
   endrule
endmodule

