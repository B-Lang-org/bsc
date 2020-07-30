(* synthesize *)
module sysDynamicFormat2 ();
   
   Reg#(Bit#(8))   count  <- mkReg(0);
   Reg#(Bit#(160)) fmt0    <- mkReg(0);
   Reg#(Bit#(640)) target <- mkReg(0);

   rule set_fmt (count[1:0] == 0);
      case (count[3:2])
	 0: begin
               let s <- $swriteAV("(default) ");
               fmt0 <= s;
	    end
	 1: begin
               let s <- $swriteAV("(decimal) %%d");
               fmt0 <= s;
	    end
	 2: begin
               let s <- $swriteAV("(hex)     %%h");
               fmt0 <= s;
	    end
	 3: begin
               let s <- $swriteAV("(binary)  %%b");
               fmt0 <= s;
	    end
      endcase
   endrule
   
   rule use_fmt (count[1:0] == 1);
      let s <- $sformatAV(fmt0, count);
      target <= s;
   endrule
	
   rule show (count[1:0] == 2);
      $display("%s", target);
   endrule
   
   rule every;
      count <= count + 1;
      if (count == 20) $finish(0);
   endrule

endmodule
