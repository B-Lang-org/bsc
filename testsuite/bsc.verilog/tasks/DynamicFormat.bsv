(* synthesize *)
module sysDynamicFormat ();
   
   Reg#(Bit#(8))   count  <- mkReg(0);
   Reg#(Bit#(160)) fmt0    <- mkReg(0);
   Reg#(Bit#(640)) target <- mkReg(0);

   rule set_fmt (count[1:0] == 0);
      case (count[3:2])
	 0: $swrite(asIfc(fmt0), "(default) ");
	 1: $swrite(asIfc(fmt0), "(decimal) %%d");
	 2: $swrite(asIfc(fmt0), "(hex)     %%h");
	 3: $swrite(asIfc(fmt0), "(binary)  %%b");
      endcase
   endrule
   
   rule use_fmt (count[1:0] == 1);
      $sformat(asIfc(target), fmt0, count);
   endrule
	
   rule show (count[1:0] == 2);
      $display("%s", target);
   endrule
   
   rule every;
      count <= count + 1;
      if (count == 20) $finish(0);
   endrule

endmodule
