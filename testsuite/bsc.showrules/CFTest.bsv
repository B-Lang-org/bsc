(* synthesize *)
module mkCFTest();
   Reg#(Bool) toggle <- mkReg(True);
   Reg#(UInt#(8)) count  <- mkReg(0);
   Reg#(UInt#(8)) count2 <- mkReg(0);
   
   rule flip;
      toggle <= !toggle;
   endrule
   
   (* conflict_free = "incr, decr" *)
   rule incr;
      if (toggle)
	 count <= count + 2;
      else
	 count2 <= count2 + 5;
   endrule

   rule decr;
      if (toggle)
	 count2 <= count2 - 2;
      else
	 count <= count - 1;
   endrule
   
   rule done (count > 100);
      $finish(0);
   endrule
   
endmodule
