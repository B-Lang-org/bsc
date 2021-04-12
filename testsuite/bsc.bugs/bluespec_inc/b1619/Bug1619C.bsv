(* synthesize *)
module sysBug1619C();

   Reg#(UInt#(8)) x <- mkReg(0);
   Reg#(Bool)     decr1 <- mkReg(True);
   Reg#(Bool)     addN  <- mkReg(True);
   Reg#(UInt#(2)) n     <- mkReg(3);

   rule low_priority if (decr1);
      x <= x - 1;
   endrule

   for (Integer i = 0; i < 3; i = i+1) begin
       (* descending_urgency="normal,low_priority" *)
       rule normal if (fromInteger(i) == n);
	  x <= x + extend(n);
       endrule
   end

endmodule