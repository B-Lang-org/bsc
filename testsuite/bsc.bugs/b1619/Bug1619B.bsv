(* synthesize *)
module sysBug1619B();

   Reg#(UInt#(8)) x <- mkReg(0);
   Reg#(Bool)     decr1 <- mkReg(True);
   Reg#(Bool)     addN  <- mkReg(True);
   Reg#(UInt#(2)) n     <- mkReg(3);

   rule high_priority if (decr1);
      x <= x - 1;
   endrule

   for (Integer i = 0; i < 3; i = i+1) begin
//       (* descending_urgency="high_priority,normal" *)
       rule normal if (fromInteger(i) == n);
	  x <= x + extend(n);
       endrule
   end

endmodule