(* synthesize *)
module sysDUSingleton ();
   Reg#(Bool) c <- mkReg(True);
   Reg#(Bit#(8)) rg <- mkReg(0);

   (* descending_urgency = "r1" *)
   rule r1 (c);
      rg <= rg + 1;
      c <= False;
   endrule

   rule r2;
      rg <= rg - 1;
      c <= True;
   endrule
endmodule

