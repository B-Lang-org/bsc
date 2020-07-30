(* synthesize *)
module sysTest();

   Reg#(UInt#(8)) r <- mkReg(0);
   Reg#(UInt#(8)) m <- mkReg(0);

   rule rl1;
      r <= r / 16;
      m <= r % 16;
   endrule

   Reg#(Int#(8)) sr <- mkReg(0);
   Reg#(Int#(8)) sm <- mkReg(0);

   rule rl2;
      sr <= sr / 16;
      sm <= sr % 16;
   endrule

endmodule