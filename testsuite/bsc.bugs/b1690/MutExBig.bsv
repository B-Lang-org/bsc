import Vector :: *;

(* synthesize *)
module sysMutExBig();

   Vector#(5,Reg#(Bool)) flag <- replicateM(mkReg(True));
   Reg#(Bool)            x    <- mkRegU();


   Bit#(3) p3_hi = truncateLSB(pack(readVReg(flag)));
   Bit#(3) p3_lo = truncate   (pack(readVReg(flag)));

   rule r1 (p3_hi == 3'b011);
      $display("R1");
      x <= !x;
   endrule

   rule r2 (p3_lo == 3'b011);
      $display("R2");
      x <= !x;
   endrule

   rule r3 (flag[4] && !flag[0]);
      $display("R3");
      x <= !x;
   endrule
   
   rule r4 (flag[2]);
      $display("R4");
      x <= !x;
   endrule
   
   rule done if (pack(readVReg(flag)) == '0);
      $finish(0);
   endrule

   Reg#(Vector#(5,Bool)) flagr <- mkReg(replicate(True));
   Reg#(Bool)            y     <- mkRegU();
   
   Bit#(3)  r3_hi = truncateLSB(pack(flagr));
   Bit#(3)  r3_lo = truncate   (pack(flagr));
   Bit#(6)  r6 = {r3_hi, r3_lo} ;
   
   rule r1y (r3_hi == 3'b011);
      $display("R1y");
      y <= !y;
   endrule
   
   rule r2y (r3_lo == 3'b011);
      $display("R2y");
      y <= !y;
   endrule
   
   rule r3y (r6 == 6 'b111111);
      $display("R3y");
      y <= !y;
   endrule

   rule r4y (flagr[4] && !flagr[0]);
      $display("R4y");
      y <= !y;
   endrule

   rule r5y (flagr[4] && flagr[0]);
      $display("R5y");
      y <= !y;
   endrule
   



endmodule
