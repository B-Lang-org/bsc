(* synthesize *)
module sysTestCRegU3 ();

   Reg#(Bit#(32)) rg[3] <- mkCRegU(3);

   Reg#(Bit#(32)) cnt <- mkReg(0);

   rule tick;
      $display("===== %b =====", Bit#(3)'(truncate(cnt)));
      cnt <= cnt + 1;
      // allow for at least two cycles where all are writing
      if (cnt > fromInteger(2**3 + 2))
         $finish(0);
   endrule

   rule r0;
      $display("[%d] read[0]: %h", cnt, rg[0]);
      if (cnt[0] == 1) begin
         Bit#(32) val = 'h000000F0;
         $display("[%d] write[0]: %h", cnt, val);
         rg[0] <= val;
      end
   endrule

   rule r1;
      $display("[%d] read[1]: %h", cnt, rg[1]);
      if (cnt[1] == 1) begin
         Bit#(32) val = 'h00000F00;
         $display("[%d] write[1]: %h", cnt, val);
         rg[1] <= val;
      end
   endrule

   rule r2;
      $display("[%d] read[2]: %h", cnt, rg[2]);
      if (cnt[2] == 1) begin
         Bit#(32) val = 'h0000F000;
         $display("[%d] write[2]: %h", cnt, val);
         rg[2] <= val;
      end
   endrule

endmodule
