(* synthesize *)
module sysArithShift();
   Reg#(Int#(6)) r6_0 <- mkReg(6'b001100);
   Reg#(Int#(6)) r6_f <- mkReg(6'b101100);

   Reg#(Int#(26)) r26_0 <- mkReg(26'h10e7d2a);
   Reg#(Int#(26)) r26_f <- mkReg(26'h30e7d2a);

   Reg#(Int#(36)) r36_0 <- mkReg(36'h70e7d2af5);
   Reg#(Int#(36)) r36_f <- mkReg(36'hf0e7d2af5);

   Reg#(Int#(96)) r96_0 <- mkReg(96'h70e7d2af_deadbeef_cafef00d);
   Reg#(Int#(96)) r96_f <- mkReg(96'hf0e7d2af_deadbeef_cafef00d);

   Reg#(UInt#(8)) count <- mkReg(0);

   rule incr;
      count <= count + 1;
   endrule

   rule shifter;
      $display("%h >> %0d == %h", r6_0,  count, r6_0  >> count);
      $display("%h >> %0d == %h", r6_f,  count, r6_f  >> count);
      $display("%h >> %0d == %h", r26_0, count, r26_0 >> count);
      $display("%h >> %0d == %h", r26_f, count, r26_f >> count);
      $display("%h >> %0d == %h", r36_0, count, r36_0 >> count);
      $display("%h >> %0d == %h", r36_f, count, r36_f >> count);
      $display("%h >> %0d == %h", r96_0, count, r96_0 >> count);
      $display("%h >> %0d == %h", r96_f, count, r96_f >> count);
   endrule

   rule done (count == 200);
      $finish(0);
   endrule

endmodule