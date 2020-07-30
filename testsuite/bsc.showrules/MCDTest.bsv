import Clocks::*;

(* synthesize *)
module mkMCDTest();
   
   Clock clk <- exposeCurrentClock();
   Clock clk2 <- mkAbsoluteClock(3, 17);
   Reset rst2 <- mkAsyncResetFromCR(2,clk2);
   
   Shifter#(8) up1 <- mkShiftUp();
   Shifter#(7) up2 <- mkShiftUp7(clocked_by clk2, reset_by rst2);
   
   Shifter#(8) down1 <- mkShiftDown8();
   Shifter#(7) down2 <- mkShiftDown(clocked_by clk2, reset_by rst2);
   
   Reg#(UInt#(4)) count <- mkReg(0);
   Reg#(UInt#(4)) count2 <- mkSyncRegFromCC(0,clk2);
   
   rule incr;
      let n = count + 1;
      count <= n;
      count2 <= n;
   endrule
   
   rule shift1;
      up1.shift_in(pack(count)[0]);
      down1.shift_in(pack(count)[3]);
   endrule

   (* descending_urgency = "shift2, shift2b" *)
   rule shift2 (pack(count2)[0] == 1);
      up2.shift_in(pack(count2)[2]);
      down2.shift_in(~pack(count2)[1]);
   endrule

   rule shift2b (pack(count2)[1] == 0);
      up2.shift_in(~pack(count2)[3]);
      down2.shift_in(pack(count2)[1]);
   endrule
   
   rule done (up2.get() != 0 && up2.get() == down2.get());
      let t <- $time();
      if (t > 0)
      begin
	 $display("%0d: %0d", count2, up2.get());
	 $finish(0);
      end
   endrule
   
endmodule

interface Shifter#(numeric type n);
   method Action shift_in(Bit#(1) b);
   method Bit#(n) get();
endinterface


module mkShiftUp(Shifter#(n)) provisos(Add#(1,_,n)); // n >= 1
   
   Reg#(Bit#(n)) _x <- mkReg(0);

   method Action shift_in(Bit#(1) b);
      _x <= (_x << 1) | extend(b);
   endmethod
   
   method Bit#(n) get = asIfc(_x)._read;

endmodule

module mkShiftDown(Shifter#(n)) provisos(Add#(1,_,n)); // n >= 1
   
   Reg#(Bit#(n)) _x <- mkReg(0);

   method Action shift_in(Bit#(1) b);
      _x <= (_x >> 1) | (extend(b) << (valueOf(n) - 1));
   endmethod
   
   method Bit#(n) get = asIfc(_x)._read;

endmodule

(* synthesize *)
module mkShiftUp7(Shifter#(7));
   let _m <- mkShiftUp();
   return _m;
endmodule

(* synthesize *)
module mkShiftDown8(Shifter#(8));
   let _m <- mkShiftDown();
   return _m;
endmodule

