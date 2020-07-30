import Clocks::*;

(* synthesize *)
module sysUngatedClockMux(Empty);

  Clock clk5  <- mkAbsoluteClock(60, 60);
  Clock clk11 <- mkAbsoluteClock(120, 120);

  Reg#(Bit#(32)) flipcount <- mkReg(3);

  Reg#(Bit#(32)) fliptime <- mkReg(24);

  Reg#(Bool) clkflag <- mkReg(True);

  MuxClkIfc cm <- mkUngatedClockMux(clk11, clk5);
  Clock clkM = cm.clock_out;

  // make a reset for the muxed clock
  Reset rstM <- mkAsyncResetFromCR(2, clkM);

  Reg#(Bit#(14)) real_counter <- mkReg(0, clocked_by clkM, reset_by rstM);

  rule count (flipcount != fliptime);
     flipcount <= flipcount + 1;
  endrule

  rule select (flipcount == fliptime);
     cm.select(clkflag);
     clkflag <= !clkflag;
     fliptime <= fliptime << 1;
     flipcount <= 0;

     if(clkflag) 
       $display ("Clock Select A");
     else 
       $display ("Clock Select B");

  endrule

  rule real_count;
     real_counter <= real_counter + 1;
  endrule

  rule test;
    $display("Real counter: %0d Time %t", real_counter, $time);
    if (real_counter == 9)
      $finish(0);
  endrule

endmodule



