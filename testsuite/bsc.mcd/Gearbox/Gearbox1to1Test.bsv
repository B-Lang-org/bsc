import Gearbox::*;
import StmtFSM::*;

(* synthesize *)
module sysGearbox1to1Test();
   Clock clk <- exposeCurrentClock;
   Reset rst <- exposeCurrentReset;
   
   Gearbox#(1,1,Bit#(8)) dut1 <- mk1toNGearbox(clk, rst, clk, rst);
   Gearbox#(1,1,Bit#(8)) dut2 <- mkNto1Gearbox(clk, rst, clk, rst);
   
   Reg#(Bit#(8))         data1 <- mkReg(0);
   Reg#(Bit#(8))         data2 <- mkReg(0);
   
   Reg#(Bit#(32))        count <- mkReg(0);
   
   rule incr;
      count <= count + 1;
   endrule
   
   rule source_1;
      dut1.enq(unpack(data1));
      data1 <= data1 + 1;
   endrule
   
   rule source_2;
      dut2.enq(unpack(data2));
      data2 <= data2 + 1;
   endrule
   
   rule sink_1;
      let x = dut1.first; dut1.deq;
      $display("[%0t]:01: Deq = { %0d }", $time, x[0]);
   endrule
   
   rule sink_2;
      let x = dut2.first; dut2.deq;
      $display("[%0t]:02: Deq = { %0d }", $time, x[0]);
   endrule
   
   rule simulation_done(count == 1000);
      $display("[%0t] Ending Simulation", $time);
      $finish(0);
   endrule
endmodule
