import Clocks::*;

interface SubIfc;
  method Action stop();
endinterface

(* synthesize *)
(* clock_family="default_clock, gclk" *)
(* gate_input_clocks="gclk" *)
module mkSub(Clock gclk, SubIfc ifc);
   Reg#(Bool) running <- mkReg(True);
   Reg#(UInt#(8)) x <- mkReg(0);
   Reg#(UInt#(8)) y <- mkReg(0, clocked_by gclk);
   
   rule incr_x;
      x <= x + 1;
   endrule: incr_x
   
   rule incr_y;
      y <= y + 1;
   endrule: incr_y
   
   rule show (running);
      $display("x = %0d\ny = %0d", x, y);
   endrule: show
   
   method Action stop();
      running <= False;
   endmethod
endmodule: mkSub

(* synthesize *)
module sysSameFamily();

   Reg#(Bool) done <- mkReg(False);
   Reg#(UInt#(8)) count <- mkReg(0);
   GatedClockIfc gc <- mkGatedClockFromCC(True);
   Clock clk2 = gc.new_clk;
   
   SubIfc sub <- mkSub(clk2);
   
   rule ctrl (!done);
      gc.setGateCond((count % 32) < 16);
      count <= count + 1;
      if (count >= 100) begin
         sub.stop;
	 done <= True;
      end
   endrule: ctrl
   
   rule finish (done);
      $finish(0);
   endrule: finish
   
endmodule: sysSameFamily
