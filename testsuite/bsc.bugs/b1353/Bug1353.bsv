import FIFO::*;
import Vector::*;

(* options = "-aggressive-conditions" *)
(* synthesize *)
module sysBug1353();
   Reg#(UInt#(3)) r <- mkReg(0);
   
   Vector#(8,FIFO#(UInt#(32))) fifos = ?;
   for(Integer i = 0; i < 8; i = i + 1) begin 
     fifos[i] <- mkFIFO;
   end
   
   PulseWire enq_alive <- mkPulseWire;
   
   rule enq;
      enq_alive.send;
      for(Integer i = 0; i < 8; i = i + 1)
	 fifos[i].enq(zeroExtend(r) + fromInteger(i));
      $display("Enq all fifos when r is %0d", r);
   endrule
   
   rule move_deq;
      r <= r + 1;
   endrule
   
   PulseWire deq_alive <- mkPulseWire;
   
   rule deq(r > 0);
      deq_alive.send;
      let f = fifos[r];
      $display("Deq fifo %0d value %0d", r, f.first);
      f.deq;
   endrule

   rule exit(!enq_alive && !deq_alive);
      $display("Simulation deadlocked");
      $finish(0);
   endrule
   
endmodule

