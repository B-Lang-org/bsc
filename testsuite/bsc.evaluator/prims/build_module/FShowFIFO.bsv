import FShow::*;
import FIFO::*;

module mkFifoFmt#(FIFO#(t) ff)(Fmt)
  provisos(Bits#(t,st),FShow#(t));
  RWire#(t) rw <- mkRWire;
  rule load_wire;
     rw.wset(ff.first);
  endrule

  return (isValid(rw.wget) ? fshow(validValue(rw.wget)) : $format("EMPTY"));
endmodule

instance FShow#(FIFO#(t))
  provisos (Bits#(t,st),FShow#(t));
  function fshow(ff);
     let c = clockOf(ff.deq);
     let r = resetOf(ff.deq);
     return primBuildModule(primGetName(fshowFifo),c,r,mkFifoFmt(ff));
  endfunction
endinstance

(* synthesize *)
module sysFShowFIFO();
   
   FIFO#(Maybe#(Int#(32))) f <- mkFIFO;

   Reg#(UInt#(32)) cycle <- mkReg(0);
   
   rule tick;
      cycle <= cycle + 1;
   endrule
   
   rule show;
      $display("Cycle %0d ", cycle, fshow(f));
   endrule
   
   rule test(cycle == 0);
      f.enq(Nothing);
   endrule
   
   rule test2(cycle == 1);
      f.enq(Valid(-1));
      f.deq;
   endrule
   
   (* execution_order = "show, test3" *)
   rule test3(cycle == 3);
      $finish(0);
   endrule
   
endmodule
