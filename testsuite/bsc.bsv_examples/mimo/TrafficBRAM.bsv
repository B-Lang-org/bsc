import MIMO::*;
import LFSR::*;
import Vector::*;
import DefaultValue::*;
import BUtils::*;
import GetPut::*;
import FIFO::*;


typedef Get#(Bit#(n)) RandI#(numeric type n);

module mkRand_6#(Bit#(16) ini)(RandI#(6));
   LFSR#(Bit#(16)) lfsr <- mkLFSR_16;
   FIFO#(Bit#(6)) fi <- mkFIFO;
   Reg#(Bool) starting <- mkReg(True);
   
   rule start if (starting);
      starting <= False;
      lfsr.seed(ini);
   endrule
   
   rule run if (!starting);
      fi.enq(lfsr.value()[10:5]);
      lfsr.next;
   endrule
   
   return fifoToGet(fi);
endmodule

module mkRand_8#(Bit#(32) ini)(RandI#(8));
   LFSR#(Bit#(32)) lfsr <- mkLFSR_32;
   FIFO#(Bit#(8)) fi <- mkFIFO;
   Reg#(Bool) starting <- mkReg(True);
   
   rule start if (starting);
      starting <= False;
      lfsr.seed(ini);
   endrule
   
   rule run if (!starting);
      fi.enq(lfsr.value()[21:14]);
      lfsr.next;
   endrule
   
   return fifoToGet(fi);
endmodule

(* synthesize *)
module sysTrafficBRAM();
   MIMOConfiguration cfg = defaultValue;
   cfg.bram_based = True;
   
   MIMO#(32, 32, 48, Bit#(8))      dut       <- mkMIMO(cfg);
   Vector#(32, RandI#(8))          vdata     <- mapM(mkRand_8, genWith(fromInteger));
   RandI#(6)                       enqcount  <- mkRand_6('h11);
   RandI#(6)                       deqcount  <- mkRand_6('h39);
   
   (* fire_when_enabled *)
   rule enqueue_next_sequence;
      function ActionValue#(Bit#(8)) getByte (RandI#(8) ifc) = ifc.get();
					      
      Vector#(32, Bit#(8)) v <- mapM(getByte, vdata);
      Bit#(6) cnt <- enqcount.get();
      
      if (cnt <= 32 && dut.enqReadyN(cExtend(cnt))) begin
         dut.enq(cExtend(cnt), v);
	 if (cnt > 0) begin
	    $write("enq: ");
	    for(Integer i = 0; i < 32; i = i + 1) begin
	       if (fromInteger(i) < cnt) begin
		  $write("%3d ", v[i]);
	       end
	    end
	    $display();
	 end
      end
   endrule
   
   (* fire_when_enabled *)
   rule dequeue_next_sequence;
      Vector#(32, Bit#(8)) v = newVector;
      Bit#(6) cnt <- deqcount.get();
      
      if (cnt <= 32 && dut.deqReadyN(cExtend(cnt))) begin
	 dut.deq(cExtend(cnt));
	 v = dut.first();
	 if (cnt > 0) begin
	    $write("deq: ");
	    for(Integer i = 0; i < 32; i = i + 1) begin
	       if (fromInteger(i) < cnt) begin
		  $write("%3d ", v[i]);
	       end
	    end
	    $display();
	 end
      end
   endrule
      
   Reg#(UInt#(32)) cycleCount <- mkReg(0);
   rule count_inc;
      cycleCount <= cycleCount + 1;
   endrule
   
   rule done if (cycleCount > 5000);
      $finish;
   endrule
   
endmodule


