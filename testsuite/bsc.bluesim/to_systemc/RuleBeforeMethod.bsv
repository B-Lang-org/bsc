import FIFO::*;

interface Dut;
   method Action enq( int x );
   method Action deq();
   method int    first();
endinterface

(* synthesize *)
module sysRuleBeforeMethod( Dut );
   
   FIFO#(int) fifo <- mkFIFO;
   
   Reg#(Bit#(4)) cntrEnq <- mkReg(0);
   Reg#(Bit#(4)) cntrDeq <- mkReg(0);

   Wire#(Bool) stallEnq <- mkDWire(False);
   Wire#(Bool) stallDeq <- mkDWire(False);

   rule mixitup;
      if (cntrEnq[1] == 1)
      begin
         $display("Stall Enq");
	 stallEnq <= True;
      end
      if (cntrDeq[2] == 1)
      begin
         $display("Stall Deq");
	 stallDeq <= True;
      end
      cntrEnq <= cntrEnq + 1;
      cntrDeq <= cntrDeq + 1;
   endrule
   
   // This method requires mixitup to run before,
   // but that is OK because it is an Action method.
   method Action enq( int x ) if (!stallEnq);
      $display($time, "  Enqueue %x", x );
      fifo.enq(x);
   endmethod
   
   // This method requires mixitup to run before,
   // but that is OK because it is an Action method.
   method Action deq() if (!stallDeq);
      $display($time, "  Deq ");
      fifo.deq();
   endmethod
   
   // This method requires mixitup to run before,
   // and that is not OK because it is a value method.
   method int    first() if (!stallDeq);
      return fifo.first();
   endmethod

endmodule
