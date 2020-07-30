
(*synthesize*)
module sysMutuallyExclusiveAssump_CombSched();

   Reg#(Bool) rdCond <- mkRegU;
   Reg#(Bool) wrCond <- mkRegU;
   
   RWire#(void) toMem_rw   <- mkRWire;
   
   Reg#(Maybe#(Bit#(4))) queue <- mkRegU;
   Reg#(Bit#(4)) current_entry <- mkRegU;

   let the_bank <- mkMutuallyExclusiveAssump_CombSched_Sub;
   
   (*descending_urgency="accept, rd_data"*)
   rule accept (queue matches tagged Valid .e);
      current_entry <= e;
      if (e==0)
         the_bank.transfer;
   endrule

   rule rd_data (rdCond);
      if (current_entry==0)
         the_bank.endTransfer(True);
   endrule
   
   (*mutually_exclusive="rd_data, handle_write"*)
   rule handle_write (wrCond);
      toMem_rw.wset(?);
      the_bank.endTransfer(False);
   endrule

   (*descending_urgency="handle_write, connectResponse"*)
   rule connectResponse;
      toMem_rw.wset(?);
   endrule
endmodule


interface SubIfc;
   method Action transfer;
   method Action endTransfer(Bool x);
endinterface

(*synthesize*)
module mkMutuallyExclusiveAssump_CombSched_Sub(SubIfc);

   Reg#(int) transferring <- mkReg(0);
   
   rule set_precharge;
      transferring <= transferring + 1;
   endrule
   
   method Action transfer() if (transferring==0);
      transferring <= transferring + 2;
   endmethod   
   
   method Action endTransfer(Bool x);
      transferring <= 0;
   endmethod
   
endmodule

