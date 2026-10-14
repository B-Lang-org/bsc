
import RegFile::*;

(* synthesize *)
module sysSchedCondsInit();
   SubIfc s <- mkSub;

   Reg#(Bool) c <- mkReg(True);

   // Make sure to compile with -aggressive-conditions so that the RDY
   // condition of "s.m()" is conditionally added to the firing condition
   // of this rule (and therefore "do_req" is not mutually exclusive with
   // "do_init" in the submod).
   //
   rule do_req;
      if (c)
         s.m();
      else
         $display("Not updating");
   endrule

endmodule

interface SubIfc;
   method Action m();
endinterface

module mkSub(SubIfc);

   RegFile#(Bit#(1), Bit#(8)) rf <- mkRegFileFull;

   Reg#(Bool)      r_initialized  <- mkReg(False);

   Reg#(Bit#(8))   r_val          <- mkRegU;

   rule do_init (! r_initialized);
      rf.upd(0, 17);
      r_initialized <= True;
   endrule

   method Action m() if (r_initialized);
      rf.upd(1, 2);
   endmethod
endmodule


