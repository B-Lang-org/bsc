import RegFile::*;
import Clocks::*;

// Use a port-limited resource (RegFile) in a module instantiation.
// Up to five uses is ok, because there are five ports.

(* synthesize *)
module sysRegFileFiveInstUses (Empty);
   RegFile#(Bit#(8),Bool) rf <- mkRegFileFull;

   for (Integer i=0; i<5; i=i+1) begin
      Reg#(Bit#(8)) r <- mkRegU;
      mkRegFileFiveInstUses_Sub( rf.sub(r) );
   end
endmodule

// make a module with an instantiation argument which is dynamic
(* synthesize *)
module mkRegFileFiveInstUses_Sub#(Bool b) ();
   rule r;
      $display(b);
   endrule
endmodule

