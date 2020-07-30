import RegFile::*;
import Clocks::*;

// Use a port-limited resource (RegFile) in a module instantiation (mkReset).
// Six uses should result in a conflict (G0002), because there are only
// five ports.

(* synthesize *)
module sysRegFileSixInstUses (Empty);
   RegFile#(Bit#(8),Bool) rf <- mkRegFileFull;

   for (Integer i=0; i<6; i=i+1) begin
      Reg#(Bit#(8)) r <- mkRegU;
      mkRegFileSixInstUses_Sub( rf.sub(r) );
   end
endmodule

// make a module with an instantiation argument which is dynamic
(* synthesize *)
module mkRegFileSixInstUses_Sub#(Bool b) ();
   rule r;
      $display(b);
   endrule
endmodule

