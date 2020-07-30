import Probe::*;

(* synthesize *)
module mkCommentOnSubmodProbe();

   (* doc = "This is a probe" *)
   Probe#(Bool) r();
   mkProbe the_r(r);

   rule do_it;
      r <= True;
   endrule

endmodule

