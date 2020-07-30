import Vector::*;
import Clocks::*;

(* synthesize *)
module sysClockedByPort_VecClock (Vector#(2,Clock) clks,
                                  (* clocked_by="clks" *)
                                  int v,
                                  Empty ifc);
endmodule

