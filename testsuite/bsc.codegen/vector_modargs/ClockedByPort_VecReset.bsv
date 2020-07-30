import Vector::*;
import Clocks::*;

(* synthesize *)
module sysClockedByPort_VecReset (Vector#(2,Reset) rsts,
                                  (* reset_by="rsts" *)
                                  int v,
                                  Empty ifc);
endmodule

