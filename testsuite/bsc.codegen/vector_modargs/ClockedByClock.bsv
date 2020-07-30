import Vector::*;

// This should fail because the attribute is not allowed for clocks

(* synthesize *)
module sysClockedByClock (Clock c,
                          (* clocked_by="c" *)
                          Clock c2,
                          Empty ifc);
endmodule

