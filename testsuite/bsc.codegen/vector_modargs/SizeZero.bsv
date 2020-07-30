import Vector::*;

typedef 0 N;

(* synthesize *)
(* gate_input_clocks="v_clk" *)
module sysSizeZero (Clock clk,
                    Vector#(N, Clock) v_clk,
                    (* clocked_by="c" *)
                    Vector#(N, Reset) v_rst,
                    Empty ifc);
endmodule

