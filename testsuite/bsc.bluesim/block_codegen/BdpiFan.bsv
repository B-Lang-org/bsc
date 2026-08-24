// Two separately-synthesized modules importing DIFFERENT BDPI
// functions, for the shared-simdir -c fan-out test: each module's
// generated .cxx must carry declarations for exactly the functions
// it calls, with no shared imported_BDPI_functions.h to fight over.

import "BDPI" function Bit#(32) bdpi_leaf_fn(Bit#(32) x);
import "BDPI" function Bit#(32) bdpi_top_fn(Bit#(32) x);

interface Leaf;
    method Bit#(32) look(Bit#(32) x);
endinterface

(* synthesize *)
module mkBdpiLeaf (Leaf);
    method look(x) = bdpi_leaf_fn(x);
endmodule

(* synthesize *)
module mkBdpiTop (Empty);
    Leaf sub <- mkBdpiLeaf;
    Reg#(Bit#(32)) cnt <- mkReg(0);

    rule step;
        cnt <= cnt + 1;
        if (cnt == 4) begin
            $display("top=%0d leaf=%0d",
                     bdpi_top_fn(cnt), sub.look(cnt));
            $finish(0);
        end
    endrule
endmodule
