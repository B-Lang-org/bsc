(* synthesize *)
module sysResetOfResets(Reset rst1, Empty ifc);

Reset rst <- exposeCurrentReset();
Reg#(Bool) r <- mkReg(True);

Reg#(Bool) s();
mkReg#(True) the_s(s, reset_by(rst1));

Reg#(Bool) t();
mkReg#(True) the_t(t, reset_by(resetOf(r)));

let sr = s && r;

rule test;
  $display(resetOf(s) == resetOf(sr));
  $display(resetOf(r) == resetOf(sr));
  $finish(0);
endrule

endmodule
