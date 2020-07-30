(* synthesize *)
module sysResetOf(Reset rst1, Empty ifc);

Reset rst <- exposeCurrentReset();
Reg#(Bool) r <- mkReg(True);

Reg#(Bool) s();
mkReg#(True) the_s(s, reset_by(rst1));

Reg#(Bool) t();
mkReg#(True) the_t(t, reset_by(resetOf(r)));

rule test;
  if((resetOf(s) != (resetOf(r))) && (resetOf(r) == resetOf(t)) &&
     (resetOf(0) == noReset)) 
     $display("PASS");
  else
     $display("FAIL");
  $finish(0);
endrule

endmodule
