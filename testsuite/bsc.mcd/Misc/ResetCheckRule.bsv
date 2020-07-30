(* synthesize *)
module sysResetCheckRule#(Reset rst)(Empty);

Reg#(Bit#(8)) r <- mkReg(0);
Reg#(Bit#(8)) s();
mkReg#(0) the_s(s, reset_by(rst));

rule test;
  $display(r + s);
  $finish(0);
endrule

endmodule

