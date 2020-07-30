interface Test;
  method Bit#(8) out();
endinterface

(* synthesize *)
module sysResetCheckMethod#(Reset rst)(Test);

Reg#(Bit#(8)) r <- mkReg(0);
Reg#(Bit#(8)) s();
mkReg#(0) the_s(s, reset_by(rst));

method out();
  return (r+s);
endmethod

endmodule

