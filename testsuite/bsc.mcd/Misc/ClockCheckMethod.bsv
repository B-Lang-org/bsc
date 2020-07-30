interface Test;
  method Bit#(8) out();
endinterface

(* synthesize *)
module sysClockCheckMethod#(Clock c)(Test);

Reg#(Bit#(8)) r <- mkReg(0);
Reg#(Bit#(8)) s();
mkRegU the_s(s, clocked_by(c));

method out();
  return (r+s);
endmethod

endmodule

