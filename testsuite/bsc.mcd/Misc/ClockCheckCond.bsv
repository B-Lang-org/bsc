interface Test;
  method Bit#(8) out();
endinterface

(* synthesize *)
module sysClockCheckCond#(Clock c)(Test);

  Reg#(Bool) x();
  mkRegU the_x(x, clocked_by c);

  Reg#(Bit#(8)) y();
  mkReg#(0) the_y(y);

  method out() if(x);
    return(y);
  endmethod
endmodule
    
