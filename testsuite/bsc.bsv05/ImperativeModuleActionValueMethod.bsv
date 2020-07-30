interface AVIfc;
   method ActionValue#(Bool) m();
endinterface

module mkFoo(AVIfc);
  Reg #(Bool) r();
  mkReg#(True) r_inst(r);
  method ActionValue#(Bool) m();
     return r;
  endmethod
endmodule
