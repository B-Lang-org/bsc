interface IFC#(type n , type k);
endinterface

module mkTest (IFC#(n,k));
  Reg#(Bit#(k)) r();
  mkReg#(0) i_r(r);
endmodule

