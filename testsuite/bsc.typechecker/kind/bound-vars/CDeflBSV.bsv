interface IFCStar#(type a);
    method Bool foo(a x);
endinterface

module mkIFC(IFCStar#(a));
  Bit#(a) x = 0;
endmodule

