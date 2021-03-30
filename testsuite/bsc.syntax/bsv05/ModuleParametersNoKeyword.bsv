interface Bogus#(type a);
endinterface

module mkModuleParameters#(Bit#(16) k)(Bogus#(Bit#(16)));
  Empty params();
  mkParams #(5) the_params(params);
endmodule

module mkParams#(parameter Bit#(16) k)(Empty);
endmodule
