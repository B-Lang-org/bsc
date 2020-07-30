module mkModuleParameters#(parameter Bit#(16) k)(Empty);
  Empty params();
  mkParams #(5) the_params(params);
endmodule

module mkParams#(parameter Bit#(16) k)(Empty);
endmodule
