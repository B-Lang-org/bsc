package ModuleArgument;

module [Module] helloWorld#(Module#(Empty) mod)(Empty);
  let e <- mod;
endmodule

module [m] fooBar#(m#(Empty) mod)(Empty)
  provisos (IsModule#(m, c));
  let e <- mod;
endmodule

endpackage
