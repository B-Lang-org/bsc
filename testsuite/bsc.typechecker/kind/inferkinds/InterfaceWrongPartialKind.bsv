interface Foo#(numeric type a);
endinterface

module mkInterfaceWrongPartialKind(Foo#(Bool));
endmodule

