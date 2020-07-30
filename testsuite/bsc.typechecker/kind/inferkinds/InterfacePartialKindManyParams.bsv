interface Foo#(type a, type b, numeric type c, type d, type e);
endinterface

module mkInterfacePartialKindManyParams(Foo#(Bool,Bool,1,Bool,Bool));
endmodule

