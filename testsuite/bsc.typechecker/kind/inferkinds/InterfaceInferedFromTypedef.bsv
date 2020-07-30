interface Foo#(type a);
endinterface

typedef Foo#(1) T;

module mkInterfaceInferedFromTypedef(Foo#(1));
endmodule

