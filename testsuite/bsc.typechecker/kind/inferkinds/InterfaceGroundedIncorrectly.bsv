interface Foo#(type a);
endinterface

module mkInterfaceGroundedIncorrectly(Foo#(1));
endmodule

