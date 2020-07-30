interface Foo;
    method Bit#(8) bar(Bit#(8) arg);
endinterface

import "BVI" foo = module mkFoo(Foo);
  method baz bar();
endmodule
