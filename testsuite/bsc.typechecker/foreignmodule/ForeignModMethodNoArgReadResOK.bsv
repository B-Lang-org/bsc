interface Foo;
    method Bit#(8) bar();
endinterface

import "BVI" foo = module mkFoo(Foo);
  method baz bar();
endmodule
