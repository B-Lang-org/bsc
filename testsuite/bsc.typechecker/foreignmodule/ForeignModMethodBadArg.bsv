interface Foo;
    method Bit#(8) bar(Integer arg);
endinterface

import "BVI" foo = module mkFoo(Foo);
  method baz bar(glurph);
endmodule
