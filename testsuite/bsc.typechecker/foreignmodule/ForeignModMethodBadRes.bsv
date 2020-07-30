interface Foo;
    method Integer bar(Bit#(8) arg);
endinterface

import "BVI" foo = module mkFoo(Foo);
  method baz bar(glurph);
endmodule
