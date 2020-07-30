interface Foo;
    method Action bar(Bit#(8) arg);
endinterface

import "BVI" foo = module mkFoo(Foo);
  method bar(glurph) enable(baz);
endmodule
