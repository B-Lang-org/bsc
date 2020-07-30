interface Foo;
    method Bit#(8) bar();
endinterface

import "BVI" foo = module mkFoo(Foo);
  method bar();
endmodule
