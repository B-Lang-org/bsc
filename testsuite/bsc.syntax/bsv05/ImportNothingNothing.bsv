interface Foo;
  method Bit#(16) test();
endinterface

import "BVI" Broken = module broken(Foo);
  method test();
endmodule
