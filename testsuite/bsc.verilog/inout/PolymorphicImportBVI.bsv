interface Foo#(type t);
  interface Inout#(t) pin;
endinterface

import "BVI" foo =
module vFoo(Foo#(t))
  provisos (Bits#(t, st));

  default_clock no_clock;
  default_reset no_reset;

  parameter     width = valueOf(st);

  ifc_inout     pin(PIN);
endmodule

