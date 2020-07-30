
`ifdef INC1
`include "include1.inc"
`endif

`ifdef SYNTAXERROR
import Foo::*
`endif

`ifdef CIRCERROR
import Foo::*;
`endif

