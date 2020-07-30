// this file has multiple type errors to test parallel type-checking

Action a = $display("foo");

Bit#(16) b = a;

Bit#(32) c = b;

Bit#(32) d = zeroExtend(b); // this should be ok

Bit#(16) e = truncate(c); // this should be ok

Action f = c;



