typedef struct {Bit#(a) foo;} Foo#(type a);

Foo#(3) x = Foo {foo:0};
Foo#(4) y = zeroExtend(x);
