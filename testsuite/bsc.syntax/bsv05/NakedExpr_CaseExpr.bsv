typedef enum {Foo, Bar, Foobar} FooNum deriving(Bits, Eq);

module mkCase(Empty);
  Reg#(int) r <- mkReg(0);
  Reg#(FooNum) r_foo <- mkReg(Foo);

  rule change_foo;
    r_foo <= case (r_foo) matches
                Foo: Bar;
                Bar: r == 42 ? Foobar : Bar;
                Foobar: Foobar;
             endcase;
  endrule
endmodule
