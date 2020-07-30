interface Foo;
  method ActionValue#(Bool) m();
endinterface: Foo

module foo(Foo);
  method m();
    actionvalue
    endactionvalue
  endmethod
endmodule: foo

