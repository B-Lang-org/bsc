interface Foo;
  method ActionValue#(Bool) m();
endinterface: Foo

module foo(Foo);
  method m();
    begin
    end
  endmethod
endmodule: foo

