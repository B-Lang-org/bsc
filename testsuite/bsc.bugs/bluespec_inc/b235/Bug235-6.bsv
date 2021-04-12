interface Foo;
  method ActionValue#(Bool) m();
endinterface: Foo

module foo(Foo);
  method m();
    actionvalue
      begin
      end
    endactionvalue
  endmethod
endmodule: foo

