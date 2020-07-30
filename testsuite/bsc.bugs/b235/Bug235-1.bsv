interface Foo;
  method Action m();
endinterface: Foo

module foo(Foo);
  method m();
    action
      begin
      end
    endaction
  endmethod
endmodule: foo

