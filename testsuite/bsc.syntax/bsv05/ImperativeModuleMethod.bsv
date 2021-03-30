module mkFoo(Reg#(Bool));
  method Bool _read();
    _read = False;
  endmethod
  method Action _write(Bool val);
    action
    endaction
  endmethod
endmodule
