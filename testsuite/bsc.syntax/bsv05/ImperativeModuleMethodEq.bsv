module mkFoo(Reg#(Bool));
  method Bool _read() = False;
  method Action _write(Bool val);
    action
    endaction
  endmethod
endmodule
