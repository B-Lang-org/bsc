module mkFoo(Reg#(Bool));
  Reg#(Bool) r();
  mkReg#(False) r_inst(r);
  method Bool _read() if (r);
    _read = False;
  endmethod
  method Action _write(Bool val);
    action
    endaction
  endmethod
endmodule
