module mkFoo(Reg#(Bool));
  Reg#(Maybe#(Bool)) r();
  mkReg#(Invalid) r_inst(r);
  method Bool _read() if (r matches Invalid);
    _read = False;
  endmethod
  method Action _write(Bool val);
    action
    endaction
  endmethod
endmodule
