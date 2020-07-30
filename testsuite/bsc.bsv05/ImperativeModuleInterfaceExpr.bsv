module mkFoo(Reg#(Bool));
  Reg#(Bool) ifc;
  ifc = interface Reg
          method Bool _read();
            _read = False;
          endmethod
          method Action _write(Bool val);
            action
            endaction
          endmethod
        endinterface;
  return ifc;
endmodule
