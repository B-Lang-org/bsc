module mkConfigReg#(a init)(Reg#(a)) provisos(Bits#(a,sa));
  Reg#(a) r();
  mkReg#(init) the_r(r);

  RWire#(a) rw();
  mkRWire the_rw(rw);

  (* fire_when_enabled *)
  rule propagate (rw.wget() matches tagged Valid .v);
     r <= v;
  endrule

  method _read();
    return(r);
  endmethod

  method Action _write(a val);
    rw.wset(val);
  endmethod
endmodule

(* synthesize *)
module sysConfigReg(Reg#(Bit#(16)));
  Reg#(Bit#(16)) r();
  mkConfigReg#(0) the_r(r);
  return (r);
endmodule
