module mkBypassReg#(a init)(Reg#(a)) provisos(Bits#(a,sa));
  Reg#(a) r();
  mkReg#(init) the_r(r);

  RWire#(a) rw();
  mkRWire the_rw(rw);

  (* fire_when_enabled *)
  rule propagate (rw.wget() matches tagged Valid .v);
     r <= v;
  endrule

  method Action _write(a val);
    rw.wset(val);
  endmethod

  method _read();
    case (rw.wget()) matches
      Invalid : return r;
      tagged Valid .v : return v;
    endcase
  endmethod

endmodule

(* synthesize *)
module sysBypassReg(Reg#(Bit#(16)));
  Reg#(Bit#(16)) r();
  mkBypassReg#(0) the_r(r);
  return (r);
endmodule
