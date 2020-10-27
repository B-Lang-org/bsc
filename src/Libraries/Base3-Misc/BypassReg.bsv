package BypassReg;

// This is a register that allows the value to be bypassed within
// a cycle. The reading and writing methods act like a normal
// register, but there is a third method, bypass, which
// schedules before the _read method. The bypass method allows
// a value to supplied in a cycle to override the stored value
// of the register and be returned from the _read method.
// If there is no write during the cycle, then the bypassed
// value will be stored in the register.

interface WReg#(type a);
   method Action bypass(a x);
   method a _read();
   method Action _write(a x);
endinterface: WReg

module mkBypassReg#(a init)(WReg#(a)) provisos (Bits#(a,asz));

   RWire#(a) _rw0 <- mkRWire();
   Reg#(a)   _reg <- mkReg(init);
   RWire#(a) _rw1 <- mkRWire();

   (* fire_when_enabled, no_implicit_conditions *)
   rule update;
      if (_rw1.wget() matches tagged Valid .x)
         _reg <= x;
      else if (_rw0.wget() matches tagged Valid .x)
         _reg <= x;
   endrule

   method Action bypass(a x);
      _rw0.wset(x);
   endmethod

   method a _read();
      if (_rw0.wget() matches tagged Valid .x)
         return x;
      else
         return _reg;
   endmethod

   method Action _write(a x);
      _rw1.wset(x);
   endmethod

endmodule: mkBypassReg

endpackage: BypassReg
