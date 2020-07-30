package XReg;

interface XReg#(type a, type b);
   method a _read;
   method Action _write (a value);
   interface Reg#(b) x;
endinterface

module mkXReg#(a init)(XReg#(a, b))
   provisos (Bits#(a, sa), Bits#(b, sb), Add#(ignore,sa,sb));
   let _m = liftModule(mkReg(init));
   Reg#(a) _r();
   _m __(_r); // the "__" makes this instantiation anonymous

   method _read  = _r._read;
   method _write = _r._write;
   
   interface Reg x;
      method b _read;
	 return unpack({0, pack(_r)});
      endmethod
      method Action _write (b value);
	 let x = unpack(truncate(pack(value)));
	 _r <= x;
      endmethod
   endinterface

endmodule
   
endpackage