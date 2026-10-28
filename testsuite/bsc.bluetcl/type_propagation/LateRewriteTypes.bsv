package LateRewriteTypes;
typedef struct { Bit#(4) hi; Bit#(4) lo; } Payload deriving (Bits, Eq);
interface I; method Bit#(4) result(Bit#(8) x, Bit#(3) n, Bit#(8) y, Bool p); endinterface
(* synthesize *) module mkSignedShiftSlice(I);
 method Bit#(4) result(Bit#(8) x, Bit#(3) n, Bit#(8) y, Bool p);
  Int#(8) sx = unpack(x);
  Payload s = unpack(pack(sx >> n));
  return s.lo;
 endmethod
endmodule
(* synthesize *) module mkUnsignedShiftSlice(I);
 method Bit#(4) result(Bit#(8) x, Bit#(3) n, Bit#(8) y, Bool p);
  Payload s = unpack(x >> n);
  return s.lo;
 endmethod
endmodule
(* synthesize *) module mkSignedShiftConstSlice(I);
 method Bit#(4) result(Bit#(8) x, Bit#(3) n, Bit#(8) y, Bool p);
  Int#(8) sx = unpack(x);
  Payload s = unpack(pack(sx >> 2));
  return s.lo;
 endmethod
endmodule
(* synthesize *) module mkMuxSlice(I);
 method Bit#(4) result(Bit#(8) x, Bit#(3) n, Bit#(8) y, Bool p);
  Payload s = unpack(p ? x : y);
  return s.lo;
 endmethod
endmodule
(* synthesize *) module mkNegSlice(I);
 method Bit#(4) result(Bit#(8) x, Bit#(3) n, Bit#(8) y, Bool p);
  Payload s = unpack(-x);
  return s.lo;
 endmethod
endmodule
endpackage
