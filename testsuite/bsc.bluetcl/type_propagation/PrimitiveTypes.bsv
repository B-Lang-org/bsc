package PrimitiveTypes;
interface Calc;
 method Bit#(16) result(Bit#(16) a, Bit#(16) b, Bit#(16) c);
endinterface
(* synthesize *) module mkUIntPlain(Calc);
 method Bit#(16) result(Bit#(16) a, Bit#(16) b, Bit#(16) c);
  UInt#(16) x = unpack(a);
  UInt#(16) y = unpack(b);
  UInt#(16) z = unpack(c);
  UInt#(16) sum = x + y;
  return pack((sum * z) ^ (sum >> 3));
 endmethod
endmodule
(* synthesize *) module mkUIntObserved(Calc);
 method Bit#(16) result(Bit#(16) a, Bit#(16) b, Bit#(16) c);
  UInt#(16) x = unpack(a);
  UInt#(16) y = unpack(b);
  UInt#(16) z = unpack(c);
  UInt#(16) sum = unpack(pack(x + y));
  return pack((sum * z) ^ (sum >> 3));
 endmethod
endmodule
(* synthesize *) module mkIntPlain(Calc);
 method Bit#(16) result(Bit#(16) a, Bit#(16) b, Bit#(16) c);
  Int#(16) x = unpack(a);
  Int#(16) y = unpack(b);
  Int#(16) z = unpack(c);
  Int#(16) sum = x + y;
  return pack((sum * z) ^ (sum >> 3));
 endmethod
endmodule
(* synthesize *) module mkIntObserved(Calc);
 method Bit#(16) result(Bit#(16) a, Bit#(16) b, Bit#(16) c);
  Int#(16) x = unpack(a);
  Int#(16) y = unpack(b);
  Int#(16) z = unpack(c);
  Int#(16) sum = unpack(pack(x + y));
  return pack((sum * z) ^ (sum >> 3));
 endmethod
endmodule
interface CompareChoice;
 method Bit#(8) choose(Bit#(8) a, Bit#(8) b, Bit#(8) c, Bit#(8) d, Bit#(8) x, Bit#(8) y, Bool pick);
endinterface
(* synthesize *) module mkPrimitiveBool(CompareChoice);
 method Bit#(8) choose(Bit#(8) a, Bit#(8) b, Bit#(8) c, Bit#(8) d, Bit#(8) x, Bit#(8) y, Bool pick);
  Bool condition = (a == b) && ((c < d) || !pick);
  return condition ? x : y;
 endmethod
endmodule
interface WideProduct; method Bit#(32) result(Bit#(16) a, Bit#(16) b); endinterface
(* synthesize *) module mkRawWideProduct(WideProduct);
 method Bit#(32) result(Bit#(16) a, Bit#(16) b);
  Int#(16) x = unpack(a);
  Int#(16) y = unpack(b);
  return primMul(pack(x),pack(y));
 endmethod
endmodule
(* synthesize *) module mkUnsignedWideProduct(WideProduct);
 method Bit#(32) result(Bit#(16) a, Bit#(16) b);
  UInt#(16) x = unpack(a);
  UInt#(16) y = unpack(b);
  return primMul(pack(x),pack(y));
 endmethod
endmodule
interface RawBit; method Bit#(1) result(Bit#(1) a, Bit#(1) b); endinterface
(* synthesize *) module mkPrimitiveRawBit(RawBit);
 method Bit#(1) result(Bit#(1) a, Bit#(1) b) = a & b;
endmodule
(* synthesize *) module mkPrimitiveRawAdd(Calc);
 method Bit#(16) result(Bit#(16) a, Bit#(16) b, Bit#(16) c) = a + b;
endmodule
interface Shift; method Bit#(16) result(Bit#(16) a, Bit#(4) amount); endinterface
(* synthesize *) module mkPrimitiveShift(Shift);
 method Bit#(16) result(Bit#(16) a, Bit#(4) amount);
  Int#(16) value = unpack(a);
  return pack(value >> amount);
 endmethod
endmodule
(* synthesize *) module mkNumericUnion(Calc);
 method Bit#(16) result(Bit#(16) a, Bit#(16) b, Bit#(16) c);
  Int#(16) signedA = unpack(a);
  Int#(16) signedB = unpack(b);
  UInt#(16) unsignedA = unpack(a);
  UInt#(16) unsignedB = unpack(b);
  Int#(16) signedSum = signedA + signedB;
  UInt#(16) unsignedSum = unsignedA + unsignedB;
  return pack(signedSum >> 3) ^ pack(unsignedSum >> 3);
 endmethod
endmodule
endpackage
