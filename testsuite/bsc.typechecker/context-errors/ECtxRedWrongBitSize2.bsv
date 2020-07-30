import Vector::*;

Vector#(8,Bool) v = replicate(True);

Bit#(7) x = pack(v);

