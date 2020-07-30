typedef struct {
   Bit#(TSub#(a, 3)) f1;
   Bit#(4)           f2;
   Bit#(4)           f3;
 } S#(type a);

instance Bits#(S#(a), sz)
provisos (Bits#(Bit#(TSub#(a,3)), v1),
          Add#(v1, 8, sz));

   function Bit#(sz) pack(S#(a) x);
      return { x.f1, x.f2, x.f3 };
   endfunction

   function S#(a) unpack(Bit#(sz) x);
      let                         x0 = primSplit(x);
      Tuple2#(Bit#(4), Bit#(4))   x1 = primSplit(x0.snd);
      return (S { f1: x0.fst, f2: x1.fst, f3: x1.snd });
   endfunction

endinstance

