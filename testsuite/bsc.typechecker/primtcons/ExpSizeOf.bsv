
typedef struct {
    addr a;
    Bit#(TLog#(SizeOf#(dta))) o;
} CRAddr #(type addr, type dta);

instance Bits#(CRAddr#(addr, dta), _v100)
  provisos (Bits#(addr, _v101),
            Bits#(Bit#(TLog#(SizeOf#(dta))), _v104),
            Add#(_v101, _v104, _v100));

    function Bit#(_v100) pack(CRAddr#(addr, dta) _x);
      return (primConcat(pack(_x.a), pack(_x.o)));
    endfunction

    function CRAddr#(addr, dta) unpack(Bit#(_v100) _x);
      function fn(_arg);
         return (CRAddr { a : unpack(_arg.fst), o : unpack(_arg.snd)});
      endfunction
      return fn(primSplit(_x));
    endfunction

endinstance

