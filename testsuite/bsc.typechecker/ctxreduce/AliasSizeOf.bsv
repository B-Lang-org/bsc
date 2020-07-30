
typedef struct {
   Bit#(id_size) arid;
   Bit#(length_size) arlen;
} AXIparams#(numeric type id_size,
             numeric type length_size)
   deriving (Bits, Eq, FShow);

interface AXI4producers#(type a, type d);
   method ActionValue#(AXIparams#(a,d)) params;
endinterface

module mkRandoms(AXI4producers#(a,d))
   provisos (NumAlias#(param_size,
		       TDiv#(SizeOf#(AXIparams#(a,d)),32)));

      Reg#(Bit#(param_size)) paramLFSR <- mkRegU;
      return ?;
endmodule

