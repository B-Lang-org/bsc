typedef struct {
   Bit#(cs)        chip;
   Bit#(ba)        bank;
   Bit#(a)         data;
   } CommandData#(numeric type a, numeric type cs, numeric type ba) deriving (Bits, Eq);

typedef union tagged {
   void                  Idle;
   CommandData#(a,cs,ba) Nop;
   CommandData#(a,cs,ba) Load;
   CommandData#(a,cs,ba) AutoRefresh;
   void                  PrechargeAll;
   CommandData#(a,cs,ba) Precharge;
   CommandData#(a,cs,ba) Activate;
   CommandData#(a,cs,ba) TerminateBurst;
   CommandData#(a,cs,ba) ReadBurst;
   CommandData#(a,cs,ba) WriteBurst;
   } DDR2Command#(numeric type a, numeric type cs, numeric type ba) deriving (Bits, Eq);

interface Command#(numeric type a, numeric type cs, numeric type ba);
   method DDR2Command#(a,cs,ba) myCommand;
endinterface

module mkTest(Command#(a,cs,ba));

  Reg#(DDR2Command#(a,cs,ba)) r <- mkRegU;

  method myCommand = r;

endmodule
