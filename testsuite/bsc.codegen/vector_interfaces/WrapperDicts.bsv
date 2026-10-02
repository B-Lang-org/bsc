package WrapperDicts;

import Vector::*;

typedef struct {
   Bit#(n) value;
} Encoded#(numeric type n);

// This local, polymorphic instance is needed by the generated wrapper.
// Its nontrivial encoding makes using the wrong dictionary observable.
instance Bits#(Encoded#(n), n);
   function Bit#(n) pack(Encoded#(n) x) = ~x.value;
   function Encoded#(n) unpack(Bit#(n) x) = Encoded { value: ~x };
endinstance

typedef struct {
   Bit#(4) hi;
   Bit#(4) lo;
} Derived deriving (Bits);

interface EncodedRegs;
   interface Vector#(4, Reg#(Encoded#(8))) regs;
endinterface

interface DerivedRegs;
   interface Vector#(4, Reg#(Derived)) regs;
endinterface

// A legal source name must not collide with a lifted dictionary either.
Bit#(8) _lifted_dict0 = 8'h12;

(* synthesize *)
module mkEncodedRegs(EncodedRegs);
   Vector#(4, Reg#(Encoded#(8))) rs <-
      replicateM(mkReg(Encoded { value: _lifted_dict0 }));
   interface regs = rs;
endmodule

(* synthesize *)
module mkDerivedRegs(DerivedRegs);
   Vector#(4, Reg#(Derived)) rs <-
      replicateM(mkReg(Derived { hi: 1, lo: 2 }));
   interface regs = rs;
endmodule

endpackage
