// An example which tests the splitting of constants (in the optimization
// of PrimAnd/PrimOr/PrimXOr on concats, constants, and undefs).
//
// This example creates the expression:
//
//   { e::Bit#(24), 0::Bit#(12) } `op` { 2::Bit#(26), ?::Bit#(10) }
//
// The constant 2 is split into the high 24 bits and the low 2 bits.
// A bug was causing the split to put the low bits in the high chunk.
// This resulted in the register "zza" being assigned 36'hAAA2AA2AA,
// where the correct value is 36'hAAAAAAAAA.  Or, with "-unspecified-to 0",
// the value is 36'h800800800.
//

import Vector::*;

typedef enum {ASAP, WAIT} QOS deriving(Bounded, Bits, Eq);

typedef struct {QOS       qos;
		Maybe#(a) data;
		} Wrap#(type a) deriving (Eq, Bits, Bounded);


(* synthesize *)
module sysConcatOpt3 (Empty);

   Wrap#(Bit#(10))   wrapInvalid = Wrap {qos: WAIT, data: tagged Invalid };
   Wrap#(Bit#(10))   wrapValid0  = Wrap {qos: WAIT, data: tagged Valid 0 };

   Reg#(Vector#(3, Wrap#(Bit#(10))))    rg   <- mkRegU;

   Reg#(Bit#(8)) counter <- mkReg(0);

   rule do_test;
      counter <= counter + 1;
      case (counter)
         0 : begin
	        rg <= replicate(wrapInvalid);
	     end
         1 : begin
	        $display("rg = %h", rg);
	     end
         2 : begin
	        rg <= replicate(wrapValid0);
	     end
         3 : begin
	        $display("rg = %h", rg);
	     end
         default: $finish(0);
      endcase
   endrule

endmodule

