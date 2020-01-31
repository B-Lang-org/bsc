package Cntrs;

export Count(..);
export mkCount;
export ModArith(..);

export UCount(..);
export mkUCount;

// A new wrapper for the Counter module

interface Count#(type t);
   method Action incr    (t val);
   method Action decr    (t val);
   method Action update  (t val);
   method Action _write  (t val);
   method t      _read;
endinterface


// scheduling order
// read < update < ( incr, decr ) < write
module mkCount #(t resetVal) (Count#(t))
   provisos ( Arith#(t)
             ,ModArith#(t)
             ,Bits#(t,st));
   (*hide*)
   let _i <- valueOf(st) != 0 ?  vCount (resetVal) :  vCount0;

   method Action incr    (t val) = _i.incrA(val);
   method Action decr    (t val) = _i.incrB( negate(val) );
   method Action update  (t val) = _i.update(val) ;
   method Action _write  (t val) = _i._write(val) ;
   method t      _read           = _i._read;

endmodule


////////////////////////////////////////////////////////////////////
// Verilog Wrappers
////////////////////////////////////////////////////////////////////
interface VCount#(type t);
   method Action incrA   (t val);
   method Action incrB   (t val);
   method Action update  (t val);
   method Action _write  (t val);
   method t      _read;
endinterface

// Empty hardware
module vCount0 (VCount#(t))
   provisos (ModArith#(t)
             ,Literal#(t)
             ,Bits#(t,st));
   method Action incrA   (t val) = noAction;
   method Action incrB   (t val) = noAction;
   method Action update  (t val) = noAction;
   method Action _write  (t val) = noAction;
   method t      _read           = 0;
endmodule

import "BVI" Counter =
module vCount #(t resetVal) (VCount#(t))
   provisos (ModArith#(t)
             ,Bits#(t,st));

   parameter width = valueOf(st);
   parameter init  = pack(resetVal);
   default_clock (CLK, (*unused*)x);
   default_reset (RST);

   method incrA  (DATA_A) enable(ADDA);
   method incrB  (DATA_B) enable(ADDB);
   method (*reg*) Q_OUT  _read;
   method update (DATA_C) enable(SETC);
   method _write (DATA_F) enable(SETF);

      schedule incrA C incrA;
      schedule incrB C incrB;
      schedule update C update;
      schedule _write SBR _write;
      schedule _read CF _read;
      schedule (incrA) CF (incrB);
      schedule _read SB (incrA, incrB, update, _write);
      schedule update SB (incrA, incrB);
      schedule (incrA, incrB, update) SB _write;

endmodule



// Perhaps this should be in the Prelude
// Define a class for modulo arithmetic on packed representation
//  Fixedpoint can be included
typeclass ModArith#(type t);
endtypeclass

instance ModArith#(Bit#(n));
endinstance
instance ModArith#(Int#(n));
endinstance
instance ModArith#(UInt#(n));
endinstance

////////////////////////////////////////////////////////
//  A counter module whose width is based on elaboration parameter
// And not on any type parameters
///////////////////////////////////
interface UCount;
   method Action update (Integer val);
   method Action _write (Integer val);
   method Action incr   (Integer val);
   method Action decr   (Integer val);
   method Bool isEqual  (Integer val);
   method Bool isLessThan    (Integer val);
   method Bool isGreaterThan (Integer val);
endinterface


module mkUC #( Count#(UInt#(s)) c) (UCount);
   method Action incr (Integer val) 	= c.incr   (fromInteger(val));
   method Action decr (Integer val) 	= c.decr   (fromInteger(val));
   method Action _write (Integer val) 	= c._write (fromInteger(val));
   method Action update (Integer val) 	= c.update (fromInteger(val));

   method Bool isEqual	     (Integer val) 	= (c._read == fromInteger(val));
   method Bool isLessThan    (Integer val) 	= (c._read <  fromInteger(val));
   method Bool isGreaterThan (Integer val) 	= (c._read >  fromInteger(val));
endmodule


// A counter which can count from 0 to maxVal inclusive (maxVal known at compile time):
module mkUCount#(Integer initValue, Integer maxValue) (UCount);
   let _i = ?;
   let ii = fromInteger(initValue);
   let m = maxValue;

   if (m < 0) begin
      errorM ( "a mkUCount instantiated with maxValue = " + integerToString(m) +
               ". mavValue must be >= 0");
   end
   else if (m<2**0)   begin (*hide*) Count#(UInt#(0))  _r <- mkCount(ii); (*hide*)_i <- mkUC(_r); end
   else if (m<2**1)   begin (*hide*) Count#(UInt#(1))  _r <- mkCount(ii); (*hide*)_i <- mkUC(_r); end
   else if (m<2**2)   begin (*hide*) Count#(UInt#(2))  _r <- mkCount(ii); (*hide*)_i <- mkUC(_r); end
   else if (m<2**3)   begin (*hide*) Count#(UInt#(3))  _r <- mkCount(ii); (*hide*)_i <- mkUC(_r); end
   else if (m<2**4)   begin (*hide*) Count#(UInt#(4))  _r <- mkCount(ii); (*hide*)_i <- mkUC(_r); end
   else if (m<2**5)   begin (*hide*) Count#(UInt#(5))  _r <- mkCount(ii); (*hide*)_i <- mkUC(_r); end
   else if (m<2**6)   begin (*hide*) Count#(UInt#(6))  _r <- mkCount(ii); (*hide*)_i <- mkUC(_r); end
   else if (m<2**7)   begin (*hide*) Count#(UInt#(7))  _r <- mkCount(ii); (*hide*)_i <- mkUC(_r); end
   else if (m<2**8)   begin (*hide*) Count#(UInt#(8))  _r <- mkCount(ii); (*hide*)_i <- mkUC(_r); end
   else if (m<2**9)   begin (*hide*) Count#(UInt#(9))  _r <- mkCount(ii); (*hide*)_i <- mkUC(_r); end
   else if (m<2**10)  begin (*hide*) Count#(UInt#(10)) _r <- mkCount(ii); (*hide*)_i <- mkUC(_r); end
   else if (m<2**11)  begin (*hide*) Count#(UInt#(11)) _r <- mkCount(ii); (*hide*)_i <- mkUC(_r); end
   else if (m<2**12)  begin (*hide*) Count#(UInt#(12)) _r <- mkCount(ii); (*hide*)_i <- mkUC(_r); end
   else if (m<2**13)  begin (*hide*) Count#(UInt#(13)) _r <- mkCount(ii); (*hide*)_i <- mkUC(_r); end
   else if (m<2**14)  begin (*hide*) Count#(UInt#(14)) _r <- mkCount(ii); (*hide*)_i <- mkUC(_r); end
   else if (m<2**15)  begin (*hide*) Count#(UInt#(15)) _r <- mkCount(ii); (*hide*)_i <- mkUC(_r); end
   else if (m<2**16)  begin (*hide*) Count#(UInt#(16)) _r <- mkCount(ii); (*hide*)_i <- mkUC(_r); end
   else if (m<2**17)  begin (*hide*) Count#(UInt#(17)) _r <- mkCount(ii); (*hide*)_i <- mkUC(_r); end
   else if (m<2**18)  begin (*hide*) Count#(UInt#(18)) _r <- mkCount(ii); (*hide*)_i <- mkUC(_r); end
   else if (m<2**19)  begin (*hide*) Count#(UInt#(19)) _r <- mkCount(ii); (*hide*)_i <- mkUC(_r); end
   else if (m<2**20)  begin (*hide*) Count#(UInt#(20)) _r <- mkCount(ii); (*hide*)_i <- mkUC(_r); end
   else if (m<2**21)  begin (*hide*) Count#(UInt#(21)) _r <- mkCount(ii); (*hide*)_i <- mkUC(_r); end
   else if (m<2**22)  begin (*hide*) Count#(UInt#(22)) _r <- mkCount(ii); (*hide*)_i <- mkUC(_r); end
   else if (m<2**23)  begin (*hide*) Count#(UInt#(23)) _r <- mkCount(ii); (*hide*)_i <- mkUC(_r); end
   else if (m<2**24)  begin (*hide*) Count#(UInt#(24)) _r <- mkCount(ii); (*hide*)_i <- mkUC(_r); end
   else if (m<2**25)  begin (*hide*) Count#(UInt#(25)) _r <- mkCount(ii); (*hide*)_i <- mkUC(_r); end
   else if (m<2**26)  begin (*hide*) Count#(UInt#(26)) _r <- mkCount(ii); (*hide*)_i <- mkUC(_r); end
   else if (m<2**27)  begin (*hide*) Count#(UInt#(27)) _r <- mkCount(ii); (*hide*)_i <- mkUC(_r); end
   else if (m<2**28)  begin (*hide*) Count#(UInt#(28)) _r <- mkCount(ii); (*hide*)_i <- mkUC(_r); end
   else if (m<2**29)  begin (*hide*) Count#(UInt#(29)) _r <- mkCount(ii); (*hide*)_i <- mkUC(_r); end
   else if (m<2**30)  begin (*hide*) Count#(UInt#(30)) _r <- mkCount(ii); (*hide*)_i <- mkUC(_r); end
   else if (m<2**31)  begin (*hide*) Count#(UInt#(31)) _r <- mkCount(ii); (*hide*)_i <- mkUC(_r); end
   else if (m<2**32)  begin (*hide*) Count#(UInt#(32)) _r <- mkCount(ii); (*hide*)_i <- mkUC(_r); end
   else begin
      errorM ( "a mkUCount instantiated with maxValue = " + integerToString(m) +
               ". mavValue must be <= 2**32");
   end

   return _i;
endmodule


endpackage
