package SyncFIR;

import FIRMain::*;

import Vector::*;

/*********************    Modular FIR Filter      *****************************/
/*                                                                            */
/*  Rather than defining a single FIR Filter the approach is to define a      */
/*  parameterized module which can be instantiated for any number of          */
/*  and any (arithmetic) type. This is eased by the regularity of a FIR       */
/*  pipeline. For a FIR filter with N coefficients the pipeline will be:      */
/*                                                                            */
/*           (FIRHead) --> (FIRBody * (N-2)) --> (FIRBody)                    */
/*                                                                            */
/*                                                                            */
/******************************************************************************/


// The start of a Direct-Form FIR Pipeline

module mkFIRHead (FIRHead#(arith_t))
  provisos (Bits#(arith_t, sz), Arith#(arith_t));
  
  Reg#(arith_t)  r0   <- mkReg(0);
  Reg#(arith_t)  d0   <- mkReg(0); // Advanced users can replace registers d0, d1 
  Reg#(arith_t)  d1   <- mkReg(0); // with RWire to improve latency (in the Head only).
  Reg#(arith_t)  k    <- mkReg(0);

  method Action setCoef(arith_t n);
    action
      k <= n;
    endaction
  endmethod
  
  method ActionValue#(Tuple2#(arith_t, arith_t)) fir(arith_t data);
    actionvalue
      d0 <= data;
      d1 <= d0;
      r0 <= d1 * k;
      return tuple2(d1, r0);
    endactionvalue
  endmethod

endmodule: mkFIRHead


//The body of a Direct-Form FIR pipeline. Replicated N-2 times
module mkFIRBody (FIRBody#(arith_t))
  provisos (Bits#(arith_t, sz), Arith#(arith_t));
  
  Reg#(arith_t)  r1   <- mkReg(0);
  Reg#(arith_t)  d1   <- mkReg(0);
  Reg#(arith_t)  d2   <- mkReg(0);
  Reg#(arith_t)  k    <- mkReg(0);
  
  method Action setCoef(arith_t n);
    action
      k <= n;
    endaction
  endmethod
  
  method ActionValue#(Tuple2#(arith_t, arith_t)) fir(arith_t d, arith_t r);
    actionvalue
      d1 <= d;
      d2 <= d1;
      r1 <= (d2 * k) + r;
      return tuple2(d2, r1);
    endactionvalue
  endmethod
  
endmodule: mkFIRBody

//The tail of the FIR filter. Final output value is available here.

module mkFIRTail (FIRTail#(arith_t))
  provisos (Bits#(arith_t, sz), Arith#(arith_t));
  
  Reg#(arith_t)   r1   <- mkReg(0);
  Reg#(arith_t)   d1   <- mkReg(0);
  Reg#(arith_t)   d2   <- mkReg(0);
  Reg#(arith_t)   k    <- mkReg(0);
  
  method Action setCoef(arith_t n);
    action
      k <= n;
    endaction
  endmethod
  
  method ActionValue#(arith_t) fir(arith_t d, arith_t r);
    actionvalue
      d1 <= d;
      d2 <= d1;
      r1 <= (d2 * k) + r;
      return r1;
    endactionvalue
  endmethod
  
  
endmodule: mkFIRTail

//Builds a modular FIR pipeline out of the components above.
//The FIRBodies are stored in a Vector
//The output only becomes valid once the pipeline is full
//After changing coefficients the pipeline must refill

module mkModularFIR (FIRFilter#(arith_t, m))
  provisos (Bits#(arith_t, sz), Arith#(arith_t),  Add#(n,2,m)); //n = m - 2
  
   Reg#(Bool)      valid       <- mkReg(False);
   Reg#(UInt#(m))  counter     <- mkReg(0);
   Integer         length_     = valueOf(n);
  
  FIRHead#(arith_t)              h      <- mkFIRHead;
  Vector#(n, FIRBody#(arith_t))   bs     <- replicateM(mkFIRBody);
  FIRTail#(arith_t)              t      <- mkFIRTail;
 
  method Action setCoefs(Vector#(m, arith_t) ks);
    action
      h.setCoef(ks[0]);
      Integer i;
      for (i = 0; i < length_; i = i + 1)
      begin
        FIRBody#(arith_t) b;
        b = bs[i];
        b.setCoef(ks[i + 1]);
      end
      t.setCoef(ks[i]);
      counter <= 0;
      valid <= False;
    endaction
  endmethod

  method ActionValue#(Maybe#(arith_t)) fir(arith_t data);
    actionvalue
    
      Tuple2#(arith_t, arith_t) tmp <- h.fir(data);
      
      for (Integer i = 0; i < length_; i = i + 1)
      begin
        FIRBody#(arith_t) b;
        b = bs[i];
        tmp <- b.fir(tmp.fst(), tmp.snd());
      end
      
      arith_t res <- t.fir(tmp.fst(), tmp.snd());
      
      //Workaround of Bug 571. Can't use if to return in actionvalue
      case (valid) matches
        True:   return Valid(res);
	False:
	begin
	  if (counter >= fromInteger((length_ + 2) * 2)) 
	    valid <= True;
	  else
	    counter <= counter + 1;
	  return Invalid;
	end
      endcase
    endactionvalue
  endmethod
 
endmodule

endpackage: SyncFIR
