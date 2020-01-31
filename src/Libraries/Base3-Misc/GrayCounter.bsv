////////////////////////////////////////////////////////////////////////////////
//  Filename      : GrayCounter.bsv
//  Author        : Todd Snyder
//  Description   : Gray-Coded Counter with Set/Get methods for Binary and Gray
//                  code
////////////////////////////////////////////////////////////////////////////////
package GrayCounter;

// Notes :

////////////////////////////////////////////////////////////////////////////////
/// Imports
////////////////////////////////////////////////////////////////////////////////
import Clocks            ::*;
import Gray              ::*;

////////////////////////////////////////////////////////////////////////////////
/// Interfaces
////////////////////////////////////////////////////////////////////////////////
interface GrayCounter#(numeric type n);
   method    Action      incr;
   method    Action      decr;
   method    Action      sWriteBin(Bit#(n) value);
   method    Bit#(n)     sReadBin;
   method    Action      sWriteGray(Gray#(n) value);
   method    Gray#(n)	 sReadGray;
   method    Bit#(n)   	 dReadBin;
   method    Gray#(n)  	 dReadGray;
endinterface: GrayCounter

////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
///
/// Implementation
///
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
module mkGrayCounter#(Gray#(n) initval, Clock dClk, Reset dRstN)(GrayCounter#(n))
   provisos(Add#(1, msb, n));

   ////////////////////////////////////////////////////////////////////////////////
   /// Design Elements
   ////////////////////////////////////////////////////////////////////////////////
   Reg#(Gray#(n))                            rsCounter           <- mkRegA(initval);
   PulseWire                                 pwIncrement         <- mkPulseWire;
   PulseWire                                 pwDecrement         <- mkPulseWire;

   ReadOnly#(Gray#(n))                       wdCounterCrossing   <- mkNullCrossingWire(dClk, rsCounter);
   Reg#(Gray#(n))                            rdCounterPre        <- mkRegA(initval, clocked_by dClk, reset_by dRstN);
   Reg#(Gray#(n))                            rdCounter           <- mkRegA(initval, clocked_by dClk, reset_by dRstN);

   ////////////////////////////////////////////////////////////////////////////////
   /// Rules
   ////////////////////////////////////////////////////////////////////////////////
   (* no_implicit_conditions, fire_when_enabled *)
   rule synchronizer;
      rdCounterPre <= wdCounterCrossing;
      rdCounter    <= rdCounterPre;
   endrule

   rule do_increment(pwIncrement && !pwDecrement);
      rsCounter <= grayIncr(rsCounter);
   endrule

   rule do_decrement(!pwIncrement && pwDecrement);
      rsCounter <= grayDecr(rsCounter);
   endrule

   ////////////////////////////////////////////////////////////////////////////////
   /// Interface Connections / Methods
   ////////////////////////////////////////////////////////////////////////////////
   method Action incr;
      pwIncrement.send;
   endmethod

   method Action decr;
      pwDecrement.send;
   endmethod

   method Action sWriteBin(Bit#(n) value);
      rsCounter <= grayEncode(value);
   endmethod

   method Bit#(n) sReadBin;
      return grayDecode(rsCounter);
   endmethod

   method Action sWriteGray(Gray#(n) value);
      rsCounter <= value;
   endmethod

   method Gray#(n) sReadGray;
      return rsCounter;
   endmethod

   method Bit#(n) dReadBin;
      return grayDecode(rdCounter);
   endmethod

   method Gray#(n) dReadGray;
      return rdCounter;
   endmethod

endmodule: mkGrayCounter

endpackage: GrayCounter
