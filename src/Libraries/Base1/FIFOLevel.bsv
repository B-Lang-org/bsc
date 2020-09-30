package FIFOLevel ;

import FIFOF_ :: * ;
import GetPut :: * ;


export FIFOLevelIfc(..) ;
export mkFIFOLevel ;
export mkGFIFOLevel ;
export SyncFIFOLevelIfc(..) ;
export mkSyncFIFOLevel ;

export FIFOCountIfc(..) ;
export mkFIFOCount ;
export mkGFIFOCount ;
export SyncFIFOCountIfc(..) ;
export mkSyncFIFOCount ;
export mkGSyncFIFOCount ;


//@ \subsubsection{Level FIFO}
//@ \index{Clocks@\te{LevelFIFO} (package)|textbf}
//@
//@ The BSV \te{LevelFIFO} library provides FIFO interfaces and modules
//@ which include methods to indicate the level or the current number
//@ of items stored in the FIFO.  Two versions are included in this
//@ package, the first for a single clock, and the second for
//@ dual clocks.   The interface and module definitions are detailed
//@ below.
//@


//@ \index{FIFOLevelIfc@\te{FIFOLevelIfc} (interface)|textbf}
//@ In addition to common FIFO methods, the \te{FIFOLevelIfc}
//@ interface defines methods to compare the current level to
//@ \te{Integer} constants.
//@ Note that \te{FIFOLevelIfc} interface has a parameter for the
//@ fifoDepth.  This numeric type parameter is needed, since the width
//@ of the counter is dependent on the FIFO depth.

//@ # 15
interface FIFOLevelIfc#( type a_type, numeric type fifoDepth ) ;
   method Action enq( a_type x1 );
   method Action deq();
   method a_type first();
   method Action clear();

   method Bool notFull ;
   method Bool notEmpty ;

   method Bool isLessThan   ( Integer c1 ) ;
   method Bool isGreaterThan( Integer c1 ) ;

   //   method UInt#(TLog#(fifoDepth)) maxDepth ;
endinterface


//@
//@ \index{mkFIFOLevel@\te{mkFIFOLevel} (module)|textbf}
//@ The module mkFIFOLevel
//@
//@ # 3
module mkFIFOLevel( FIFOLevelIfc#(a_type, fifoDepth) )
   provisos( Bits#(a_type, sa ),          // Can convert to Bits
            Log#(TAdd#(fifoDepth,1),cntSize)
            ) ;  // Get the width from the depth

   Integer ififoDepth = (valueOf( fifoDepth ) < 3 ?
                         (error ("mkFIFOLevel: fifoDepth must be greater than 2. " +
                                 "Specified depth is " + integerToString( valueOf(fifoDepth)) + "." ) ) :
                         valueOf( fifoDepth ) );

   FIFOLevel_INT#(a_type, cntSize)
      _fifoLevel <- vbFIFOLevel( ififoDepth ) ;

   Reg#(Bool) levelsValid <- mkReg(True);
   PulseWire doResetEnq <- mkPulseWire;
   PulseWire doResetDeq <- mkPulseWire;
   PulseWire doResetClr <- mkPulseWire;

   Bool doReset = doResetEnq || doResetDeq || doResetClr;

   rule reset(doReset);
     levelsValid <= True;
   endrule

   method Action enq( a_type x ) if ( _fifoLevel.i_notFull ) ;
      _fifoLevel.enq( x ) ;
      levelsValid <= False;
      doResetEnq.send;
   endmethod

   method Action deq if ( _fifoLevel.i_notEmpty ) ;
      _fifoLevel.deq ;
      levelsValid <= False;
      doResetDeq.send;
   endmethod

   method first if ( _fifoLevel.i_notEmpty ) ;
      return _fifoLevel.first ;
   endmethod

   method Action clear;
     _fifoLevel.clear ;
     levelsValid <= False;
     doResetClr.send;
   endmethod

   method notFull = _fifoLevel.notFull ;
   method notEmpty = _fifoLevel.notEmpty ;

   method Bool isLessThan ( Integer c1 ) if (levelsValid) ;
      return rangeTest( _fifoLevel.i_count, c1, \< , 1, ififoDepth  , "isLessThan" ) ;
   endmethod

   method Bool isGreaterThan ( Integer c1 ) if (levelsValid) ;
      return rangeTest( _fifoLevel.i_count, c1, \> , 0, ififoDepth -1  , "isGreaterThan" ) ;
   endmethod

//    method maxDepth ;
//       return fromInteger( ififoDepth );
//    endmethod

endmodule

module mkGFIFOLevel#(Bool ugenq, Bool ugdeq, Bool ugcount)( FIFOLevelIfc#(a_type, fifoDepth) )
   provisos( Bits#(a_type, sa ),          // Can convert to Bits
            Log#(TAdd#(fifoDepth,1),cntSize)
            ) ;  // Get the width from the depth

   Integer ififoDepth = (valueOf( fifoDepth ) < 3 ?
                         (error ("mkFIFOLevel: fifoDepth must be greater than 2. " +
                                 "Specified depth is " + integerToString( valueOf(fifoDepth)) + "." ) ) :
                         valueOf( fifoDepth ) );

   FIFOLevel_INT#(a_type, cntSize)
      _fifoLevel <- vbFIFOLevel( ififoDepth ) ;


   Action enqGuard = noAction ;
   Action deqGuard = noAction ;
   Action clrGuard = noAction ;
   Bool   levelsValid = ? ;
   if ( ugcount )
      begin
         enqGuard = noAction ;
         deqGuard = noAction ;
         clrGuard = noAction ;
         levelsValid = True ;
      end
   else
      begin
         Reg#(Bool) levelsValid_virtual_Reg <- mkReg(True);
         PulseWire doResetEnq <- mkPulseWire;
         PulseWire doResetDeq <- mkPulseWire;
         PulseWire doResetClr <- mkPulseWire;

         Bool doReset = doResetEnq || doResetDeq || doResetClr;

         rule reset(doReset);
            levelsValid_virtual_Reg <= True;
         endrule
         enqGuard = (action
                        levelsValid_virtual_Reg <= False;
                        doResetEnq.send;
                     endaction);
         deqGuard = (action
                        levelsValid_virtual_Reg <= False;
                        doResetDeq.send;
                     endaction);
         clrGuard = (action
                        levelsValid_virtual_Reg <= False;
                        doResetClr.send;
                     endaction);
         levelsValid = levelsValid_virtual_Reg._read ;
      end

   method Action enq( a_type x ) if ( _fifoLevel.i_notFull || ugenq ) ;
      _fifoLevel.enq( x ) ;
      enqGuard ;
   endmethod

   method Action deq if ( _fifoLevel.i_notEmpty || ugdeq) ;
      _fifoLevel.deq ;
      deqGuard ;
   endmethod

   method first if ( _fifoLevel.i_notEmpty || ugdeq) ;
      return _fifoLevel.first ;
   endmethod

   method Action clear;
      _fifoLevel.clear ;
      clrGuard ;
   endmethod

   method notFull = _fifoLevel.notFull ;
   method notEmpty = _fifoLevel.notEmpty ;

   method Bool isLessThan ( Integer c1 ) if (levelsValid) ;
      return rangeTest( _fifoLevel.i_count, c1, \< , 1, ififoDepth  , "isLessThan" ) ;
   endmethod

   method Bool isGreaterThan ( Integer c1 ) if (levelsValid) ;
      return rangeTest( _fifoLevel.i_count, c1, \> , 0, ififoDepth -1  , "isGreaterThan" ) ;
   endmethod
endmodule

//@ \index{SyncFIFOLevelIfc@\te{SyncFIFOLevelIfc} (interface)|textbf}
//@ In addition to common FIFO methods, the \te{SyncFIFOLevelIfc}
//@ interface defines methods to compare the current level to
//@ \te{Integer} constants.  Methods are provided for both the source
//@ (enqueue side) and destination (dequeue side) clock domains.
//@
//@ Note that \te{SyncFIFOLevelIfc} interface has a parameter for the
//@ fifoDepth.  This numeric type parameter is needed, since the width
//@ of the counter is dependent on the FIFO depth.

//@ # 19
interface SyncFIFOLevelIfc#( type a_type, numeric type fifoDepth ) ;
   method Action enq ( a_type sendData ) ;
   method Action deq () ;
   method a_type first () ;

   method Bool sNotFull ;
   method Bool sNotEmpty ;
   method Bool dNotFull ;
   method Bool dNotEmpty ;

   // Note that for the following methods, the Integer argument must
   // be a compile-time constant.
   method Bool sIsLessThan   ( Integer c1 ) ;
   method Bool sIsGreaterThan( Integer c1 ) ;
   method Bool dIsLessThan   ( Integer c1 ) ;
   method Bool dIsGreaterThan( Integer c1 ) ;

   method Action sClear ;
   method Action dClear ;

endinterface

//@
//@ \index{mkSyncFIFOLevel@\te{mkSyncFIFOLevel} (module)|textbf}
//@ The module mkSyncFIFOLevel is dual clock FIFO, where enqueue and
//@ dequeue methods are in separate clocks domains -- sClkIn and
//@ dClkIn respectively.  Because of the synchronization latency, the
//@ flag indicators will not necessarily be identical in value.  Note
//@ however, that the sNotFull and dNotEmpty flags always give proper
//@ (pessimistic) indication for the safe use of enq and deq methods;
//@ these
//@ are automatically included as implicit condition in the enq and deq
//@ (and first) methods.
//@ # 6
module mkSyncFIFOLevel(
                       Clock sClkIn, Reset sRstIn,
                       Clock dClkIn,
                       SyncFIFOLevelIfc#(a_type, fifoDepth) ifc )
   provisos( Bits#(a_type, sa),         // Can convert into Bits
             Log#(TAdd#(fifoDepth,1), cntSize) // Get the count width from the depth
           ) ;

   Integer ififoDepth = valueOf( fifoDepth ) ;

   SyncFIFOCount_INT#(a_type, cntSize) _syncFifo;
   if (valueOf(sa) == 0) begin
      (*hide*)
      SyncFIFOCount0_INT#(cntSize) _ifc0 <- vSyncFIFOCount0( ififoDepth, sClkIn, sRstIn, dClkIn ) ;
      _syncFifo = fromSyncFIFOCount0_INT( _ifc0 ) ;
   end
   else begin
      (*hide*)
      _syncFifo <- vSyncFIFOCount( ififoDepth, sClkIn, sRstIn, dClkIn ) ;
   end

   method Action enq(a_type x) if (_syncFifo.sNotFull);
      _syncFifo.enq(x);
   endmethod

   method Action deq() if (_syncFifo.dNotEmpty);
      _syncFifo.deq;
   endmethod

   method a_type first() if (_syncFifo.dNotEmpty);
      return _syncFifo.first;
   endmethod

   method Bool sNotFull  = _syncFifo.sNotFull ;
   method Bool dNotEmpty = _syncFifo.dNotEmpty ;

   method Bool sNotEmpty ;
      return (_syncFifo.sCount != 0 );
   endmethod

   method Bool dNotFull ;
      return _syncFifo.dCount != fromInteger( valueOf(fifoDepth) ) ;
   endmethod

   method Bool sIsLessThan( Integer x ) ;
      return rangeTest( _syncFifo.sCount, x, \< , 1, ififoDepth, "sIsLessThan" ) ;
   endmethod

   method Bool dIsLessThan( Integer x ) ;
      return rangeTest( _syncFifo.dCount, x, \< , 1, ififoDepth, "dIsLessThan" ) ;
   endmethod

   method Bool sIsGreaterThan( Integer x ) ;
      return rangeTest( _syncFifo.sCount, x, \> , 0, ififoDepth-1, "sIsGreaterThan" ) ;
   endmethod

   method Bool dIsGreaterThan( Integer x ) ;
      return rangeTest( _syncFifo.dCount, x, \> , 0, ififoDepth-1, "dIsGreaterThan" ) ;
   endmethod

   method Action sClear ;
      _syncFifo.sClear ;
   endmethod

   method Action dClear ;
      _syncFifo.dClear ;
   endmethod

endmodule


// An internal Interface used for import BVI spec.
interface FIFOLevel_INT #(type a_type, numeric type cntSize )  ;
   method Action enq( a_type sendData );
   method Action deq() ;
   method a_type first() ;
   method Action clear() ;
      // these follow stricter TRS rule
   method Bool notFull ;
   method Bool notEmpty ;
   method UInt#(cntSize) count  ;
      // these always give non conflicting values at beginning of cycle
   method Bool i_notFull ;
   method Bool i_notEmpty ;
   method UInt#(cntSize) i_count  ;
endinterface


// A BSV wrapper for mkSizedFIFOF_ which adds the level features
module vbFIFOLevel#( Integer depthIn )
   ( FIFOLevel_INT#(a,cntSize) ifc)
   provisos ( Bits#(a,sa) ) ;

   FIFOF_#(a)  _fifc <- mkSizedFIFOF_( depthIn, True ) ;
   Reg#(UInt#(cntSize)) countReg <- mkReg( 0 ) ;

   PulseWire r_enq <- mkPulseWire ;
   PulseWire r_deq <- mkPulseWire ;
   PulseWire r_clr <- mkPulseWire ;

   rule _updateLevelCounter ( (r_enq != r_deq)  || r_clr ) ;
      countReg <= r_clr ? 0 : ((r_enq) ? (countReg + 1) : (countReg -1 )) ;
   endrule

   method Action enq( a sendData );
      _fifc.enq( sendData ) ;
      r_enq.send ;
   endmethod

   method Action deq() ;
      _fifc.deq() ;
      r_deq.send ;
   endmethod

   method a first() ;
      return _fifc.first ;
   endmethod

   method Action clear() ;
      _fifc.clear();
      r_clr.send ;
   endmethod

   // these follow stricter TRS rule
   method Bool notFull ;
      return _fifc.notFull ;
   endmethod

   method Bool notEmpty ;
      return _fifc.notEmpty ;
   endmethod

   method UInt#(cntSize) count  ;
      return countReg ;
   endmethod

   // these always give non conflicting values at beginning of cycle
   method Bool i_notFull ;
      return _fifc.i_notFull ;
   endmethod

   method Bool i_notEmpty ;
      return _fifc.i_notEmpty ;
   endmethod

   method UInt#(cntSize) i_count  ;
      return countReg ;
   endmethod

endmodule



// Common function to test the validity arguments to methods
function Bool rangeTest( UInt#(cntSz) value,
                        Integer comp,
                        function Bool foperation(UInt#(cntSz) a,
                                                 UInt#(cntSz) b ),
                           Integer minValue,
                           Integer maxValue,
                           String methodName );

     return ((comp >= minValue) && (comp <= maxValue )) ?
                           (foperation (value,  fromInteger( comp ))) :
                           error( "Argument of " + methodName + " must be in the range of " +
                                 integerToString( minValue) +
                                 " to " +
                                 integerToString( maxValue ) +
                                 "; " +
                                 integerToString( comp ) +
                                 " is out of range.") ;
endfunction



/* -----\/----- EXCLUDED -----\/-----
typedef Bit#(17)  T ;
typedef 5        CntSz ;
(* synthesize *)
module mkTest () ;
   Clock clk <- exposeCurrentClock ;
   Reset rst <- exposeCurrentReset ;
   SyncFIFOCount_INT#(T,CntSz) fifo <- vSyncFIFOCount( 12,  clk, rst, clk ) ;

   Reg#(UInt#(CntSz))  cnt <- mkReg(0) ;

   rule test ;
      cnt <= fifo.sCount ;
      $display( "foo is %d", cnt ) ;
   endrule
endmodule
 -----/\----- EXCLUDED -----/\----- */


//@

/* -----\/----- EXCLUDED -----\/-----
(* synthesize *)
module mkTest2 () ;
   Clock clk <- exposeCurrentClock ;
   Reset rst <- exposeCurrentReset ;
   Clock  clk2 = clk ;

   // Define a fifo of Int(#23) with 128 entries
   SyncFIFOLevelIfc#(Int#(23),128) fifo <- mkSyncFIFOLevel(  clk, rst, clk2 ) ;

   // Define some constants
   let sAlmostFull = fifo.sIsGreaterThan( 120 ) ;
   let dAlmostFull = fifo.sIsGreaterThan( 120 ) ;
   let dAlmostEmpty = fifo.dIsLessThan( 12 ) ;

   // a register to indicate a burst mode
   Reg#(Bool)  burstOut <- mkReg( False ) ;


   // Set and clear the burst mode depending on fifo status
   rule timeToDeque( dAlmostFull && ! burstOut ) ;
      burstOut <= True ;
   endrule
   rule timeToStop ( dAlmostEmpty && burstOut );
      burstOut <= False ;
   endrule
   rule moveData ( burstOut ) ;
      let dataToSend = fifo.first ;
      fifo.deq ;
      // bursting.send( dataToSend ) ;
   endrule

   Reg#(UInt#(CntSz))  cnt <- mkReg(0) ;

   rule test ( ! fifo.sIsLessThan( 6 ) )  ;
      $display( "greater than 5 " ) ;
   endrule
   rule test1 ( ! fifo.sIsLessThan( 1 ) )  ;
      $display( "greater than 5 " ) ;
   endrule
   rule test2 ( ! fifo.sIsLessThan( 6 ) )  ;
      $display( "greater than 5 " ) ;
   endrule
   rule test3 ( ! fifo.sIsLessThan( 6 ) )  ;
      $display( "greater than 5 " ) ;
   endrule
   rule test3g ( ! fifo.sIsGreaterThan( 6 ) )  ;
      $display( "greater than 5 " ) ;
   endrule
   rule test4 ( ! fifo.sIsLessThan( 3 ) )  ;
      $display( "greater than 5 " ) ;
   endrule
   rule test5 ( ! fifo.sIsLessThan( 4 ) )  ;
      $display( "greater than 5 " ) ;
   endrule

   //  type error since we require an Integer
//    rule testX ( ! fifo.levels.sIsLessThan( cnt ) )  ;
//       $display( "greater than 5 " ) ;
//    endrule

endmodule
 -----/\----- EXCLUDED -----/\----- */

//@ \begin{itemize}
//@   \item{\bf Example}
//@
//@ The following example shows the use of \te{SyncLevelFIFO} as a way
//@ to collect data into a FIFO, and then send it out in a burst mode.  The
//@ portion of the design shown, waits until the FIFO is almost
//@ full, and then sets a register, {\tt burstOut} which indicates
//@ that the FIFO should dequeue. When the FIFO is almost empty, the
//@ flag is cleared, and FIFO fills again.
//@
//@ \begin{libverbatim}
//@    . . .
//@    // Define a fifo of Int(#23) with 128 entries
//@    SyncFIFOLevelIfc#(Int#(23),128) fifo <- mkSyncFIFOLevel(  clk, rst, clk2 ) ;
//@
//@    // Define some constants
//@    let sFifoAlmostFull = fifo.sIsGreaterThan( 120 ) ;
//@    let dFifoAlmostFull = fifo.dIsGreaterThan( 120 ) ;
//@    let dFifoAlmostEmpty = fifo.dIsLessThan( 12 ) ;
//@
//@    // a register to indicate a burst mode
//@    Reg#(Bool)  burstOut <- mkReg( False ) ;
//@
//@    . . .
//@    // Set and clear the burst mode depending on fifo status
//@    rule timeToDeque( dFifoAlmostFull && ! burstOut ) ;
//@       burstOut <= True ;
//@    endrule
//@
//@    rule timeToStop ( dFifoAlmostEmpty && burstOut );
//@       burstOut <= False ;
//@    endrule
//@
//@    rule moveData ( burstOut ) ;
//@       let dataToSend = fifo.first ;
//@       fifo.deq ;
//@       ...
//@       bursting.send( dataToSend ) ;
//@    endrule
//@ \end{libverbatim}
//@ \end{itemize}
// TODO Add single clock version of this fifo

interface FIFOCountIfc#( type a_type, numeric type fifoDepth) ;
   method Action enq ( a_type sendData ) ;
   method Action deq () ;
   method a_type first () ;

   method Bool notFull ;
   method Bool notEmpty ;

   method UInt#(TLog#(TAdd#(fifoDepth,1))) count;

   method Action clear;
endinterface

module mkFIFOCount( FIFOCountIfc#(a_type, fifoDepth) ifc )
   provisos (Bits#(a_type,sa));

   Integer ififoDepth = (valueOf( fifoDepth ) < 3 ?
                         (error ("mkFIFOLevel: fifoDepth must be greater than 2. " +
                                 "Specified depth is " + integerToString( valueOf(fifoDepth)) + "." ) ) :
                         valueOf( fifoDepth ) );

   FIFOLevel_INT#(a_type, (TLog#(TAdd#(fifoDepth,1))))
      _fifoLevel <- vbFIFOLevel( ififoDepth ) ;

   Reg#(Bool) levelsValid <- mkReg(True); // Needed only for scheduling
   PulseWire doResetEnq <- mkPulseWire;
   PulseWire doResetDeq <- mkPulseWire;
   PulseWire doResetClr <- mkPulseWire;

   Bool doReset = doResetEnq || doResetDeq || doResetClr;

   rule reset(doReset);
     levelsValid <= True;
   endrule

   method Action enq( a_type x ) if ( _fifoLevel.i_notFull ) ;
      _fifoLevel.enq( x ) ;
      levelsValid <= False;
      doResetEnq.send;
   endmethod

   method Action deq if ( _fifoLevel.i_notEmpty ) ;
      _fifoLevel.deq ;
      levelsValid <= False;
      doResetDeq.send;
   endmethod

   method first if ( _fifoLevel.i_notEmpty ) ;
      return _fifoLevel.first ;
   endmethod

   method Action clear;
     _fifoLevel.clear ;
     levelsValid <= False;
     doResetClr.send;
   endmethod

   method notFull = _fifoLevel.notFull ;
   method notEmpty = _fifoLevel.notEmpty ;

   method count if(levelsValid);
      return  _fifoLevel.i_count ;
   endmethod

endmodule

module mkGFIFOCount#(Bool ugenq, Bool ugdeq, Bool ugcount)( FIFOCountIfc#(a_type, fifoDepth) ifc )
   provisos (Bits#(a_type,sa));

   Integer ififoDepth = (valueOf( fifoDepth ) < 3 ?
                         (error ("mkFIFOLevel: fifoDepth must be greater than 2. " +
                                 "Specified depth is " + integerToString( valueOf(fifoDepth)) + "." ) ) :
                         valueOf( fifoDepth ) );

   FIFOLevel_INT#(a_type, (TLog#(TAdd#(fifoDepth,1))))
      _fifoLevel <- vbFIFOLevel( ififoDepth ) ;

   Action enqGuard = noAction ;
   Action deqGuard = noAction ;
   Action clrGuard = noAction ;
   Bool   levelsValid = ? ;
   if ( ugcount )
      begin
         enqGuard = noAction ;
         deqGuard = noAction ;
         clrGuard = noAction ;
         levelsValid = True ;
      end
   else
      begin
         Reg#(Bool) levelsValid_virtual_Reg <- mkReg(True);
         PulseWire doResetEnq <- mkPulseWire;
         PulseWire doResetDeq <- mkPulseWire;
         PulseWire doResetClr <- mkPulseWire;

         Bool doReset = doResetEnq || doResetDeq || doResetClr;

         rule reset(doReset);
            levelsValid_virtual_Reg <= True;
         endrule
         enqGuard = (action
                        levelsValid_virtual_Reg <= False;
                        doResetEnq.send;
                     endaction);
         deqGuard = (action
                        levelsValid_virtual_Reg <= False;
                        doResetDeq.send;
                     endaction);
         clrGuard = (action
                        levelsValid_virtual_Reg <= False;
                        doResetClr.send;
                     endaction);
         levelsValid = levelsValid_virtual_Reg._read ;
      end

   method Action enq( a_type x ) if ( _fifoLevel.i_notFull || ugenq ) ;
      _fifoLevel.enq( x ) ;
      enqGuard ;
   endmethod

   method Action deq if ( _fifoLevel.i_notEmpty || ugdeq ) ;
      _fifoLevel.deq ;
      deqGuard;
   endmethod

   method first if ( _fifoLevel.i_notEmpty || ugdeq ) ;
      return _fifoLevel.first ;
   endmethod

   method Action clear;
      _fifoLevel.clear ;
      clrGuard;
   endmethod

   method notFull = _fifoLevel.notFull ;
   method notEmpty = _fifoLevel.notEmpty ;

   method count if(levelsValid);
      return  _fifoLevel.i_count ;
   endmethod

endmodule


interface SyncFIFOCountIfc#( type a_type, numeric type fifoDepth) ;
   method Action enq ( a_type sendData ) ;
   method Action deq () ;
   method a_type first () ;

   method Bool sNotFull ;
   method Bool sNotEmpty ;
   method Bool dNotFull ;
   method Bool dNotEmpty ;

   method UInt#(TLog#(TAdd#(fifoDepth,1))) sCount;
   method UInt#(TLog#(TAdd#(fifoDepth,1))) dCount;

   method Action sClear;
   method Action dClear;
endinterface

module mkSyncFIFOCount(
                       Clock sClkIn, Reset sRstIn,
                       Clock dClkIn,
                       SyncFIFOCountIfc#(a_type, fifoDepth) ifc )
   provisos( Bits#(a_type, sa),         // Can convert into Bits
             Log#(TAdd#(fifoDepth,1), cntSize) // Get the count width from the depth
	   ) ;

   Integer ififoDepth = valueOf( fifoDepth ) ;

   SyncFIFOCount_INT#(a_type, cntSize) _syncFifo;
   if (valueOf(sa) == 0) begin
      (*hide*)
      SyncFIFOCount0_INT#(cntSize) _ifc0 <- vSyncFIFOCount0( ififoDepth, sClkIn, sRstIn, dClkIn ) ;
      _syncFifo = fromSyncFIFOCount0_INT( _ifc0 ) ;
   end
   else begin
      (*hide*)
      _syncFifo <- vSyncFIFOCount( ififoDepth, sClkIn, sRstIn, dClkIn ) ;
   end

   method Action enq(a_type x) if (_syncFifo.sNotFull);
      _syncFifo.enq(x);
   endmethod

   method Action deq() if (_syncFifo.dNotEmpty);
      _syncFifo.deq();
   endmethod

   method a_type first() if (_syncFifo.dNotEmpty);
      return _syncFifo.first;
   endmethod

   method Bool sNotFull  = _syncFifo.sNotFull ;
   method Bool dNotEmpty = _syncFifo.dNotEmpty ;

   method Bool sNotEmpty ;
      return (_syncFifo.sCount != 0 );
   endmethod

   method Bool dNotFull ;
      return _syncFifo.dCount != fromInteger( valueOf(fifoDepth) ) ;
   endmethod

   method sCount ;
      return _syncFifo.sCount;
   endmethod

   method dCount ;
      return _syncFifo.dCount;
   endmethod

   method Action sClear;
      _syncFifo.sClear;
   endmethod

   method Action dClear;
      _syncFifo.dClear;
   endmethod
endmodule

module mkGSyncFIFOCount#( Bool ugenq, Bool ugdeq )
                        ( Clock sClkIn, Reset sRstIn,
                          Clock dClkIn,
                          SyncFIFOCountIfc#(a_type, fifoDepth) ifc )
   provisos( Bits#(a_type, sa),         // Can convert into Bits
             Log#(TAdd#(fifoDepth,1), cntSize) // Get the count width from the depth
	   ) ;

   Integer ififoDepth = valueOf( fifoDepth ) ;

   SyncFIFOCount_INT#(a_type, cntSize) _syncFifo;
   if (valueOf(sa) == 0) begin
      (*hide*)
      SyncFIFOCount0_INT#(cntSize) _ifc0 <- vSyncFIFOCount0( ififoDepth, sClkIn, sRstIn, dClkIn ) ;
      _syncFifo = fromSyncFIFOCount0_INT( _ifc0 ) ;
   end
   else begin
      (*hide*)
      _syncFifo <- vSyncFIFOCount( ififoDepth, sClkIn, sRstIn, dClkIn ) ;
   end

   method Action enq(a_type x) if (_syncFifo.sNotFull || ugenq);
      _syncFifo.enq(x);
   endmethod

   method Action deq() if (_syncFifo.dNotEmpty || ugdeq);
      _syncFifo.deq();
   endmethod

   method a_type first() if (_syncFifo.dNotEmpty || ugdeq);
      return _syncFifo.first;
   endmethod

   method Bool sNotFull  = _syncFifo.sNotFull ;
   method Bool dNotEmpty = _syncFifo.dNotEmpty ;

   method Bool sNotEmpty ;
      return (_syncFifo.sCount != 0 );
   endmethod

   method Bool dNotFull ;
      return _syncFifo.dCount != fromInteger( valueOf(fifoDepth) ) ;
   endmethod

   method sCount ;
      return _syncFifo.sCount;
   endmethod

   method dCount ;
      return _syncFifo.dCount;
   endmethod

   method Action sClear;
      _syncFifo.sClear;
   endmethod

   method Action dClear;
      _syncFifo.dClear;
   endmethod
endmodule

// An internal Interface used for import BVI spec.
interface SyncFIFOCount_INT #(type a_type, numeric type cntSize )  ;
   method Action enq( a_type sendData );
   method Action deq() ;
   method a_type first() ;
   method Bool sNotFull ;
   method Bool dNotEmpty ;
   method UInt#(cntSize) sCount  ;
   method UInt#(cntSize) dCount  ;
   method Action sClear;
   method Action dClear;
endinterface

// A variant for zero-width data
interface SyncFIFOCount0_INT #( numeric type cntSize )  ;
   method Action enq();
   method Action deq() ;
   method Bool sNotFull ;
   method Bool dNotEmpty ;
   method UInt#(cntSize) sCount  ;
   method UInt#(cntSize) dCount  ;
   method Action sClear;
   method Action dClear;
endinterface

function SyncFIFOCount_INT#(a,n) fromSyncFIFOCount0_INT (SyncFIFOCount0_INT#(n) ifc0);
   return (interface SyncFIFOCount_INT;
              method enq(sendData) = ifc0.enq;
	      method deq()         = ifc0.deq;
	      method first()       = ?;
	      method sNotFull()    = ifc0.sNotFull;
	      method dNotEmpty()   = ifc0.dNotEmpty;
	      method sCount()      = ifc0.sCount;
	      method dCount()      = ifc0.dCount;
	      method sClear()      = ifc0.sClear;
	      method dClear()      = ifc0.dClear;
           endinterface);
endfunction

import "BVI" SyncFIFOLevel =
module vSyncFIFOCount#( Integer depthIn
              ) (Clock sClkIn, Reset sRstIn,
                 Clock dClkIn,
                 SyncFIFOCount_INT#(a,cntSize) ifc)
   provisos ( Bits#(a,sa) ) ;

   let logDepth = log2( depthIn ) ;
   let pwrDepth = 2 ** logDepth ;

   if (pwrDepth < 2) error( "mkSyncFIFOLevel depth must be greater than 1 for correct operation" ) ;
   let depthErr = ("SyncFIFOCount depth must be power of 2.  Please  increased from "
                   + integerToString (depthIn) + " to "
                   + integerToString (pwrDepth) + "." );

   let realDepth = (( depthIn == pwrDepth ) ? pwrDepth :
                    error ( depthErr )) ;

   let indxErr = ( "SyncFIFOCount: indicator widths have wrong size specified: "
                  + "width is "
                  + integerToString (  valueOf(cntSize))
                  + " and it must be: "
                  + integerToString ( log2 (realDepth + 1) )
                  );


   parameter dataWidth = valueOf( sa ) ;
   parameter depth = realDepth ; // must be power of 2 !
   parameter indxWidth = (log2(realDepth + 1) == valueOf(cntSize)) ? logDepth :
                         error (indxErr);


   default_clock no_clock ;
   no_reset ;

   input_clock clk_src ( sCLK, (*unused*)sCLK_GATE ) = sClkIn;
   input_clock clk_dst ( dCLK, (*unused*)dCLK_GATE ) = dClkIn;

   input_reset (sRST) clocked_by (clk_src) = sRstIn ;

   method enq ( sD_IN )  enable(sENQ)            clocked_by(clk_src) reset_by(sRstIn);
   method deq ()         enable(dDEQ)            clocked_by(clk_dst) reset_by(no_reset);
   method dD_OUT first()                         clocked_by(clk_dst) reset_by(no_reset);

   method sFULL_N sNotFull                       clocked_by(clk_src) reset_by(sRstIn);
   method dEMPTY_N dNotEmpty                     clocked_by(clk_dst) reset_by(no_reset);

   method dCOUNT dCount                          clocked_by(clk_dst) reset_by(no_reset);
   method sCOUNT sCount                          clocked_by(clk_src) reset_by(sRstIn);

   method sClear() ready(sCLR_RDY) enable (sCLR) clocked_by(clk_src) reset_by(sRstIn);
   method dClear() ready(dCLR_RDY) enable (dCLR) clocked_by(clk_dst) reset_by(no_reset);

   // Scheduling annotation
      schedule first CF first ;
      schedule first SB deq ;

   // XXX reconsider the following
      schedule enq C enq;
      schedule enq CF sNotFull ;
      schedule deq CF dNotEmpty ;
      schedule (sNotFull, sCount)  CF (sNotFull, sCount);
      schedule dNotEmpty CF (first, dNotEmpty, dCount) ;

   // Since the count are possibly stale, they are SB with enq and deq
      schedule deq C deq ;
      schedule dCount SB deq;
      schedule dCount CF (first, dCount) ;
      schedule sCount SB enq ;

   // The clears must go after everything else
      schedule (first, deq, dCount, dNotEmpty) SB dClear;
      schedule (enq, sCount, sNotFull) SB sClear ;
      schedule sClear CF sClear;
      schedule dClear CF dClear;

   // Cross domains are all conflict free
      schedule (first, deq, dCount, dNotEmpty, dClear) CF (enq, sCount, sNotFull, sClear) ;

endmodule

// Version for data width 0
import "BVI" SyncFIFOLevel0 =
module vSyncFIFOCount0#( Integer depthIn
              ) (Clock sClkIn, Reset sRstIn,
                 Clock dClkIn,
                 SyncFIFOCount0_INT#(cntSize) ifc);

   let logDepth = log2( depthIn ) ;
   let pwrDepth = 2 ** logDepth ;

   if (pwrDepth < 2) error( "mkSyncFIFOLevel depth must be greater than 1 for correct operation" ) ;
   let depthErr = ("SyncFIFOCount depth must be power of 2.  Please  increased from "
                   + integerToString (depthIn) + " to "
                   + integerToString (pwrDepth) + "." );

   let realDepth = (( depthIn == pwrDepth ) ? pwrDepth :
                    error ( depthErr )) ;

   let indxErr = ( "SyncFIFOCount: indicator widths have wrong size specified: "
                  + "width is "
                  + integerToString (  valueOf(cntSize))
                  + " and it must be: "
                  + integerToString ( log2 (realDepth + 1) )
                  );


   parameter depth = realDepth ; // must be power of 2 !
   parameter indxWidth = (log2(realDepth + 1) == valueOf(cntSize)) ? logDepth :
                         error (indxErr);


   default_clock no_clock ;
   no_reset ;

   input_clock clk_src ( sCLK, (*unused*)sCLK_GATE ) = sClkIn;
   input_clock clk_dst ( dCLK, (*unused*)dCLK_GATE ) = dClkIn;

   input_reset (sRST) clocked_by (clk_src) = sRstIn ;

   method enq ()         enable(sENQ)            clocked_by(clk_src) reset_by(sRstIn);
   method deq ()         enable(dDEQ)            clocked_by(clk_dst) reset_by(no_reset);

   method sFULL_N sNotFull                       clocked_by(clk_src) reset_by(sRstIn);
   method dEMPTY_N dNotEmpty                     clocked_by(clk_dst) reset_by(no_reset);

   method dCOUNT dCount                          clocked_by(clk_dst) reset_by(no_reset);
   method sCOUNT sCount                          clocked_by(clk_src) reset_by(sRstIn);

   method sClear() ready(sCLR_RDY) enable (sCLR) clocked_by(clk_src) reset_by(sRstIn);
   method dClear() ready(dCLR_RDY) enable (dCLR) clocked_by(clk_dst) reset_by(no_reset);

   // Scheduling annotation

   // XXX reconsider the following
      schedule enq C enq;
      schedule enq CF sNotFull ;
      schedule deq CF dNotEmpty ;
      schedule (sNotFull, sCount)  CF (sNotFull, sCount);
      schedule dNotEmpty CF (dNotEmpty, dCount) ;

   // Since the count are possibly stale, they are SB with enq and deq
      schedule deq C deq ;
      schedule dCount SB deq;
      schedule dCount CF dCount ;
      schedule sCount SB enq ;

   // The clears must go after everything else
      schedule (deq, dCount, dNotEmpty) SB dClear;
      schedule (enq, sCount, sNotFull) SB sClear ;
      schedule sClear CF sClear;
      schedule dClear CF dClear;

   // Cross domains are all conflict free
      schedule (deq, dCount, dNotEmpty, dClear) CF (enq, sCount, sNotFull, sClear) ;

endmodule


// Define instances of ToGet and ToPut for the intefaces defined in this package
instance ToGet #( FIFOLevelIfc#(a,n), a ) ;
   function Get#(a) toGet (FIFOLevelIfc#(a,n) i);
      return (interface Get;
                 method ActionValue#(a) get();
                    i.deq ;
                    return i.first ;
              endmethod
         endinterface);
   endfunction
endinstance

instance ToPut #( FIFOLevelIfc#(a,n), a ) ;
   function Put#(a) toPut (FIFOLevelIfc#(a,n) i);
      return (interface Put;
                 method Action put(a x);
                    i.enq(x) ;
              endmethod
         endinterface);
   endfunction
endinstance


instance ToGet #( SyncFIFOLevelIfc#(a,n), a ) ;
   function Get#(a) toGet (SyncFIFOLevelIfc#(a,n) i);
      return (interface Get;
                 method ActionValue#(a) get();
                    i.deq ;
                    return i.first ;
              endmethod
         endinterface);
   endfunction
endinstance


instance ToPut #( SyncFIFOLevelIfc#(a,n), a ) ;
   function Put#(a) toPut (SyncFIFOLevelIfc#(a,n) i);
      return (interface Put;
                 method Action put(a x);
                    i.enq(x) ;
              endmethod
         endinterface);
   endfunction
endinstance


instance ToGet #( FIFOCountIfc#(a,n), a ) ;
   function Get#(a) toGet (FIFOCountIfc#(a,n) i);
      return (interface Get;
                 method ActionValue#(a) get();
                    i.deq ;
                    return i.first ;
              endmethod
         endinterface);
   endfunction
endinstance


instance ToPut #( FIFOCountIfc#(a,n), a ) ;
   function Put#(a) toPut (FIFOCountIfc#(a,n) i);
      return (interface Put;
                 method Action put(a x);
                    i.enq(x) ;
              endmethod
         endinterface);
   endfunction
endinstance



instance ToGet #( SyncFIFOCountIfc#(a,n), a ) ;
   function Get#(a) toGet (SyncFIFOCountIfc#(a,n) i);
      return (interface Get;
                 method ActionValue#(a) get();
                    i.deq ;
                    return i.first ;
              endmethod
         endinterface);
   endfunction
endinstance


instance ToPut #( SyncFIFOCountIfc#(a,n), a ) ;
   function Put#(a) toPut (SyncFIFOCountIfc#(a,n) i);
      return (interface Put;
                 method Action put(a x);
                    i.enq(x) ;
              endmethod
         endinterface);
   endfunction
endinstance


endpackage
