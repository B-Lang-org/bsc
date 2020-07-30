package Mii;

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

import Control::*;
import EthFrame::*;
import GetPut::*;
import Connectable::*;
import Randomizeable::*;
import RandomSynth::*;

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

typedef enum  {NONE, EARLY, LATE} CollisionKind deriving(Bounded, Bits, Eq);

typedef struct {
		CollisionKind kind;
		Bit#(16)      on_symbol;
//		Frame         frame;
		} Collision  deriving (Bits, Eq);

typedef struct {
		Bool collision;
		Bool carrier;
		} Indications  deriving (Bits, Eq);

typedef Bit#(4)  Nibble;

typedef struct {
		Nibble nibble;
		Bool   err;
		} MiiNibble  deriving (Bits, Eq);

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

interface IndicationsIFC;
   method Indications indicate();
endinterface

interface MediaIFC;
   method Bool carrier_out();
   method Action carrier_in(Bool value);
endinterface

interface MiiNibbleTxRxIFC;
   interface Get#(MiiNibble) tx;
   interface Put#(MiiNibble) rx;
endinterface

instance Connectable#(MiiNibbleTxRxIFC, MiiNibbleTxRxIFC);
      module mkConnection#(MiiNibbleTxRxIFC left, MiiNibbleTxRxIFC right) (Empty);

	 mkConnection(left.tx, right.rx);
	 mkConnection(left.rx, right.tx);

      endmodule
endinstance

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

instance Randomizeable#(Collision);
   module mkRandomizer (Randomize#(Collision));
      
      // TODO ... deal with EARLY/LATE collisions etc.
   
      let max = fromInteger(valueOf(MaxDataLength));
      
      Randomize#(CollisionKind) kind_gen   <- mkGenericRandomizer_Synth;
      Randomize#(Bit#(16))      symbol_gen <- mkConstrainedRandomizer_Synth(1, max - 1);
      
      interface Control cntrl;
	 method Action init();
	    kind_gen.cntrl.init();
	    symbol_gen.cntrl.init();
	 endmethod
      endinterface
      
      method ActionValue#(Collision) next ();

	 let kind       <- kind_gen.next();
	 let symbol     <- symbol_gen.next();
	 
	 let collision = Collision {kind:       kind,
				    on_symbol:  ((kind == NONE) ? 0 : symbol)
				    };
   
	 return collision;
	 
      endmethod

   endmodule
endinstance

endpackage

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////
