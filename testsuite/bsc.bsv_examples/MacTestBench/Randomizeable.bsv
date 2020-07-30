package Randomizeable;

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

import Control::*;
import GetPut::*;

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

interface Randomize#(type a);
   interface Control cntrl;
   method ActionValue#(a) next();
endinterface

interface VRandomize#(type n) ;
   method ActionValue#(Bit#(n)) next();
endinterface

import "BVI" ConstrainedRandom = 
module vmkGenericRandomizer#(Bit#(n) min, Bit#(n) max, Integer width) (VRandomize#(n));

   default_clock clk(CLK);
   parameter width = width;
   parameter min = min;
   parameter max = max;

   method (* reg *)OUT next() enable(EN);

endmodule

module mkGenericRandomizer (Randomize#(a))
   provisos (Bits#(a, sa), Bounded#(a));
   a min = minBound;
   a max = maxBound;
   let _m = liftModule(vmkGenericRandomizer(pack(min), pack(max), valueOf(sa)));
   
   VRandomize#(sa)_r();
   _m __(_r); // the "__" makes this instantiation anonymous

   Reg#(Bool) initialized <- mkReg(False);

   rule every (!initialized);
      let value <- _r.next();
//      $display("Module %m unintialized (%5d).", $time);
   endrule

   interface Control cntrl;
      method Action init ();
	 initialized <= True;
      endmethod
   endinterface

   method ActionValue#(a) next() if (initialized);
      let value <- _r.next();
      return unpack(value);
   endmethod

endmodule

module mkConstrainedRandomizer#(a min, a max) (Randomize#(a))
   provisos (Bits#(a, sa), Bounded#(a));
//   a min = minBound;
//   a max = maxBound;
   let _m = liftModule(vmkGenericRandomizer(pack(min), pack(max), valueOf(sa)));
   
   VRandomize#(sa)_r();
   _m __(_r); // the "__" makes this instantiation anonymous

   Reg#(Bool) initialized <- mkReg(False);

   rule every (!initialized);
      let value <- _r.next();
//      $display("Module %m unintialized (%5d).", $time);
   endrule

   interface Control cntrl;
      method Action init ();
	 initialized <= True;
      endmethod
   endinterface

   method ActionValue#(a) next() if (initialized);
      let value <- _r.next();
      return unpack(value);
   endmethod

endmodule

function Get#(a) randomizeToGet (Randomize#(a) ifc);
   let out = interface Get
		method ActionValue#(a) get;
		   let value <- ifc.next();
		   return value;
		endmethod
	     endinterface;
   return out;
endfunction

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

typeclass Randomizeable#(type t);
   module mkRandomizer (Randomize#(t));
endtypeclass

endpackage

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

