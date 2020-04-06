package Randomizable;

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

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

interface Control ;
   method Action init();
endinterface

import "BVI" ConstrainedRandom =
module vmkGenericRandomizer#(Bit#(n) min, Bit#(n) max, Integer width) (VRandomize#(n));

   default_clock clk(CLK);
   parameter width = width;
   parameter min = min;
   parameter max = max;

   method (* reg *)OUT next() enable(EN);
   schedule next C next;
endmodule

module mkGenericRandomizer (Randomize#(a))
   provisos (Bits#(a, sa), Bounded#(a));
   a min = minBound;
   a max = maxBound;
   let _m = liftModule(mkConstrainedRandomizer(min, max));

   Randomize#(a) _r <- _m;

   return _r;

endmodule

module mkConstrainedRandomizer#(a min, a max) (Randomize#(a))
   provisos (Bits#(a, sa), Bounded#(a));

   Randomize#(a) ifc;

   Reg#(Bool) initialized <- mkReg(False);
   Wire#(Bit#(sa)) ignore <- mkWire;

   if (genC)
      begin

	 VRandomize#(sa) _r <- liftModule(cmkGenericRandomizer(pack(min), pack(max)));

	 rule every (!initialized);
	    let value <- _r.next();
	    ignore <= value;
//	    $display("Module %m uninitialized (%5d).", $time);
	 endrule


	 ifc = interface Randomize;
		  interface Control cntrl;
		     method Action init ();
			initialized <= True;
		     endmethod
		  endinterface

		  method ActionValue#(a) next() if (initialized);
		     let value <- _r.next();
		     return unpack(value);
		  endmethod
	       endinterface;

      end
   else
      begin

	 VRandomize#(sa) _r <- liftModule(vmkGenericRandomizer(pack(min), pack(max), valueOf(sa)));

	 rule every (!initialized);
	    let value <- _r.next();
	    ignore <= value;
	    //      $display("Module %m uninitialized (%5d).", $time);
	 endrule

	 ifc = interface Randomize;
		  interface Control cntrl;
		     method Action init ();
			initialized <= True;
		     endmethod
		  endinterface

		  method ActionValue#(a) next() if (initialized);
		     let value <- _r.next();
		     return unpack(value);
		  endmethod
	       endinterface;

      end
   return (ifc);
endmodule

import "BDPI" function ActionValue#(Bit#(32)) rand32();
import "BDPI" function Action srand(Bit#(32)  seed);

module cmkGenericRandomizer#(Bit#(n) min, Bit#(n) max) (VRandomize#(n))
   provisos(Add#(n, 32, j));

   Wire#(Bit#(n)) zaz <- mkDWire(0);

   rule every;
      Integer i = 0;
      Integer width = valueOf(n);

      Bit#(n) value = 0;

      for (i = 0; i <= width; i = i + 32)
	 begin
	    Bit#(32) x <- rand32;
	    value = truncate({value, x});
	 end
      zaz <= value;
   endrule

   method ActionValue#(Bit#(n)) next();

      Bit#(n) value = zaz;

      if ((1 + (max - min)) == 0)
	 value = min + value;
      else
	 value = min + (value % (1 + (max - min)));

      return value;

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

module mkSpecialRandomizer#(function a modify_value(a value)) (Randomize#(a))
   provisos (Randomizable#(a));

   Randomize#(a) basic_gen <- mkRandomizer;

   interface Control cntrl;
      method Action init();
	 basic_gen.cntrl.init();
      endmethod
   endinterface

   method ActionValue#(a) next ();
      let value <- basic_gen.next();
      return modify_value(value);
   endmethod
endmodule

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

typeclass Randomizable#(type t);
   module mkRandomizer (Randomize#(t));
endtypeclass

endpackage

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////
