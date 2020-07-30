package Test20;

import ModuleCollect::*;
import List::*;
import ListN::*;

interface Condition;
   method Integer index;
   method Bool condition;
endinterface

typedef ModuleCollect#(Condition, i) CondModule#(type i);
interface CondWires#(type n);
   method Bit#(n) wires;
   method Action clear;
endinterface

module [Module] mkCondWrapper#(CondModule#(Empty) mkM)(CondWires#(n));
   IWithCollection#(Condition, Empty) ecs();
   exposeCollection#(mkM) the_dut(ecs);
   let cs = ecs.collection;

   Reg#(Bit#(1)) rs[valueOf(n)];
   for (Integer i=0; i<valueOf(n); i=i+1)
      begin
	 Reg#(Bit#(1)) r();
	 mkReg#(0) an_r(r);
	 rs[i] = asReg(r);
      end

   method wires;
      ListN#(n, Bit#(1)) xs;
      for (Integer i=0; i<valueOf(n); i=i+1)
	 begin
	    let x = rs[i];
	    xs[i] = x;
	 end
      return (pack(xs));
   endmethod

   method Action clear;
   endmethod
endmodule

// --------------------



module [CondModule] mkTbGCD(Empty);
endmodule: mkTbGCD

(* synthesize *)
module [Module] mkTopLevel(CondWires#(2));
   CondWires#(2) ifc();
   mkCondWrapper#(mkTbGCD) the_top_level(ifc);
   return (ifc);
endmodule

endpackage
