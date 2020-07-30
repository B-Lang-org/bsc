package DemonstrateConditions;

import ModuleCollect::*;
import Assert::*;
import List::*;
import Vector::*;

// This package is intended to demonstrate the use of ModuleCollect.
// We recall that an ordinary module, when instantiated, adds its own
// items to the growing accumulation of (1) state elements, and (2)
// rules, which are processed by later stages of the compiler.  The
// ModuleCollect package allows other items to be accumulated too.  But
// this extra "collection" must be exposed and processed at a higher
// level: in particular, any module which is to be synthesized must not
// be collecting any extra stuff, as the compiler would not know how to
// handle it.  This package is a simple example of how it all works.

// Suppose it is desired to place various test conditions (Boolean
// expressions) at random places in a design, and to set an external
// wire to 1 (e.g. to light a LED) if ever the condition is satisfied.  
// The desired interface at the top level is accordingly as follows:

interface CondWires#(type n);
   method Bit#(n) wires;
   method Action clear;
endinterface

// The "wires" method tells which conditions have been set, and the
// "clear" method resets them all to 0.  It is parameterized on the
// number of wires.

// The items in our extra collection will be interfaces of the
// following type:

interface Condition;
   method Integer index;
   method Bool condition;
endinterface

// The "index" method indicates which wire is to be set if the
// "condition" method ever returns True.

// We next define the "CondModule" type.  This is to behave like an
// ordinary module providing an interface of type "i", except that it
// also can collect items of type "Condition":

typedef ModuleCollect#(Condition, i) CondModule#(type i);

// The next definition shows how items are added to the collection.
// This is the module which will be instantiated at various places in
// the design, to test various conditions.  It takes one static
// parameter, "ix", to specify which wire is to carry this condition,
// and one dynamic parameter (one varying at run-time) "c", giving the
// value of the condition itself.  

module [CondModule] testCondition#(Integer ix)(Bool c, Empty ifc);
   // A new item for the collection is defined:
   let item = (interface Condition;
		  method index;
		     return (ix);
		  endmethod
		  
		  method condition;
		     return (c);
		  endmethod
	       endinterface);

   // The item is added to the collection, using a function defined in
   // the ModuleCollect package:
   addToCollection(item);
endmodule

// We use "testCondition" in the code for our design, and we attach our
// design to a testbench as usual (see below).  Let us assume that the
// result is a stand-alone module with an interface of type "Empty".
// The following definition takes such a module as parameter "mkM",
// brings out its collection of "Condition" items, and defines a module
// with a "CondWires" interface, as required for the top level.  Note
// that this definition produces an ordinary module, as the "[Module]"
// indicates: 

module [Module] mkCondWrapper#(CondModule#(Empty) mkM)(CondWires#(n));
   // We use the module "exposeCollection", in the "ModuleCollect"
   // package.  This has an interface consisting of the interface to
   // the original module (which happens to be of type "Empty"), and a
   // "List" of items of the collected type ("Condition" in this case):
   IWithCollection#(Condition, Empty) ecs();
   exposeCollection#(mkM) the_dut(ecs);

   // We select the list of collected items:
   let cs = ecs.collection;
   // We check that all the indices for wires are within range:
   for (Integer i=0; i<length(cs); i=i+1)
      staticAssert((cs[i]).index  < valueOf(n), 
		   "Condition index out of range");

   // Declare and initialise a list of registers to remember which
   // wires have been set (we use an array of individual registers to
   // avoid conflicts if several are to be set at once):
   List#(Reg#(Bit#(1))) rs = List::replicate(valueOf(n), ?);
   for (Integer i=0; i<valueOf(n); i=i+1)
      begin
	 Reg#(Bit#(1)) r();
	 mkReg#(0) an_r(r);
	 rs[i] = asReg(r);
      end

   // This rule (which, as we check by setting attributes, fires on
   // each clock) sets any register for which the corresponding
   // condition is satisfied:
   (* no_implicit_conditions, fire_when_enabled *)
   rule setRs;
      for (Integer i=0; i<length(cs); i=i+1)
	 if ((cs[i]).condition)
	    (rs[(cs[i]).index]) <= 1;
   endrule
     
   // This method delivers the array of values in the registers.
   method wires;
      // Convert the array to a "Vector", so that its length is known to
      // the compiler (this is necessary for an interface which is to
      // be synthesized into Verilog wires):
      Vector#(n, Reg#(Bit#(1))) rsn = toVector(rs);
      // Declare a list of the values in the registers (using an
      // auxiliary function to do the reading):
      function Bit#(1) read(Reg#(Bit#(1)) r) = r;
      let xs = map(read, rsn);
      // Pack up the "Vector" into a bit-pattern, and return it:
      return (pack(xs));
   endmethod

   // The method to clear all the registers:
   method Action clear;
      for (Integer i=0; i<valueOf(n); i=i+1)
	  (rs[i]) <= 0;
   endmethod
endmodule

// --------------------

// The code between this marker and the next one is copied from one of
// the tests in the Bluespec's test suite.  The only changes made are
// as follows:
//
// (1) The modules are specified to be of module type "CondModule"
// (given in square brackets after the "module" keyword);
// (2) Two "testCondition" calls have been inserted into the "mkGCD"
// module.

typedef UInt#(51) NumTyp;

interface ArithIO_IFC #(parameter type aTyp);
    method Action start(aTyp num1, aTyp num2);
    method aTyp result();
endinterface: ArithIO_IFC

module [CondModule] mkGCD(ArithIO_IFC#(NumTyp));
   Reg#(NumTyp) x();
   mkReg#(?) the_x(x);
   
   Reg#(NumTyp) y();
   mkReg#(0) the_y(y);

   // Insert two tests of register values:
   testCondition(0, x==14);
   testCondition(1, y==2);
   
   rule flip (x > y && y != 0);
      x <= y;
      y <= x;
   endrule
   
   rule sub (x <= y && y != 0);
      y <= y - x;
   endrule
   
   method Action start(NumTyp num1, NumTyp num2) if (y == 0);
      action
         x <= num1;
         y <= num2;
      endaction
   endmethod: start
   
   method NumTyp result() if (y == 0);
      result = x;
   endmethod: result
   
endmodule: mkGCD


module [CondModule] mkTbGCD(Empty);
   ArithIO_IFC#(NumTyp) gcd();
   mkGCD the_gcd(gcd);
   
   Reg#(NumTyp) count1();
   mkReg#(19) the_count1(count1);
   Reg#(NumTyp) count2();
   mkReg#(5) the_count2(count2);
   
   Reg#(NumTyp) tbresult();
   mkReg#(0) the_tbresult(tbresult);
   
   Reg#(Bool) started();
   mkReg#(False) the_started(started);

   Reg#(Nat) cycles();
   mkReg#(0) the_cycles(cycles);

   rule start_sim(!started);
      started <= True;
      $dumpvars();
   endrule

   rule count;
      cycles <= cycles+1;
   endrule

   rule stop(cycles>500);
      $finish(0);
   endrule
   
   rule rule1SendInput (True);
      gcd.start(count1, count2);
      count1 <= count1 + 3;
      count2 <= count2 + 2;
   endrule: rule1SendInput
   rule rule2GetResult (True); 
      tbresult <= gcd.result;
   endrule: rule2GetResult
endmodule: mkTbGCD

// --------------------

// Finally comes the new top-level module.  It applies "mkCondWrapper"
// to the testbench module "mkTbGCD" to produce the required top-level
// interface (the wires, together with the "clear" method), and returns
// it:

(* synthesize *)
module [Module] mkTopLevel(CondWires#(2));
   CondWires#(2) ifc();
   mkCondWrapper#(mkTbGCD) the_top_level(ifc);
   return (ifc);
endmodule

endpackage
