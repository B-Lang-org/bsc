
import ModuleCollect::*;
import List::*;
import ListN::*;
import Assert::*;

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

interface AssertionWires#(type n);
   method Bit#(n) wires;
   method Action clear;
endinterface

// The "wires" method tells which conditions have been set, and the
// "clear" method resets them all to 0.  It is parameterized on the
// number of wires.

// The items in our extra collection will be interfaces of the
// following type:

interface AssertionWire;
   method Integer index;
   method Bool fail;
   method Action clear;
endinterface

// The "index" method indicates which wire is to be set if the
// "fail" method ever returns True.

// We next define the "AssertModule" type.  This is to behave like an
// ordinary module providing an interface of type "i", except that it
// also can collect items of type "AssertionWire":

typedef ModuleCollect#(AssertionWire, i) AssertModule#(type i);

typedef Tuple2#(AssertionWires#(n), i) CondIfc#(type i, type n);

// The next definition shows how items are added to the collection.
// This is the module which will be instantiated at various places in
// the design, to test various conditions.  It takes one static
// parameter, "ix", to specify which wire is to carry this condition,
// and one dynamic parameter (one varying at run-time) "c", giving the
// value of the condition itself.  

interface AssertionReg;
   method Action set;
   method Action clear;
endinterface

module [AssertModule] conditionReg#(Integer ix)(AssertionReg);

   Reg#(Bool) cond();
   mkReg#(False) i_cond(cond);

   // A new item for the collection is
   let item = (interface AssertionWire;
                 method index;
                    return (ix);
                 endmethod

                 method fail;
                    return(cond);
                 endmethod
  
                 method Action clear;
                     cond <= False;
                 endmethod
               endinterface);

     addToCollection(item);

     method Action set;
       cond <= True;
     endmethod

     method Action clear;
       cond <= False;
     endmethod

endmodule
                     
function Bool readCond(AssertionWire c);
  return(c.fail);
endfunction
       
module [Module] exposeAssertionWires#(AssertModule#(i) mkI)(CondIfc#(i, n));
   
   IWithCollection#(AssertionWire, i) ecs();
   exposeCollection#(mkI) the_dut(ecs);
   
   // We select the list of collected items:
   let cs = ecs.collection;

   // We check that all the indices for wires are within range:
   for (Integer i=0; i<length(cs); i=i+1)
      staticAssert((cs[i]).index  < valueOf(n), "Assertion index out of range");
        
   // This method delivers the array of values in the registers.
   // Replace with 
   // let c_ifc (which should typecheck)
   // or 
   // AssertionWires#(m) c_ifc (which shouldn't)
   // and you'll get an internal compiler error because the compiler has 
   // incorrectly generalized over the numeric type variable passed to 
   // the AssertionWires constructor - it looks like the computation of 
   // free and bound type variables is incorrect
   AssertionWires#(m) c_ifc = 
     (interface AssertionWires;
        method wires;
          // Convert the array to a "ListN", so that its length is known to
          // the compiler (this is necessary for an interface which is to
          // be synthesized into Verilog wires):
          ListN#(n, Bool) xs = map(readCond, (toListN(cs)));

          // Pack up the "ListN" into a bit-pattern, and return it:
          return (pack(xs));
        endmethod

        // The method to clear all the registers:
        method Action clear;
          for (Integer i=0; i<valueOf(n); i=i+1)
	    (cs[i]).clear;
        endmethod
      endinterface);
    
    let dut_ifc = ecs.device;

    return(tuple2(c_ifc, dut_ifc));

endmodule
 
