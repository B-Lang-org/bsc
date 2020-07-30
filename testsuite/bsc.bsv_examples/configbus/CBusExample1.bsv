package CBusExample1;

import CBus::*;

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

/// Specific configuration bus size parameters
typedef 10 CBADDRSIZE; //size of configuration address bus to decode
typedef 32 CBDATASIZE; //size of configuration data bus 

typedef ModWithCBus#(CBADDRSIZE, CBDATASIZE, i) MyModWithCBus#(type i);
typedef CBus#(CBADDRSIZE, CBDATASIZE) MyCBus;

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

interface Counter#(type size_t);
   method Bool   isZero();
   method Action decrement();
   method Action load(Bit#(size_t) newval);
endinterface

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

(* synthesize *)
module mkCounterSynth(IWithCBus#(MyCBus, Counter#(8)));
   let ifc();
   exposeCBusIFC#(mkCounter) _temp(ifc);
   return (ifc);
endmodule

module [MyModWithCBus] mkCounter(Counter#(size_t))
   provisos(Add#(size_t, k, CBDATASIZE)); // this provisos ensures the register 
                                          // size is no larger than the
                                          // data size of the configuration bus
    
   Reg#(Bit#(size_t)) counter <- mkCBRegRW(13, 0); // instantiate a configuration
                                                 // register with address 13.

   method Bool isZero();
      return (counter == 0);
   endmethod
   
   method Action decrement();
      counter <= counter - 1;
   endmethod
   
   method Action load(Bit#(size_t) newval);
      counter <= newval;
   endmethod

endmodule

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

(* synthesize *)
module mkCBusExample(Empty);

   let counter_ifc();
   mkCounterSynth the_counter(counter_ifc);
   
   rule display_value (True);
      let read_value = fromMaybe(0, counter_ifc.cbus_ifc.read(13));
      $display ("Current Value %2d at time:", read_value, $time);
   endrule

   rule init_counter (counter_ifc.device_ifc.isZero());
      counter_ifc.device_ifc.load(4);
   endrule

   rule decrement (!counter_ifc.device_ifc.isZero());
      counter_ifc.device_ifc.decrement();
   endrule

   rule done (True);
      let read_value = fromMaybe(0, counter_ifc.cbus_ifc.read(13));
      if (read_value == 1) $finish();
   endrule
   
endmodule

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

endpackage

