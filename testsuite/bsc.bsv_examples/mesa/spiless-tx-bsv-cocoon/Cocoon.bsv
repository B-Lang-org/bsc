package Cocoon;

import Connectable::*;
import Environment::*;
import Memory::*;
import RPC::*;

// A tuple is not a valid (sub)interface, so the read pair is a named interface.
interface ReadWires#(type addrt, type datat);
   interface RWire#(addrt) addr;
   interface RWire#(datat) data;
endinterface

interface Wires#(type addrt, type datat);
   interface ReadWires#(addrt, datat) rd;
   interface RWire#(Tuple2#(addrt, datat)) wr;
endinterface

instance Connectable#(Wires#(addrt, datat),
		      Wires#(addrt, datat));
   module mkConnection#(Wires#(addrt, datat) cocoon,
			Wires#(addrt, datat) stub) (Empty);
      // At present the right operand can be set to, and the left can be got from:
      mkConnection(stub.rd.addr, cocoon.rd.addr);
      mkConnection(cocoon.rd.data, stub.rd.data);
      mkConnection(stub.wr, cocoon.wr);
   endmodule
endinstance

interface Stub#(type addrt, type datat);
   interface Memory#(addrt, datat) mem;
   interface Wires#(addrt, datat) cocoon;
endinterface

module mkStub(Stub#(addrt, datat))
   provisos (Bits#(addrt, sa), Bits#(datat, sd), Bounded#(addrt));

   IRPC#(addrt, datat) rpc <- mkRPC;
   RWire#(Tuple2#(addrt, datat)) wrrw <- mkRWire;

   interface Memory mem;
      method read = rpc.fn;
      method Action write(a, x);
	 wrrw.wset(tuple2(a,x));
      endmethod
   endinterface
   interface Wires cocoon;
      interface ReadWires rd;
	 interface addr = rpc.argwire;
	 interface data = rpc.reswire;
      endinterface
      interface RWire wr;
	 method wget = wrrw.wget;
	 method wset(v) = noAction;
      endinterface
   endinterface
endmodule


module mkCocoon(Memory#(addrt, datat) mem, Wires#(addrt, datat) w)
   provisos (Bits#(addrt, sa), Bits#(datat, sd), Bounded#(addrt));

   RWire#(datat) result <- mkRWire;
   RWire#(Tuple2#(addrt,datat)) wrrw <- mkRWire;

   rule write_mem (isValid(wrrw.wget));
      match {.a, .x} = validValue(wrrw.wget);
      mem.write(a,x);
   endrule


   interface ReadWires rd;
      interface RWire addr;
	 method Action wset(x);
	    result.wset(mem.read(x));
	 endmethod
	 method wget = tagged Invalid;
      endinterface
      interface RWire data;
	 method wset(v) = noAction;
	 method wget = result.wget;
      endinterface
   endinterface

   interface RWire wr;
      method wget = tagged Invalid;
      method wset = wrrw.wset;
   endinterface
endmodule


endpackage
