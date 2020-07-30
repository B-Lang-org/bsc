package Cocoon;

import Connectable::*;
import Environment::*;
import Memory::*;
import RPC::*;

interface Wires#(type addrt, type datat);
   interface Tuple2#(RWire#(addrt), RWire#(datat)) rd;
   interface RWire#(Tuple2#(addrt, datat)) wr;
endinterface

instance Connectable#(Wires#(addrt, datat), 
		      Wires#(addrt, datat));
   module mkConnection#(Wires#(addrt, datat) cocoon,
			Wires#(addrt, datat) stub) (Empty);
      // At present the right operand can be set to, and the left can be got from:
      mkConnection(stub.rd.fst, cocoon.rd.fst);
      mkConnection(cocoon.rd.snd, stub.rd.snd);
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
      interface Tuple2 rd;
	 interface fst = rpc.argwire;
	 interface snd = rpc.reswire;
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
   

   interface Tuple2 rd;
      interface RWire fst;
	 method Action wset(x);
	    result.wset(mem.read(x));
	 endmethod
	 method wget = tagged Invalid;
      endinterface
      interface RWire snd;
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
