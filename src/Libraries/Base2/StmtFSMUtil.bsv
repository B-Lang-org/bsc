package StmtFSMUtil;

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

interface MEState;
   method Action set (Integer value);
   method Action set_delayed (Integer value);
   method Action reset ();
   method Action reset_delayed ();
   method Bool is (Integer value);
endinterface

interface MEStateInternal#(type a);
   method Action set (Integer value);
   method Action set_delayed (Integer value);
   method Action reset ();
   method Action reset_delayed ();
   method Bool is (Integer value);
endinterface

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

function Action setMEState (MEState state, Integer num);
   return state.set(num);
endfunction

function Action set_delayedMEState (MEState state, Integer num);
   return state.set_delayed(num);
endfunction

function Action resetMEState (MEState state);
   return state.reset;
endfunction

function Action reset_delayedMEState (MEState state);
   return state.reset_delayed;
endfunction

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

module mkMEState#(Integer icount) (MEState);

   let count = icount + 1;

   function MEState convertInterface (MEStateInternal#(a) ifc);
      return (interface MEState
		 method set = ifc.set;
	 	 method set_delayed = ifc.set_delayed;
	 	 method reset = ifc.reset;
	 	 method reset_delayed = ifc.reset_delayed;
		 method is = ifc.is;
	      endinterface);
   endfunction

   MEState ifc;

   if (count < 2)
      begin
	 MEStateInternal#(Bit#(1)) _mod <- mkMEStateInternal;
	 ifc = convertInterface(_mod);
      end
   else if (count < 4)
      begin
	 MEStateInternal#(Bit#(2)) _mod <- mkMEStateInternal;
	 ifc = convertInterface(_mod);
      end
   else if (count < 8)
      begin
	 MEStateInternal#(Bit#(3)) _mod <- mkMEStateInternal;
	 ifc = convertInterface(_mod);
      end
   else if (count < 16)
      begin
	 MEStateInternal#(Bit#(4)) _mod <- mkMEStateInternal;
	 ifc = convertInterface(_mod);
      end
   else if (count < 32)
      begin
	 MEStateInternal#(Bit#(5)) _mod <- mkMEStateInternal;
	 ifc = convertInterface(_mod);
      end
   else if (count < 64)
      begin
	 MEStateInternal#(Bit#(6)) _mod <- mkMEStateInternal;
	 ifc = convertInterface(_mod);
      end
   else if (count < 128)
      begin
	 MEStateInternal#(Bit#(7)) _mod <- mkMEStateInternal;
	 ifc = convertInterface(_mod);
      end
   else if (count < 256)
      begin
	 MEStateInternal#(Bit#(8)) _mod <- mkMEStateInternal;
	 ifc = convertInterface(_mod);
      end
   else if (count < 512)
      begin
	 MEStateInternal#(Bit#(9)) _mod <- mkMEStateInternal;
	 ifc = convertInterface(_mod);
      end
   else if (count < 1024)
      begin
	 MEStateInternal#(Bit#(10)) _mod <- mkMEStateInternal;
	 ifc = convertInterface(_mod);
      end
   else if (count < 2048)
      begin
	 MEStateInternal#(Bit#(11)) _mod <- mkMEStateInternal;
	 ifc = convertInterface(_mod);
      end
   else if (count < 4096)
      begin
	 MEStateInternal#(Bit#(12)) _mod <- mkMEStateInternal;
	 ifc = convertInterface(_mod);
      end
   else if (count < 8192)
      begin
	 MEStateInternal#(Bit#(13)) _mod <- mkMEStateInternal;
	 ifc = convertInterface(_mod);
      end
   else
      error("FSM too big.");

   return ifc;

endmodule

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

module mkMEStateInternal (MEStateInternal#(a))
   provisos(Bounded#(a), Bits#(a, sa), Bitwise#(a), Eq#(a), Literal#(a));

   Wire#(a) value_wire <- mkDWire(0);
   Reg#(a) value_reg <- mkReg(1);
   a current_value = 0;
   a delayed_value = 0;
   Bool set_value = False;
   Bool set_delayed_value = False;

   Wire#(a) current_wire_0 <- mkDWire(0);
   Wire#(a) current_wire_1 <- mkDWire(0);
   Wire#(a) delayed_wire_0 <- mkDWire(0);
   Wire#(a) delayed_wire_1 <- mkDWire(0);
   Wire#(Bool) set_wire_0 <- mkDWire(False);
   Wire#(Bool) set_delayed_wire_0 <- mkDWire(False);
   Wire#(Bool) set_wire_1 <- mkDWire(False);
   Wire#(Bool) set_delayed_wire_1 <- mkDWire(False);

   current_value = current_wire_0 | current_wire_1;
   delayed_value = delayed_wire_0 | delayed_wire_1;
   set_value = set_wire_0 || set_wire_1;
   set_delayed_value = set_delayed_wire_0 || set_delayed_wire_1;

   rule every;
      if (set_value)
	 value_wire <= current_value;
      else
	 value_wire <= value_reg;
   endrule

   rule every_delayed;
      if (set_delayed_value)
	 value_reg <= delayed_value;
      else if (set_value)
	 value_reg <= current_value;
   endrule

   method Action set (Integer value);
      current_wire_0 <= fromInteger(value);
      set_wire_0 <= True;
   endmethod

   method Action set_delayed (Integer value);
      delayed_wire_0 <= fromInteger(value);
      set_delayed_wire_0 <= True;
   endmethod

   method Action reset ();
      current_wire_1 <= 0;
      set_wire_1 <= True;
   endmethod

   method Action reset_delayed ();
      delayed_wire_1 <= 0;
      set_delayed_wire_1 <= True;
   endmethod

   method Bool is (Integer value);
      return (fromInteger(value) == value_wire);
   endmethod

endmodule

endpackage
