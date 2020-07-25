////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

package ZBus;

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

import List::*;
import ZBusUtil::*;

//@ \subsubsection{ZBus}
//@ \index{ZBus@\te{ZBus} (package)|textbf}
//@ BSV provides the \te{ZBus} library to allow users to implement and use
//@ tri-state buses. Since BSV does not support high-impedance or
//@ undefined values internally, the library encapsulates the tri-state
//@ bus implementation in a module that can only be accessed through
//@ predefined interfaces which do not allow direct access to internal
//@ signals (which could potentially have high-impedance or undefined
//@ values).
//@
//@ The Verilog implementation of the tri-state module includes a number
//@ of primitive sub-modules that are implemented using Verilog tri-state
//@ wires. The BSV representation of the bus, however, only models the
//@ values of the bus at the associated interfaces and thus the need to
//@ represent high-impedance or undefined values in BSV is avoided.

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

module mkZBus#(List#(ZBusBusIFC#(t)) ifc_list)(Empty)
   provisos (Eq#(t), Bits#(t, st));

   ZBusInternalIFC#(t) bus();
   mkZBusInternal#(ifc_list) the_bus(bus);

   let fromBusValid =  bStateToValid(resolveBusBState(ifc_list));

   rule update_IFCs (True);
      updateFromBus(ifc_list, bus.zout, fromBusValid);
   endrule

endmodule

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

function Action updateFromBus(List#(ZBusBusIFC#(t)) ifc_list, ZBit#(t) zout, Bool isvalid);
   action
      if (length(ifc_list) > 0)
	 begin
	    updateZBusBusIFCFromBus(head(ifc_list), zout, isvalid);
	    updateFromBus(tail(ifc_list), zout, isvalid);
	 end
   endaction
endfunction

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

function Action updateZBusBusIFCFromBus(ZBusBusIFC#(t) ifc, ZBit#(t) zout, Bool isvalid);
   action
      ifc.fromBusSample(zout, isvalid);
   endaction
endfunction

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

function Bool bStateToValid(BState bstate);
   return (bstate == HiZN);
endfunction

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

interface ZBusInternalIFC #(type t);
   method ZBit#(t) zout();
endinterface: ZBusInternalIFC

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

module mkZBusInternal#(List#(ZBusBusIFC#(t)) ifc_list)(ZBusInternalIFC#(t))
   provisos (Eq#(t), Bits#(t, st));

   ZBit#(t) zout_final;
   if (length(ifc_list) == 2)
      begin
  	 ResolveZ#(t) i1();
  	 mkResolveZ the_i1(i1);
	
  	 zout_final =
  	 i1.resolve(zBusIFCGetToBusValue(head(ifc_list)),
  		    zBusIFCGetToBusValue(head(tail(ifc_list))));
      end
   else
      begin

  	 ResolveZ#(t) i1();
  	 mkResolveZ the_i1(i1);
	
 	 ZBusInternalIFC#(t) i2();
  	 mkZBusInternal#(tail(ifc_list)) the_i2(i2);

	 zout_final =
	 i1.resolve(zBusIFCGetToBusValue(head(ifc_list)),
		    i2.zout);
      end

   method zout() ;
      return zout_final;
   endmethod

endmodule

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

function ZBit#(t) zBusIFCGetToBusValue(ZBusBusIFC#(t) ifc);
   return ifc.toBusValue();
endfunction

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

//@ The interfaces are defined as follows:
//@
//@ \index{ZBusClientIFC@\te{ZBusClientIFC} (interface)|textbf}
//@ \begin{libverbatim}
//@ interface ZBusClientIFC #(type t) ;
//@    method Action      drive(t value);
//@    method t           get();
//@    method Bool        fromBusValid();
//@ endinterface
//@ \end{libverbatim}
//@
//@ \index{ZBusBusIFC@\te{ZBusBusIFC} (interface)|textbf}
//@ \begin{libverbatim}
//@ interface ZBusBusIFC #(type t) ;
//@    method Action      fromBusSample(ZBit#(t) value, Bool isValid);
//@    method ZBit#(t)    toBusValue();
//@    method Bool        toBusCtl();
//@ endinterface
//@ \end{libverbatim}
//@

interface ZBusBusIFC #(type t) ;
   method Action      fromBusSample(ZBit#(t) value, Bool isJust);
   method ZBit#(t)    toBusValue();
   method Bool        toBusCtl();
endinterface

//@ \index{ZBusDualIFC@\te{ZBusDualIFC} (interface)|textbf}
//@ \begin{libverbatim}
//@ interface ZBusDualIFC #(type t) ;
//@    method ZBusBusIFC#(t)    busIFC;
//@    method ZBusClientIFC#(t) clientIFC;
//@ endinterface
//@ \end{libverbatim}
//@


//@ The \te{ZBusClientIFC} allows a BSV module to connect to the tri-state
//@ bus.  For this interface There are no tri-state values as either
//@ method arguments or return values.  The \te{ZBusBuslIFC} interface
//@ connects to the bus structure itself (using tri-state values). The
//@ \te{ZBusDualIFC} interface includes one ZBusBusIFC and one ZBusClientIFC.
//@ For a given bus, one \te{ZBusDualIFC} interface is associated with
//@ each bus client.

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

//@ The library also provides a module constructor function,
//@ \te{mkZBusBuffer}, which allows the user to create a module which
//@ provides the \te{ZBusDualIFC} interface.
//@
//@ \index{mkZBusBuffer@\te{mkZBusBuffer} (function)|textbf}
//@ \begin{libverbatim}
//@ module mkZBusBuffer (ZBusDualIFC #(t))
//@    provisos (Eq#(t), Bits#(t,st));
//@ \end{libverbatim}
//@
//@ This module provides essentially the functionality of a tri-state
//@ buffer.  The following code fragment creates a tri-state buffer (with
//@ an interface named buffer\_0) for a 32 bit signal.
//@
//@ \begin{libverbatim}
//@    ZBusDualIFC#(Bit#(32)) buffer_0();
//@    mkZBusBuffer inst_buffer_0(buffer_0);
//@ \end{libverbatim}
//@
//@ This code fragment drives a value of \te{12} onto the associated bus.
//@
//@ \begin{libverbatim}
//@    buffer_0.clientIFC.drive(12);
//@ \end{libverbatim}
//@
//@ The \te{get()} and \te{fromBusValid()} methods (associated
//@ with the \te{ZBusClientIFC} interface) allow each bus client to access the
//@ current value on the bus. If the bus is in an invalid state (i.e. has
//@ a high-impedance value or an undefined value because it is being
//@ driven by more than one client simultaneously), then the
//@ \te{get()} method will return \te{0} and the
//@ \te{fromBusValid()} method will return \te{False}.  In all other
//@ cases, the \te{fromBusValid()} method will return \te{True} and the
//@ \te{get()} method will return the current value of the bus.



////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

typedef enum {HiZN, HiZ, Nothing} BState
              deriving (Eq, Bits);

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

function BState resolveBusBState (List#(ZBusBusIFC #(t)) ifc_list);

   if (length(ifc_list) == 0)
      return HiZ;
   else
      return resolveBState(getBStateFromZBusIFC(head(ifc_list)),
			   resolveBusBState(tail(ifc_list)));
endfunction

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

function BState getBStateFromZBusIFC (ZBusBusIFC#(t) ifc);
   return createBState(ifc.toBusCtl);
endfunction

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

function BState createBState (Bool driven);
   if (driven)
      return HiZN;
   else
      return HiZ;
endfunction

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

function BState resolveBState (BState bs_0, BState bs_1);
   if ((bs_0 == Nothing) || (bs_1 == Nothing) || ((bs_0 == HiZN) && (bs_1 == HiZN)))
      return Nothing;
   else if ((bs_0 == HiZN) || (bs_1 == HiZN))
      return HiZN;
   else
      return HiZ;
endfunction

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

//@ Finally, the \te{ZBus} library provides the \te{mkZBus} module
//@ constructor function.
//@
//@ \index{mkZBus@\te{mkZBus} (function)|textbf}
//@ \begin{libverbatim}
//@ module mkZBus#(List#(ZBusBusIFC#(t)) ifc_list)(Empty)
//@    provisos (Eq#(t), Bits#(t, st));
//@ \end{libverbatim}
//@
//@ This function takes a list of \te{ZBusBusIFC} interfaces as arguments
//@ and creates a module which ties them all together in a bus. The
//@ following code fragment demonstrates its use.
//@
//@ \begin{libverbatim}
//@    ZBusDualIFC#(Bit#(32)) buffer_0();
//@    mkZBusBuffer inst_buffer_0(buffer_0);
//@
//@    ZBusDualIFC#(Bit#(32)) buffer_1();
//@    mkZBusBuffer inst_buffer_1(buffer_1);
//@
//@    ZBusDualIFC#(Bit#(32)) buffer_2();
//@    mkZBusBuffer inst_buffer_2(buffer_2);
//@
//@    List#(ZBusIFC#(Bit#(32))) ifc_list;
//@
//@    bus_ifc_list = cons(buffer_0.busIFC,
//@                         cons(buffer_1.busIFC,
//@                              cons(buffer_2.busIFC,
//@                                        nil)));
//@
//@    Empty bus_ifc();
//@    mkZBus#(bus_ifc_list) inst_bus(bus_ifc);
//@ \end{libverbatim}

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

interface ZBusClientIFC #(type t) ;
   method Action      drive(t value);
   method t           get();
   method Bool        fromBusValid();
endinterface

interface ZBusDualIFC #(type t) ;
   interface ZBusBusIFC#(t)    busIFC;
   interface ZBusClientIFC#(t) clientIFC;
endinterface

module mkZBusBuffer (ZBusDualIFC #(t))
   provisos (Eq#(t), Bits#(t,st));

   RWire#(t) value_reg();
   mkRWire reg_0(value_reg);

   RWire#(t) bus_value_reg();
   mkRWire reg_1(bus_value_reg);

   RWire#(t) bus_value_reg_out();
   mkRWire reg_1_out(bus_value_reg_out);

   RWire#(Bool) bus_valid_reg();
   mkRWire reg_3(bus_valid_reg);

   RWire#(Bool) bus_valid_reg_out();
   mkRWire reg_3_out(bus_valid_reg_out);

   PulseWire driven <- mkPulseWire;

   ConvertToZ#(t)   to_z   <- mkConvertToZ;
   ConvertFromZ#(t) from_z <- mkConvertFromZ;

   rule every (True);
      bus_value_reg_out.wset(unJust(bus_value_reg.wget()));
      bus_valid_reg_out.wset(unJust(bus_valid_reg.wget()));
   endrule

   interface ZBusBusIFC busIFC;

      method Action fromBusSample(ZBit#(t) value, Bool isJust);
	 action
	    if (isJust)
	       bus_value_reg.wset(from_z.convert(value));
	    else
	       bus_value_reg.wset(unpack(0));
	    bus_valid_reg.wset(isJust);
	 endaction
      endmethod

      method ZBit#(t) toBusValue();
	 let value = (driven ? unJust(value_reg.wget()) : ?);
	 return to_z.convert(value, driven);
      endmethod

      method Bool toBusCtl();
	 return driven;
      endmethod

   endinterface

   interface ZBusClientIFC clientIFC ;

      method Action drive(value);
	 action
	    value_reg.wset(value);
	    driven.send();
	 endaction
      endmethod

      method t get();
	 return unJust(bus_value_reg_out.wget());
      endmethod

      method Bool fromBusValid();
	 return unJust(bus_valid_reg_out.wget());
      endmethod

   endinterface

endmodule

endpackage

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////
