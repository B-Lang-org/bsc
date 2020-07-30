package CBus;

import List::*;
import ModuleCollect::*;

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

// Interface for the configuration bus ("back door" interface)
interface CBus#(type sa, type sd);
   method Action           write(Bit#(sa) addr, Bit#(sd) data);
   method Maybe#(Bit#(sd)) read(Bit#(sa) addr);
endinterface

// Interface coupling the CBus interface with the "front door" device interface
interface IWithCBus#(type cbus_IFC, type device_IFC);
   interface cbus_IFC cbus_ifc;
   interface device_IFC device_ifc;
endinterface

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

// Define CBusItem, the type of item to be collected by module collect
typedef CBus#(sa, sd) CBusItem #(type sa, type sd);

// Define ModWithCBus, the type of a module collecting CBusItems
typedef ModuleCollect#(CBusItem#(sa, sd), i) ModWithCBus#(type sa, type sd, type i);

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

// A module wrapper that adds the CBus to the collection and
// returns only the "front door" interface.
module [ModWithCBus#(sa,sd)] collectCBusIFC#(Module#(IWithCBus#(CBus#(sa, sd), i)) m)(i);
   
   IWithCBus#(CBus#(sa, sd), i) double_ifc();
   liftModule#(m) _temp(double_ifc);

   addToCollection(double_ifc.cbus_ifc);

   return(double_ifc.device_ifc);
endmodule

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

// A module wrapper that takes a module with a normal interface,
// processes the collected CBusItems and provides an IWithCBus interface.
module [Module] exposeCBusIFC#(ModWithCBus#(sa, sd, i) sm)
                              (IWithCBus#(CBus#(sa, sd), i));
   
   IWithCollection#(CBusItem#(sa, sd), i) collection_ifc();
   exposeCollection#(sm) _temp(collection_ifc);
   
   let item_list = collection_ifc.collection;
  
   interface CBus cbus_ifc;
      method Action write(Bit#(sa) addr, Bit#(sd) data);
	 
	 function ifc_write(item_ifc);
	    action
	       item_ifc.write(addr, data);
	    endaction
	 endfunction

	 /// write to all collected interfaces
	 joinActions(map(ifc_write, item_list));
      endmethod
      
      method Maybe#(Bit#(sd)) read(Bit#(sa) addr);
	 
	 function ifc_read(item_ifc);
	    return item_ifc.read(addr);
	 endfunction

	 /// fold together the read values for all the collected interfaces
	 let vs = map(ifc_read, item_list);
	 return(foldt(fold_maybes, Invalid, vs));
      endmethod

   endinterface
   interface device_ifc = collection_ifc.device;
endmodule


   
////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

// One basic configuration register with RW capabilities.
module regRW#(Bit#(sa) reg_addr, r reset)(IWithCBus#(CBus#(sa, sd), Reg#(r)))
   provisos (Bits#(r, sr), Add#(k, sr, sd));

   Reg#(r) x();
   mkReg#(reset) _the_x(x);

   interface CBus cbus_ifc;

      method Action write(addr, data);
	 if (addr == reg_addr)
	    begin
	       x <= unpack(truncate(data));
	    end
      endmethod

      method Bit#(sd) read(addr);
	 if (addr == reg_addr)
	    return Valid({0, pack(x)});
	 else
	    return Invalid;
      endmethod

   endinterface
   
   interface Reg device_ifc;
         
      method _read = x._read;

      method _write = x._write;
      
   endinterface

endmodule

// A wrapper to provide just a normal Reg interface and automatically
// add the CBus interface to the collection. THis is the module used
// in designs (as a normal register would be used).
module [ModWithCBus#(sa, sd)] mkCBRegRW#(Bit#(sa) reg_addr, r x)(Reg#(r))
   provisos (Bits#(r, sr), Add#(k, sr, sd));
   let ifc();
   collectCBusIFC#(regRW(reg_addr, x)) _temp(ifc);
   return(ifc);
endmodule

////////////////////////////////////////////////////////////////////////////////
/// Some support functions
////////////////////////////////////////////////////////////////////////////////

// A variant of a BSV library definition: takes an extra parameter, to
// be used in the (previously disallowed) case where the list argument
// is Nil:

function a foldt(function a f(a x1, a x2), a x, List#(a) xs);
      case (xs) matches
	tagged Nil: return (x);
	default: return (fold(f, xs));
      endcase
endfunction

// The function to fold together maybe values. When both are valid, use
// "or" (it shouldn't happen).
function Maybe#(Bit#(n)) fold_maybes ( Maybe#(Bit#(n)) x,  Maybe#(Bit#(n)) y);
   if (!isValid(x) && !isValid(y))
      return Invalid;
   else 
      return Valid(fromMaybe(0,x) | fromMaybe(0,y));
endfunction

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////


endpackage
      