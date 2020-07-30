package Zow2;

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

module mkZow0#(a dflt) (Reg#(a))
   provisos (Bits #(a, sa)) ;
   Reg#(a) ifc;
   
   ifc = (interface Reg
	     method a _read;
		return unpack(0);
	     endmethod
	     method Action _write(a value);
	     endmethod
	  endinterface);

   return ifc;
endmodule

module mkZow1#(a dflt) (Reg#(a))
   provisos (Bits #(a, sa)) ;
   Reg#(a) ifc;
   
   if (valueOf(sa) == 0)
      begin
	 ifc = (interface Reg
		   method a _read;
		      return unpack(0);
		   endmethod
		   method Action _write(a value);
		   endmethod
		endinterface);
      end
   else
      begin
	 ifc = (interface Reg
		   method a _read;
		      return unpack(0);
		   endmethod
		   method Action _write(a value);
		   endmethod
		endinterface);
      end
   return asIfc(ifc);
endmodule

endpackage
