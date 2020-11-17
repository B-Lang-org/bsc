
`ifdef BSV_NO_Z
  `define BSV_GENC True
`else
  `define BSV_GENC genC
`endif

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

package ZBusUtil;

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

export ZBit;
export mkZBit;
export zBitGetWord;
export ConvertToZ(..);
export mkConvertToZ;
export ConvertFromZ(..);
export mkConvertFromZ;
export ResolveZ(..);
export mkResolveZ;

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

typedef struct {
		t word;
		} ZBit #(type t) deriving (Eq, Bits);

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

function ZBit#(t) mkZBit(t w);
   return ((ZBit { word : w}));
endfunction

function t zBitGetWord(ZBit#(t) wz);
   return (wz.word);
endfunction

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

interface ConvertToZ #(type i);
   method ZBit#(i) convert(i x1, Bool x2);
endinterface

import "BVI" ConvertToZ = module vMkConvertToZ (ConvertToZ#(i))
			  provisos (Bits#(i,si));
                             default_clock clk();
			     parameter width = valueOf(si);
			     no_reset;
			     method OUT convert(IN, CTL);
                                schedule convert CF convert ;
			  endmodule

module mkConvertToZ(ConvertToZ#(i))
   provisos (Eq#(i), Bits#(i, si), Bits#(ZBit#(i), sz));
   ConvertToZ#(i) ifc;
   if (`BSV_GENC)
      ifc = interface ConvertToZ
	       method convert(word, enable) ;
		  return (bitToZBit(word, enable));
	       endmethod
	    endinterface;
   else begin
      ConvertToZ#(i) _a();
      vMkConvertToZ inst__a(_a);
      ifc = _a;
   end
   return (ifc);
endmodule

function ZBit#(i) bitToZBit(i word, Bool enable)
   provisos (Eq#(i), Bits#(i, si));
   return ((enable ? mkZBit(word) : mkZBit(unpack(0))));
endfunction

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

interface ConvertFromZ #(type i);
   method i convert(ZBit#(i) x1);
endinterface

import "BVI" ConvertFromZ = module vMkConvertFromZ (ConvertFromZ#(i))
			    provisos (Bits#(i,si));
                               default_clock clk();
			       parameter width = valueOf(si);
			       no_reset;
			       method OUT convert(IN);
			       schedule convert CF convert;
			    endmodule

module mkConvertFromZ(ConvertFromZ#(i))
   provisos (Eq#(i), Bits#(ZBit#(i), sz), Bits#(i, si1));
   ConvertFromZ#(i) ifc;
   if (`BSV_GENC)
      ifc = interface ConvertFromZ
	       method convert(k) ;
		  return (zBitToBit(k));
	       endmethod
	    endinterface;
   else begin
      ConvertFromZ#(i) _a();
      vMkConvertFromZ inst__a(_a);
      ifc = _a;
   end
   return (ifc);
endmodule

function i zBitToBit(ZBit#(i) wz)
   provisos (Eq#(i));
   return (zBitGetWord(wz));
endfunction

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

interface ResolveZ #(type i);
   method ZBit#(i) resolve(ZBit#(i) x1, ZBit#(i) x2);
endinterface: ResolveZ

import "BVI" ResolveZ = module vMkResolveZ  (ResolveZ#(i))
			provisos (Bits#(i,si));
                           default_clock clk();
			   parameter width = valueOf(si);
			   no_reset;
			   method OUT resolve(IN_0, IN_1);
                              schedule resolve CF resolve;
			endmodule

module mkResolveZ(ResolveZ#(i))
   provisos (Eq#(i), Bits#(i, si), Bits#(ZBit#(i), sz));
   ResolveZ#(i) ifc;
   if (`BSV_GENC)
      ifc = interface ResolveZ
	       method resolve(in_0, in_1) ;
		  return (resolveZ(in_0, in_1));
	       endmethod
	    endinterface;
   else begin
      ResolveZ#(i) _a();
      vMkResolveZ inst__a(_a);
      ifc = _a;
   end
   return (ifc);
endmodule

function ZBit#(i) resolveZ(ZBit#(i) wz_0, ZBit#(i) wz_1)
  provisos (Eq#(i), Bits#(i, si));
  return (mkZBit(unpack(pack(zBitGetWord(wz_0)) | pack(zBitGetWord(wz_1)))));
endfunction

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

endpackage

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////
