package FIFOF_ ;

export FIFOF_(..) ;
export mkFIFOF_ ;
export mkFIFOF1_ ;
export mkSizedFIFOF_ ;
export mkDepthParamFIFOF_;
export mkLFIFOF_ ;
export mkLSizedFIFOF_ ;
export mkDepthParamLFIFOF_;


//@ This is an internal, undocumented package
//@ To use FIFOs in BSV use the \te{FIFO} or \te{FIFOF} packages

// the i_ versions of the notFull and notEmpty signals are conflict-free
// with enq and deq so that the implicit conditions in a guarded FIFO
// (with or without explicit full and empty signals)
// do not create a conflict between enq and deq

interface FIFOF_ #(type a) ;
    method Action enq(a x1) ;
    method Action deq() ;
    method a first() ;
    method Action clear() ;
    method Bool notFull() ;
    method Bool i_notFull() ;
    method Bool notEmpty() ;
    method Bool i_notEmpty() ;
endinterface: FIFOF_

instance FShow#(FIFOF_#(a))
   provisos(FShow#(a));
   function Fmt fshow (FIFOF_#(a) ifc);
      case (tuple2(ifc.i_notEmpty, ifc.i_notFull)) matches
	 { True,  True}: return  fshow(ifc.first);
	 { True, False}: return (fshow(ifc.first) + fshow(" ") + fshow("FULL"));
	 {False,  True}: return  $format("EMPTY");
	 {False, False}: return  $format("EMPTY");
      endcase
   endfunction
endinstance

// The name is prefixed with V because this is an internal interface.
// We don't expect users to instantiate a zero-width FIFO directly;
// if they instantiate a FIFO and the width is zero, the BSV wrapper
// will choose to instantiate a FIFO with this interface under the covers.
interface VFIFOF0_ ;
    method Action enq() ;
    method Action deq() ;
    method Action clear() ;
    method Bool notFull() ;
    method Bool i_notFull() ;
    method Bool notEmpty() ;
    method Bool i_notEmpty() ;
endinterface: VFIFOF0_

// Depth 1, width > 0
import "BVI" FIFO1 =
  module vMk1FIFOF#(Bool g) (FIFOF_#(a))
  provisos (Bits#(a,sa));
    default_clock clk(CLK, (*unused*)CLK_GATE);
    parameter width = valueOf(sa);
    parameter guarded = g;
    method enq((* reg *)D_IN) enable(ENQ);
    method deq() enable(DEQ);
    method (* reg *)D_OUT first;
    method (* reg *)FULL_N   notFull;
    method (* reg *)FULL_N i_notFull;
    method (* reg *)EMPTY_N   notEmpty;
    method (* reg *)EMPTY_N i_notEmpty;
    method clear() enable(CLR);
    schedule deq CF (enq, i_notEmpty, i_notFull) ;
    schedule enq CF (deq, first, i_notEmpty, i_notFull) ;
    schedule (first, notEmpty, notFull) CF
               (first, i_notEmpty, i_notFull, notEmpty, notFull) ;
    schedule (i_notEmpty, i_notFull) CF
               (clear, first, i_notEmpty, i_notFull, notEmpty, notFull) ;
    schedule (clear, deq, enq) SBR clear ;
    schedule first SB (clear, deq) ;
    schedule (notEmpty, notFull) SB (clear, deq, enq) ;
    schedule deq C deq;
    schedule enq C enq;
  endmodule: vMk1FIFOF

// Depth 1, width == 0
import "BVI" FIFO10 =
  module vMk1FIFOF0#(Bool g) (VFIFOF0_) ;
    default_clock clk(CLK, (*unused*)CLK_GATE);
    parameter guarded = g;
    method enq() enable(ENQ);
    method deq()enable(DEQ);
    method (* reg *)FULL_N   notFull;
    method (* reg *)FULL_N i_notFull;
    method (* reg *)EMPTY_N   notEmpty;
    method (* reg *)EMPTY_N i_notEmpty;
    method clear() enable(CLR);
    schedule deq CF (enq, i_notEmpty, i_notFull) ;
    schedule enq CF (deq, i_notEmpty, i_notFull) ;
    schedule (i_notEmpty, i_notFull) CF
               (clear, i_notEmpty, i_notFull, notEmpty, notFull) ;
    schedule (notEmpty, notFull) CF
               (i_notEmpty, i_notFull, notEmpty, notFull) ;
    schedule (clear, deq, enq) SBR clear ;
    schedule (notEmpty, notFull) SB (clear, deq, enq) ;
    schedule deq C deq;
    schedule enq C enq;
  endmodule: vMk1FIFOF0

// Depth 1
module mkFIFOF1_#(Bool g)(FIFOF_#(a))
  provisos (Bits#(a, sa)) ;
  FIFOF_#(a) ifc ;
  if (valueOf(sa) == 0)
     begin
	VFIFOF0_ _f() ;
        vMk1FIFOF0#(g) __(_f) ;

	ifc = (interface FIFOF_;
		  method Action enq(x);
		     _f.enq ;
		  endmethod
		  method deq = _f.deq ;
		  method first = ? ;
		  method notFull = _f.notFull ;
		  method i_notFull = _f.i_notFull ;
		  method notEmpty = _f.notEmpty ;
		  method i_notEmpty = _f.i_notEmpty ;
		  method clear = _f.clear ;
	       endinterface);
     end
  else
     begin
	FIFOF_#(a) _f() ;
	vMk1FIFOF#(g) __(_f) ;
	ifc = _f;
     end
   return (ifc);
endmodule: mkFIFOF1_

// Depth 2, width > 0.
import "BVI" FIFO2 =
  module vMk2FIFOF#(Bool g) (FIFOF_#(a))
  provisos (Bits#(a,sa));
    default_clock clk(CLK, (*unused*)CLK_GATE);
    parameter width = valueOf(sa);
    parameter guarded = g;
    method enq((* reg *)D_IN) enable(ENQ);
    method deq()enable(DEQ);
    method (* reg *)D_OUT first;
    method (* reg *)FULL_N   notFull;
    method (* reg *)FULL_N i_notFull;
    method (* reg *)EMPTY_N   notEmpty;
    method (* reg *)EMPTY_N i_notEmpty;
    method clear() enable(CLR);
    schedule deq CF (enq, i_notEmpty, i_notFull) ;
    schedule enq CF (deq, first, i_notEmpty, i_notFull) ;
    schedule (first, notEmpty, notFull) CF
               (first, i_notEmpty, i_notFull, notEmpty, notFull) ;
    schedule (i_notEmpty, i_notFull) CF
               (clear, first, i_notEmpty, i_notFull, notEmpty, notFull) ;
    schedule (clear, deq, enq) SBR clear ;
    schedule first SB (clear, deq) ;
    schedule (notEmpty, notFull) SB (clear, deq, enq) ;
    schedule deq C deq;
    schedule enq C enq;
  endmodule: vMk2FIFOF

// Depth 2, width == 0.
import "BVI" FIFO20 =
  module vMk2FIFOF0#(Bool g) (VFIFOF0_) ;
    default_clock clk(CLK, (*unused*)CLK_GATE);
    parameter guarded = g;
    method enq() enable(ENQ);
    method deq()enable(DEQ);
    method (* reg *)FULL_N   notFull;
    method (* reg *)FULL_N i_notFull;
    method (* reg *)EMPTY_N   notEmpty;
    method (* reg *)EMPTY_N i_notEmpty;
    method clear() enable(CLR);
    schedule deq CF (enq, i_notEmpty, i_notFull) ;
    schedule enq CF (deq, i_notEmpty, i_notFull) ;
    schedule (i_notEmpty, i_notFull, notEmpty, notFull) CF
               (i_notEmpty, i_notFull, notEmpty, notFull) ;
    schedule (i_notEmpty, i_notFull) CF clear ;
    schedule (clear, deq, enq) SBR clear ;
    schedule (notEmpty, notFull) SB (clear, deq, enq) ;
    schedule deq C deq;
    schedule enq C enq;
  endmodule: vMk2FIFOF0

// Depth 2
module mkFIFOF2_#(Bool g)(FIFOF_#(a))
   provisos (Bits#(a, sa)) ;
   FIFOF_#(a) ifc ;
   if (valueOf(sa) == 0)
      begin
	 VFIFOF0_ _f() ;
	 vMk2FIFOF0#(g) __(_f) ;

	 ifc = (interface FIFOF_;
		   method Action enq(x);
		     _f.enq ;
		   endmethod
		   method deq = _f.deq ;
		   method first = ? ;
		   method notFull = _f.notFull ;
		   method i_notFull = _f.i_notFull ;
		   method notEmpty = _f.notEmpty ;
		   method i_notEmpty = _f.i_notEmpty ;
		   method clear = _f.clear ;
		endinterface);
      end
   else
      begin
	 FIFOF_#(a) _f() ;
	 vMk2FIFOF#(g)  __(_f) ;
	 ifc = _f;
      end
   return (ifc) ;
endmodule: mkFIFOF2_

// default depth is 2
module mkFIFOF_#(Bool g)(FIFOF_#(a))
  provisos (Bits#(a, sa)) ;
  FIFOF_#(a) ifc() ;
  mkFIFOF2_#(g) __(ifc) ;
  return (ifc) ;
endmodule: mkFIFOF_


// Depth n, width > 0
// log2 (n-1) is allowed since the Verilog model has a registered output
// which is not considered in the head/tail pointers size.
import "BVI" SizedFIFO =
  module vMkSizedNFIFOF#(Integer depth, Bool g) (FIFOF_#(a))
  provisos (Bits#(a,sa));
    default_clock clk(CLK, (*unused*)CLK_GATE);
    parameter p1width = valueOf(sa);
    parameter p2depth = depth;
    parameter p3cntr_width = log2(depth-1);
    parameter guarded = g;
    method enq((* reg *)D_IN) enable(ENQ);
    method deq() enable(DEQ);
    method (* reg *)D_OUT first;
    method (* reg *)FULL_N   notFull;
    method (* reg *)FULL_N i_notFull;
    method (* reg *)EMPTY_N   notEmpty;
    method (* reg *)EMPTY_N i_notEmpty;
    method clear() enable(CLR);
    schedule deq CF (enq, i_notEmpty, i_notFull) ;
    schedule enq CF (deq, first, i_notEmpty, i_notFull) ;
    schedule (first, notEmpty, notFull) CF
               (first, i_notEmpty, i_notFull, notEmpty, notFull) ;
    schedule (i_notEmpty, i_notFull) CF
               (clear, first, i_notEmpty, i_notFull, notEmpty, notFull) ;
    schedule (clear, deq, enq) SBR clear ;
    schedule first SB (clear, deq) ;
    schedule (notEmpty, notFull) SB (clear, deq, enq) ;
    schedule deq C deq;
    schedule enq C enq;
  endmodule: vMkSizedNFIFOF

// Depth n, width == 0
import "BVI" SizedFIFO0 =
  module vMkSizedNFIFOF0#(Integer depth, Bool g)(VFIFOF0_) ;
    default_clock clk(CLK, (*unused*)CLK_GATE);
    parameter p1depth = depth;
    parameter p2cntr_width = log2(depth+1);
    parameter guarded = g;
    method enq() enable(ENQ);
    method deq()enable(DEQ);
    method (* reg *)FULL_N   notFull;
    method (* reg *)FULL_N i_notFull;
    method (* reg *)EMPTY_N   notEmpty;
    method (* reg *)EMPTY_N i_notEmpty;
    method clear() enable(CLR);
    schedule deq CF (enq, i_notEmpty, i_notFull) ;
    schedule enq CF (deq, i_notEmpty, i_notFull) ;
    schedule (i_notEmpty, i_notFull) CF
               (clear, i_notEmpty, i_notFull, notEmpty, notFull) ;
    schedule (notEmpty, notFull) CF
               (i_notEmpty, i_notFull, notEmpty, notFull) ;
    schedule (clear, deq, enq) SBR clear ;
    schedule (notEmpty, notFull) SB (clear, deq, enq) ;
    schedule deq C deq;
    schedule enq C enq;
  endmodule: vMkSizedNFIFOF0

// Depth n
module mkSizedNFIFOF_#(Integer depth, Bool g) (FIFOF_#(a))
   provisos (Bits#(a, sa));
   FIFOF_#(a) ifc ;
   if (valueOf(sa) == 0)
      begin
	 VFIFOF0_ _f() ;
	 vMkSizedNFIFOF0#(depth, g) __(_f) ;

	 ifc = (interface FIFOF_;
		   method Action enq(x);
		     _f.enq ;
		   endmethod
		   method deq = _f.deq ;
		   method first = ? ;
		   method notFull = _f.notFull ;
		   method i_notFull = _f.i_notFull ;
		   method notEmpty = _f.notEmpty ;
		   method i_notEmpty = _f.i_notEmpty ;
		   method clear = _f.clear ;
		endinterface);
      end
   else
      begin
	 FIFOF_#(a) _f() ;
	 vMkSizedNFIFOF#(depth, g) __(_f) ;
	 ifc = _f;
      end
   return (ifc) ;
endmodule: mkSizedNFIFOF_

function m#(FIFOF_#(a)) mkSizedFIFOF_(Integer depth, Bool g)
  provisos (IsModule#(m,c), Bits#(a, sa)) ;
   case (depth)
      0 : return (error("sized fifo created with depth 0!")) ;
      1 : return (mkFIFOF1_(g)) ;
      2 : return (mkFIFOF_(g));
      default : if (depth < 0) return (error("sized fifo created with negative depth!"));
                else return (mkSizedNFIFOF_(depth,g));
   endcase
endfunction: mkSizedFIFOF_

function UInt#(6) getCounterWidth(UInt#(32) depth);
   // implement log2 as a table-lookup because
   // Verilog does not have the appropriate operator

   UInt#(6) result = 32;
   for(Integer i = 31; i > 0; i = i - 1) begin
      // + 1 to  account for fast output register
     let smaller = depth <= (fromInteger(2 ** i) + 1);
     if(smaller) result = fromInteger(i);
   end
   return(result);
endfunction

import "BVI" SizedFIFO =
  module mkDepthParamFIFOF_#(UInt#(32) depth, Bool g) (FIFOF_#(a))
  provisos (Bits#(a,sa));
    default_clock clk(CLK, (*unused*)CLK_GATE);
    parameter p1width = (valueOf(sa) == 0) ? 1 : valueOf(sa);
    parameter p2depth = pack(depth);
    parameter p3cntr_width = pack(getCounterWidth(depth));
    parameter guarded = g;
    method enq((* reg *)D_IN) enable(ENQ);
    method deq() enable(DEQ);
    method (* reg *)D_OUT first;
    method (* reg *)FULL_N   notFull;
    method (* reg *)FULL_N i_notFull;
    method (* reg *)EMPTY_N   notEmpty;
    method (* reg *)EMPTY_N i_notEmpty;
    method clear() enable(CLR);
    schedule deq CF (enq, i_notEmpty, i_notFull) ;
    schedule enq CF (deq, first, i_notEmpty, i_notFull) ;
    schedule (first, notEmpty, notFull) CF
               (first, i_notEmpty, i_notFull, notEmpty, notFull) ;
    schedule (i_notEmpty, i_notFull) CF
               (clear, first, i_notEmpty, i_notFull, notEmpty, notFull) ;
    schedule (clear, deq, enq) SBR clear ;
    schedule first SB (clear, deq) ;
    schedule (notEmpty, notFull) SB (clear, deq, enq) ;
    schedule deq C deq;
    schedule enq C enq;
  endmodule: mkDepthParamFIFOF_

// XXX loopy FIFOs need not be imported as FIFOF_, because the
// XXX internal full/empty signals have the same annotations as the
// XXX exposed signals (because deq and enq are not CF, as with other
// XXX FIFOs).
// Depth 1, width > 0, loopy
import "BVI" FIFOL1 =
  module vMkL1FIFOF (FIFOF_#(a))
  provisos (Bits#(a,sa));
    default_clock clk(CLK, (*unused*)CLK_GATE);
    parameter width = valueOf(sa);
    method enq((* reg *)D_IN) enable(ENQ);
    method deq()enable(DEQ);
    method (* reg *)D_OUT first;
    method FULL_N   notFull;
    method FULL_N i_notFull;
    method (* reg *)EMPTY_N   notEmpty;
    method (* reg *)EMPTY_N i_notEmpty;
    method clear() enable(CLR);
    // The internal ready signals need to give the guarded FIFOF
    // (constructed from this FIFOF_) the right annotations.
    // We want: (first, notEmpty) SB deq SB (notFull, enq) SB clear.
    // Thus,
    schedule i_notEmpty SB (deq, enq, clear);
    schedule deq SBR i_notFull;
    schedule i_notFull SB (enq, clear);
    // and read methods are CF with each other
    schedule (i_notEmpty, i_notFull, notEmpty, notFull, first) CF
               (i_notEmpty, i_notFull, notEmpty, notFull, first);
    // In a guarded LFIFO, the deq method will SB enq, due to the i_notFull.
    // For unguarded LFIFO, the actions are techically composable in either
    // direction, but this order is not useful.  Since the deq and enq
    // actions are not parallel composable (as CF would imply), we use SB.
    schedule deq SBR enq;
    // clear happens after everything (and can be composed with itself)
    schedule (deq, enq, clear) SBR clear;
    // first must happen before deq or clear, but can be CF with enq
    // because if first is ready then enq will not unready it.
    schedule first SB (deq, clear);
    schedule first CF enq;
    // the user-visible signals have the same relationships as the internal
    schedule notEmpty SB (deq, enq, clear);
    schedule deq SBR notFull;
    schedule notFull SB (enq, clear);
    schedule deq C deq;
    schedule enq C enq;
    path (DEQ, FULL_N);
endmodule: vMkL1FIFOF

// Depth 1, width == 0, loopy
import "BVI" FIFOL10 =
  module vMkL1FIFOF0(VFIFOF0_);
    default_clock clk(CLK, (*unused*)CLK_GATE);
    method enq() enable(ENQ);
    method deq()enable(DEQ);
    method FULL_N   notFull;
    method FULL_N i_notFull;
    method (* reg *)EMPTY_N   notEmpty;
    method (* reg *)EMPTY_N i_notEmpty;
    method clear() enable(CLR);
    // see the schedule comments on vMkL1FIFOF
    schedule i_notEmpty SB (deq, enq, clear);
    schedule deq SBR i_notFull;
    schedule i_notFull SB (enq, clear);
    schedule (i_notEmpty, i_notFull, notEmpty, notFull) CF
               (i_notEmpty, i_notFull, notEmpty, notFull);
    schedule deq SBR enq;
    schedule (deq, enq, clear) SBR clear;
    schedule notEmpty SB (deq, enq, clear);
    schedule deq SBR notFull;
    schedule notFull SB (enq, clear);
    schedule deq C deq;
    schedule enq C enq;
    path (DEQ, FULL_N);
endmodule: vMkL1FIFOF0

// Depth 1, loopy
module mkLFIFOF_ (FIFOF_#(a))
   provisos (Bits#(a, sa)) ;
   FIFOF_#(a) ifc ;
   if (valueOf(sa) == 0)
      begin
	 VFIFOF0_ _f() ;
	 vMkL1FIFOF0 __(_f) ;

	 ifc = (interface FIFOF_;
		   method Action enq(x);
		     _f.enq ;
		   endmethod
		   method deq = _f.deq ;
		   method first = ? ;
		   method notFull = _f.notFull ;
		   method i_notFull = _f.i_notFull ;
		   method notEmpty = _f.notEmpty ;
		   method i_notEmpty() = _f.i_notEmpty ;
		   method clear = _f.clear ;
		endinterface);
      end
   else
      begin
	 FIFOF_#(a) _f();
	 vMkL1FIFOF  __(_f) ;
	 ifc = _f;
      end
   return (ifc) ;
endmodule: mkLFIFOF_

// Depth 2, width > 0, loopy
import "BVI" FIFOL2 =
  module vMk2LFIFOF (FIFOF_#(a))
  provisos (Bits#(a,sa));
    default_clock clk(CLK, (*unused*)CLK_GATE);
    parameter width = valueOf(sa);
    method enq((* reg *)D_IN) enable(ENQ);
    method deq()enable(DEQ);
    method (* reg *)D_OUT first;
    method FULL_N   notFull;
    method FULL_N i_notFull;
    method (* reg *)EMPTY_N   notEmpty;
    method (* reg *)EMPTY_N i_notEmpty;
    method clear() enable(CLR);
    // see the schedule comments on vMkL1FIFOF
    schedule i_notEmpty SB (deq, enq, clear);
    schedule deq SBR i_notFull;
    schedule i_notFull SB (enq, clear);
    schedule (i_notEmpty, i_notFull, notEmpty, notFull, first) CF
               (i_notEmpty, i_notFull, notEmpty, notFull, first);
    schedule deq SBR enq;
    schedule (deq, enq, clear) SBR clear;
    schedule first SB (deq, clear);
    schedule first CF enq;
    schedule notEmpty SB (deq, enq, clear);
    schedule deq SBR notFull;
    schedule notFull SB (enq, clear);
    schedule deq C deq;
    schedule enq C enq;
    path (DEQ, FULL_N);
  endmodule: vMk2LFIFOF

// Depth 2, width == 0, loopy
import "BVI" FIFOL20 =
  module vMk2LFIFOF0 (VFIFOF0_) ;
    default_clock clk(CLK, (*unused*)CLK_GATE);
    method enq() enable(ENQ);
    method deq()enable(DEQ);
    method FULL_N   notFull;
    method FULL_N i_notFull;
    method (* reg *)EMPTY_N   notEmpty;
    method (* reg *)EMPTY_N i_notEmpty;
    method clear() enable(CLR);
    // see the schedule comments on vMkL1FIFOF
    schedule i_notEmpty SB (deq, enq, clear);
    schedule deq SBR i_notFull;
    schedule i_notFull SB (enq, clear);
    schedule (i_notEmpty, i_notFull, notEmpty, notFull) CF
               (i_notEmpty, i_notFull, notEmpty, notFull);
    schedule deq SBR enq;
    schedule (deq, enq, clear) SBR clear;
    schedule notEmpty SB (deq, enq, clear);
    schedule deq SBR notFull;
    schedule notFull SB (enq, clear);
    schedule deq C deq;
    schedule enq C enq;
    path (DEQ, FULL_N);
  endmodule: vMk2LFIFOF0

// Depth 2, loopy
module mkLFIFOF2_(FIFOF_#(a))
   provisos (Bits#(a, sa)) ;
   FIFOF_#(a) ifc ;
   if (valueOf(sa) == 0)
      begin
	 VFIFOF0_ _f() ;
	 vMk2LFIFOF0 __(_f) ;

	 ifc = (interface FIFOF_;
		   method Action enq(x);
		     _f.enq ;
		   endmethod
		   method deq = _f.deq ;
		   method first = ? ;
		   method notFull = _f.notFull ;
		   method i_notFull = _f.i_notFull ;
		   method notEmpty = _f.notEmpty ;
		   method i_notEmpty = _f.i_notEmpty ;
		   method clear = _f.clear ;
		endinterface);
      end
   else
      begin
	 FIFOF_#(a) _f() ;
	 vMk2LFIFOF  __(_f) ;
	 ifc = _f;
      end
   return (ifc) ;
endmodule: mkLFIFOF2_


// Depth n, width > 0, loopy
import "BVI" SizedFIFOL =
  module vMkLSizedNFIFOF#(Integer depth) (FIFOF_#(a))
  provisos (Bits#(a,sa));
    default_clock clk(CLK, (*unused*)CLK_GATE);
    parameter p1width = valueOf(sa);
    parameter p2depth = depth;
    parameter p3cntr_width = log2(depth-1);
    method enq((* reg *)D_IN) enable(ENQ);
    method deq()enable(DEQ);
    method (* reg *)D_OUT first;
    method FULL_N   notFull;
    method FULL_N i_notFull;
    method (* reg *)EMPTY_N   notEmpty;
    method (* reg *)EMPTY_N i_notEmpty;
    method clear() enable(CLR);
    // see the schedule comments on vMkL1FIFOF
    schedule i_notEmpty SB (deq, enq, clear);
    schedule deq SBR i_notFull;
    schedule i_notFull SB (enq, clear);
    schedule (i_notEmpty, i_notFull, notEmpty, notFull, first) CF
               (i_notEmpty, i_notFull, notEmpty, notFull, first);
    schedule deq SBR enq;
    schedule (deq, enq, clear) SBR clear;
    schedule first SB (deq, clear);
    schedule first CF enq;
    schedule notEmpty SB (deq, enq, clear);
    schedule deq SBR notFull;
    schedule notFull SB (enq, clear);
    schedule deq C deq;
    schedule enq C enq;
    path (DEQ, FULL_N);
endmodule: vMkLSizedNFIFOF

// Depth n, depth param, loopy
import "BVI" SizedFIFOL =
  module mkDepthParamLFIFOF_#(UInt#(32) depth) (FIFOF_#(a))
  provisos (Bits#(a,sa));
    default_clock clk(CLK, (*unused*)CLK_GATE);
    parameter p1width = (valueOf(sa) == 0) ? 1 : valueOf(sa);
    parameter p2depth = pack(depth);
    parameter p3cntr_width = pack(getCounterWidth(depth));
    method enq((* reg *)D_IN) enable(ENQ);
    method deq()enable(DEQ);
    method (* reg *)D_OUT first;
    method FULL_N   notFull;
    method FULL_N i_notFull;
    method (* reg *)EMPTY_N   notEmpty;
    method (* reg *)EMPTY_N i_notEmpty;
    method clear() enable(CLR);
    // see the schedule comments on vMkL1FIFOF
    schedule i_notEmpty SB (deq, enq, clear);
    schedule deq SBR i_notFull;
    schedule i_notFull SB (enq, clear);
    schedule (i_notEmpty, i_notFull, notEmpty, notFull, first) CF
               (i_notEmpty, i_notFull, notEmpty, notFull, first);
    schedule deq SBR enq;
    schedule (deq, enq, clear) SBR clear;
    schedule first SB (deq, clear);
    schedule first CF enq;
    schedule notEmpty SB (deq, enq, clear);
    schedule deq SBR notFull;
    schedule notFull SB (enq, clear);
    schedule deq C deq;
    schedule enq C enq;
    path (DEQ, FULL_N);
endmodule: mkDepthParamLFIFOF_

// Depth n, width == 0, loopy
import "BVI" SizedFIFOL0 =
  module vMkLSizedNFIFOF0#(Integer depth) (VFIFOF0_);
    default_clock clk(CLK, (*unused*)CLK_GATE);
    parameter p1depth = depth;
    parameter p2cntr_width = log2(depth+1);
    method enq() enable(ENQ);
    method deq()enable(DEQ);
    method FULL_N   notFull;
    method FULL_N i_notFull;
    method (* reg *)EMPTY_N   notEmpty;
    method (* reg *)EMPTY_N i_notEmpty;
    method clear() enable(CLR);
    // see the schedule comments on vMkL1FIFOF
    schedule i_notEmpty SB (deq, enq, clear);
    schedule deq SBR i_notFull;
    schedule i_notFull SB (enq, clear);
    schedule (i_notEmpty, i_notFull, notEmpty, notFull) CF
               (i_notEmpty, i_notFull, notEmpty, notFull);
    schedule deq SBR enq;
    schedule (deq, enq, clear) SBR clear;
    schedule notEmpty SB (deq, enq, clear);
    schedule deq SBR notFull;
    schedule notFull SB (enq, clear);
    schedule deq C deq;
    schedule enq C enq;
    path (DEQ, FULL_N);
endmodule: vMkLSizedNFIFOF0

// Depth n, loopy
module mkLSizedNFIFOF_#(Integer depth) (FIFOF_#(a))
   provisos (Bits#(a, sa)) ;
   FIFOF_#(a) ifc ;
   if (valueOf(sa) == 0)
      begin
	 VFIFOF0_ _f() ;
	 vMkLSizedNFIFOF0#(depth) __(_f) ;

	 ifc = (interface FIFOF_;
		   method Action enq(x);
		     _f.enq ;
		   endmethod
		   method deq = _f.deq ;
		   method first = ? ;
		   method notFull = _f.notFull ;
		   method i_notFull = _f.i_notFull ;
		   method notEmpty = _f.notEmpty ;
		   method i_notEmpty() = _f.i_notEmpty ;
		   method clear = _f.clear ;
		endinterface);
      end
   else
      begin
	 FIFOF_#(a) _f();
	 vMkLSizedNFIFOF#(depth)  __(_f) ;
	 ifc = _f;
      end
   return (ifc) ;
endmodule: mkLSizedNFIFOF_

function m#(FIFOF_#(a)) mkLSizedFIFOF_(Integer depth)
  provisos (IsModule#(m,c), Bits#(a, sa)) ;
   case (depth)
      0 : return (error("loopy sized fifo created with depth 0!")) ;
      1 : return (mkLFIFOF_) ;
      2 : return (mkLFIFOF2_) ;
      default : if (depth < 0)
                 return (error("loopy sized fifo created with negative depth!"));
                else return (mkLSizedNFIFOF_(depth));
   endcase
endfunction: mkLSizedFIFOF_


endpackage: FIFOF_
