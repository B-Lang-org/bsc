package ProbeWire;

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

export ProbeWire(..);
export mkProbeWire;
export keepType;

//@ \subsubsection{ProbeWire}
//@
//@ \index{ProbeWire@\te{ProbeWire} (package)|textbf} A \te{ProbeWire} is a
//@ primitive used to ensure that a signal of interest is not optimized
//@ away by the compiler and that it is given a known name.  In terms of
//@ BSV syntax, the \te{Probe} primitive it used just like a register
//@ except that only a write method exists.
//@ \begin{libverbatim}
//@ interface ProbeWire #(type a);
//@     method Action _write(a x1);
//@ endinterface: Probe
//@ \end{libverbatim}

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

interface ProbeWire#(type a);
  method a id(a x);
endinterface	

module mkProbeWire(ProbeWire#(a))
   provisos (Bits#(a, sa));
   (* hide *)
   ProbeWire#(a) _r <- vMkProbeWire;

   return _r;

endmodule

import "BVI" ProbeWire =
  module vMkProbeWire (ProbeWire#(a))
     provisos (Bits#(a, sa));
     parameter size = valueOf(sa);
     default_clock clk();
     default_reset rst();
     method OUT id(IN);
     schedule id C id;
  endmodule

function a keepType(a x) provisos(Bits#(a,sa));
  let c = clockOf(x);	
  let r = noReset;
  let f = primBuildModule(primGetName(x),c,r,mkProbeWire());
  return (f.id(x));
endfunction

endpackage

