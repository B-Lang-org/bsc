package Probe;

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

export Probe(..);
export mkProbe;

//@ \subsubsection{Probe}
//@
//@ \index{Probe@\te{Probe} (package)|textbf} A \te{Probe} is a
//@ primitive used to ensure that a signal of interest is not optimized
//@ away by the compiler and that it is given a known name.  In terms of
//@ BSV syntax, the \te{Probe} primitive it used just like a register
//@ except that only a write method exists.  Since reads are not
//@ possible, The use of a \te{Probe} has has no effect on scheduling.
//@ In the generated Verilog, the associated signal will be named just
//@ like the port of any Verilog module, in this case
//@ \te{<instance\_name>\$PROBE}.  No actual \te{Probe} instance will be
//@ created however.  The only side effects of a BSV \te{Probe}
//@ instantiation relate to the naming and retention of the associated
//@ signal in the generated Verilog.
//@ \begin{libverbatim}
//@ interface Probe #(type a);
//@     method Action _write(a x1);
//@ endinterface: Probe
//@ \end{libverbatim}

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

interface Probe #(type a);
   method Action _write(a value);
endinterface

module mkProbe(Probe#(a))
   provisos (Bits#(a, sa));
   (* hide *)
   Probe#(a) _r <- vMkProbe;

   return _r;

endmodule

import "BVI" Probe =
   module vMkProbe (Probe#(a))
      provisos (Bits#(a, sa));
      parameter size = valueOf(sa);
      default_clock clk(CLK,(*unused*)CLK_GATE);
      default_reset rst();
      method _write(PROBE) enable(PROBE_VALID);
      schedule _write SBR _write;
   endmodule

endpackage
