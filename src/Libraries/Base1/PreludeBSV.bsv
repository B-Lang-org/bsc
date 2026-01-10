package PreludeBSV;

import Prelude::*;

//import Connectable::*;

// Export interfaces
export RWire(..);
export Wire;
export PulseWire(..);
export ReadOnly(..);
export WriteOnly(..);
// this is needed by the Clocks library, so we unfortunately expose it
export VWire(..);
// this is needed by UTMI's Clockery library
export VRWire(..);

// Export modules
export mkRWire;
export mkRWireSBR;
export mkWire;
export mkBypassWire;
export mkDWire;
export mkPulseWire;
export mkPulseWireOR;

export mkUnsafeRWire;
export mkUnsafeRWireSBR;
export mkUnsafeWire;
export mkUnsafeBypassWire;
export mkUnsafeDWire;
export mkUnsafePulseWire;
export mkUnsafePulseWireOR;

export mkCReg;
export mkCRegU;
export mkCRegA;

// Export functions
export when;
export regToReadOnly;
export pulseWireToReadOnly;
export readReadOnly;
export parity;
export truncateLSB;
export gcd, lcm;

// Export typeclasses
export Alias, NumAlias;

// Export Saturating Arith
export SaturationMode(..), SaturatingArith(..);

// =========================

//@ \subsubsection{RWire}
//@
//@ \index{RWire@\te{RWire} (package)|textbf}
//@ An \te{RWire} is a primitive stateless module, whose purpose is to allow
//@ data transfer between methods or between a method and a rule without
//@ the latency of a clock cycle (i.e., within a single clock).
//@
//@ The \te{RWire} interface is conceptually similar to a register's interface,
//@ but the output value is wrapped in a \te{Maybe} type.  The output is
//@ only \te{Valid} if a write has a occurred in the same clock
//@ cycle, otherwise the output is \te{Invalid}.
//@
//@ The \te{RWire} primitive implementation is only wires, so it is possible to
//@ create a combinational cycle by having a cycle of RWires (but this will be
//@ flagged by the compiler).
//@ Examples of RWire use can be found in the {\em Style Guide.}
//@
//@ # 4
interface RWire#(type a) ;
   method Action wset(a datain) ;
   method Maybe#(a) wget() ;
endinterface: RWire

interface VRWire#(type a) ;
   method Action wset(a x1);
   method a wget() ;
   method Bool whas() ;
endinterface: VRWire

interface VRWireN#(numeric type n);
  method PrimAction wset(Bit#(n) datain);
  method Bit#(n) wget();
  method Bit#(1) whas();
endinterface

// for addCFWire desugaring
// This uses prim types like something coming from genwrap.
module vMkRWire1(VRWireN#(1));

   (* hide *)
   VRWire#(Bit#(1)) _rw <- vMkRWire;
   function rw_wset(v);
      return toPrimAction(_rw.wset(v));
   endfunction
   method wset = primMethod(Cons("v", Nil), rw_wset);
   method wget = primMethod(Nil, _rw.wget);
   method whas = primMethod(Nil, pack(_rw.whas));

endmodule

interface VRWire0;
   method Action wset;
   method Bool whas;
endinterface: VRWire0

import "BVI" RWire =
   module vMkRWire (VRWire#(a))
      provisos (Bits#(a,sa));
      parameter width = valueOf(sa);
      default_clock clk();
      // reset is needed, to guarantee that the source and destination
      // are on the same reset -- if the source has no reset, use
      // "reset_by noReset" on the instantiation
      default_reset rst();
      method wset(WVAL) enable(WSET);
      method WHAS whas ;
      method WGET wget ;
      schedule (wget, whas) CF (wget, whas) ;
      schedule wset SBR (wget, whas) ;
      schedule wset C wset ;
      path (WSET, WHAS) ;
      path (WVAL, WGET) ;
   endmodule: vMkRWire

import "BVI" RWire0 =
   module vMkRWire0 (VRWire0);
      default_clock clk();
      // reset is needed, to guarantee that the source and destination
      // are on the same reset -- if the source has no reset, use
      // "reset_by noReset" on the instantiation
      default_reset rst();
      method wset() enable(WSET) ;
      method WHAS whas ;
      schedule whas CF whas ;
      schedule wset SBR whas ;
      schedule wset C wset ;
      path (WSET, WHAS) ;
   endmodule: vMkRWire0

import "BVI" RWire =
   module vMkRWireSBR (VRWire#(a))
      provisos (Bits#(a,sa));
      parameter width = valueOf(sa);
      default_clock clk();
      // reset is needed, to guarantee that the source and destination
      // are on the same reset -- if the source has no reset, use
      // "reset_by noReset" on the instantiation
      default_reset rst();
      method wset(WVAL) enable(WSET);
      method WHAS whas ;
      method WGET wget ;
      schedule (wget, whas) CF (wget, whas) ;
      schedule wset SBR (wget, whas) ;
      schedule wset SBR wset ;
      path (WSET, WHAS) ;
      path (WVAL, WGET) ;
   endmodule: vMkRWireSBR

import "BVI" RWire0 =
   module vMkRWire0SBR (VRWire0);
      default_clock clk();
      // reset is needed, to guarantee that the source and destination
      // are on the same reset -- if the source has no reset, use
      // "reset_by noReset" on the instantiation
      default_reset rst();
      method wset() enable(WSET) ;
      method WHAS whas ;
      schedule whas CF whas ;
      schedule wset SBR whas ;
      schedule wset SBR wset ;
      path (WSET, WHAS) ;
   endmodule: vMkRWire0SBR


//@ # 2
module mkRWire (RWire#(a))
   provisos (Bits #(a, sa)) ;
   RWire#(a) ifc;
   if (valueOf(sa) == 0)
      begin
         (* hide *)
         VRWire0 _r <- vMkRWire0;

         ifc = (interface RWire;
                   method wget() ;
                      return (_r.whas ? (tagged Valid (unpack(0))) : tagged Invalid);
                   endmethod: wget

                   method Action wset(x);
                      _r.wset;
                   endmethod
                endinterface);
      end
   else
      begin
         (* hide *)
         VRWire#(a) _r <-  vMkRWire;

         ifc = (interface RWire;
                   method wget() ;
                      return (_r.whas? (tagged Valid (_r.wget)) : tagged Invalid);
                   endmethod: wget

                   method Action wset(x);
                      _r.wset(x);
                   endmethod
                endinterface);
      end
   return (ifc);
endmodule: mkRWire

module mkRWireSBR (RWire#(a))
   provisos (Bits #(a, sa)) ;
   RWire#(a) ifc;
   if (valueOf(sa) == 0)
      begin
         (* hide *)
         VRWire0 _r <- vMkRWire0SBR;

         ifc = (interface RWire;
                   method wget() ;
                      return (_r.whas ? (tagged Valid (unpack(0))) : tagged Invalid);
                   endmethod: wget

                   method Action wset(x);
                      _r.wset;
                   endmethod
                endinterface);
      end
   else
      begin
         (* hide *)
         VRWire#(a) _r <-  vMkRWireSBR;

         ifc = (interface RWire;
                   method wget() ;
                      return (_r.whas? (tagged Valid (_r.wget)) : tagged Invalid);
                   endmethod: wget

                   method Action wset(x);
                      _r.wset(x);
                   endmethod
                endinterface);
      end
   return (ifc);
endmodule: mkRWireSBR

// ====

/*
instance Connectable#(RWire#(a), RWire#(a));
   module mkConnection#(RWire#(a) w1, RWire#(a) w2)(Empty);
      rule connect_rwires_lr (isValid(w1.wget));
         w2.wset(validValue(w1.wget));
      endrule
      rule connect_rwires_rl (isValid(w2.wget));
         w1.wset(validValue(w2.wget));
      endrule
   endmodule
endinstance
*/

//@ \index{Wire@\te{Wire} (interface)|textbf}
//@ \index{mkWire@\te{mkWire} (module)|textbf}
//@ The Wire interface and module are simular to RWire, but the valid
//@ bit is hidden from the user and the validity is automatically
//@ checked in an implicit condition.  The Wire interface works like
//@ the Reg interface, so mentioning the name of the wire gets at its
//@ contents whenever they're valid, and using \texttt{<=} writes the wire.

typedef Reg#(data_t) Wire#(type data_t);

//@ # 1
module mkWire(Wire#(data_t)) provisos (Bits#(data_t, data_t_size));
   (* hide *)
   RWire#(data_t) _wire <- mkRWire;
   method data_t _read() if (_wire.wget() matches (tagged Valid .value));
      return value;
   endmethod: _read
   method Action _write(data_t new_value);
      _wire.wset(new_value);
   endmethod: _write
endmodule: mkWire

interface VWire#(type a) ;
   method Action wset(a x1);
   method a wget() ;
endinterface: VWire

interface VWire0;
   method Action wset();
endinterface: VWire0

import "BVI" BypassWire =
   module vMkBypassWire (VWire#(a))
      provisos (Bits#(a,sa));
      parameter width = valueOf(sa);
      default_clock clk();
      // reset is needed, to guarantee that the source and destination
      // are on the same reset -- if the source has no reset, use
      // "reset_by noReset" on the instantiation
      default_reset rst();
      method wset(WVAL) enable((*inhigh*)WSET);
      method WGET wget ;
      schedule wset SBR (wget) ;
      schedule wset C  wset ;
      schedule wget CF wget ;
      path (WVAL, WGET) ;
   endmodule: vMkBypassWire

import "BVI" BypassWire0 =
   module vMkBypassWire0 (VWire0);
      default_clock clk();
      // reset is needed, to guarantee that the source and destination
      // are on the same reset -- if the source has no reset, use
      // "reset_by noReset" on the instantiation
      default_reset rst();
      method wset() enable((*inhigh*)WSET);
      schedule wset C  wset ;
   endmodule: vMkBypassWire0

//@ \index{mkBypassWire@\te{mkBypassWire} (module)|textbf}
//@ BypassWire is an implementation of the Wire interface where
//@ the _write method is an always_enabled method. The compiler
//@ will issue a warning if the method does not appear to be called
//@ every clock cycle. The advantage of this tradeoff is that
//@ the _read method of this interface does not carry any implicit
//@ condition (so it can satisfy a "no_implicit_conditions" assertion
//@ or an always_ready method).
module mkBypassWire(Wire#(data_t)) provisos (Bits#(data_t, data_t_size));
   // using VWire is an ugly hack to work around
   // the _read desugaring
   VWire#(data_t) ifc;
   if (valueOf(data_t_size) == 0)
      begin
         (* hide *)
         VWire0 _r <- vMkBypassWire0;

         ifc = (interface VWire
                   method Action wset(x);
                     _r.wset;
                   endmethod
                   method wget = unpack(0);
                endinterface);
      end
   else
      begin
         (* hide *)
         VWire#(data_t) _r <- vMkBypassWire;


         ifc = _r;
      end

   method _write = ifc.wset;
   method _read  = ifc.wget;

endmodule: mkBypassWire

module mkDWire#(data_t dflt) (Wire#(data_t))
   provisos (Bits#(data_t, data_t_size));

   (* hide *)
   RWire#(data_t) _wire <- mkRWire();

   method data_t _read();
      if (_wire.wget() matches (tagged Valid .value))
         return value;
      else
         return dflt;
   endmethod
   method Action _write(data_t new_value);
      _wire.wset(new_value);
   endmethod

endmodule

//@ \index{PulseWire@\te{PulseWire} (interface)|textbf}
//@ \index{mkPulseWire@\te{mkPulseWire} (module)|textbf}
//@ The PulseWire interface and module can be used within rules and
//@ actions methods to signal other methods or rules in the same clock
//@ cycle.
//@
//@  # 4
interface PulseWire;
  method Action send();
  method Bool _read();
endinterface

//@ # 1
module mkPulseWire(PulseWire);

   (* hide *)
   VRWire0 _rw <- vMkRWire0;

   method send  = _rw.wset;
   method _read = _rw.whas ;

endmodule


module mkPulseWireOR(PulseWire);

   (* hide *)
   VRWire0 _rw <- vMkRWire0SBR;

   method send  = _rw.wset;
   method _read = _rw.whas ;

endmodule

// =======

// for addCFWire desugaring
module vMkUnsafeRWire1(VRWireN#(1));

   (* hide *)
   VRWire#(Bit#(1)) _rw <- vMkUnsafeRWire;
   method wset(v);
      return(toPrimAction(_rw.wset(v)));
   endmethod
   method wget = _rw.wget;
   method whas = pack(_rw.whas);

endmodule

import "BVI" RWire =
   module vMkUnsafeRWire (VRWire#(a))
      provisos (Bits#(a,sa));
      parameter width = valueOf(sa);
      default_clock clk();
      // reset is needed, to guarantee that the source and destination
      // are on the same reset -- if the source has no reset, use
      // "reset_by noReset" on the instantiation
      default_reset rst();
      method wset(WVAL) enable(WSET);
      method WHAS whas ;
      method WGET wget ;
      schedule (wget, whas) CF (wget, whas) ;
      schedule wset SB (wget, whas) ;
      schedule wset C wset ;
      path (WSET, WHAS) ;
      path (WVAL, WGET) ;
   endmodule: vMkUnsafeRWire

import "BVI" RWire0 =
   module vMkUnsafeRWire0 (VRWire0);
      default_clock clk();
      // reset is needed, to guarantee that the source and destination
      // are on the same reset -- if the source has no reset, use
      // "reset_by noReset" on the instantiation
      default_reset rst();
      method wset() enable(WSET) ;
      method WHAS whas ;
      schedule whas CF whas ;
      schedule wset SB whas ;
      schedule wset C wset ;
      path (WSET, WHAS) ;
   endmodule: vMkUnsafeRWire0

import "BVI" RWire =
   module vMkUnsafeRWireSBR (VRWire#(a))
      provisos (Bits#(a,sa));
      parameter width = valueOf(sa);
      default_clock clk();
      // reset is needed, to guarantee that the source and destination
      // are on the same reset -- if the source has no reset, use
      // "reset_by noReset" on the instantiation
      default_reset rst();
      method wset(WVAL) enable(WSET);
      method WHAS whas ;
      method WGET wget ;
      schedule (wget, whas) CF (wget, whas) ;
      schedule wset SB (wget, whas) ;
      schedule wset SBR wset ;
      path (WSET, WHAS) ;
      path (WVAL, WGET) ;
   endmodule: vMkUnsafeRWireSBR

import "BVI" RWire0 =
   module vMkUnsafeRWire0SBR (VRWire0);
      default_clock clk();
      // reset is needed, to guarantee that the source and destination
      // are on the same reset -- if the source has no reset, use
      // "reset_by noReset" on the instantiation
      default_reset rst();
      method wset() enable(WSET) ;
      method WHAS whas ;
      schedule whas CF whas ;
      schedule wset SB whas ;
      schedule wset SBR wset ;
      path (WSET, WHAS) ;
   endmodule: vMkUnsafeRWire0SBR


//@ # 2
module mkUnsafeRWire (RWire#(a))
   provisos (Bits #(a, sa)) ;
   RWire#(a) ifc;
   if (valueOf(sa) == 0)
      begin
         (* hide *)
         VRWire0 _r <- vMkUnsafeRWire0;

         ifc = (interface RWire;
                   method wget() ;
                      return (_r.whas ? (tagged Valid (unpack(0))) : tagged Invalid);
                   endmethod: wget

                   method Action wset(x);
                      _r.wset;
                   endmethod
                endinterface);
      end
   else
      begin
         (* hide *)
         VRWire#(a) _r <-  vMkUnsafeRWire;

         ifc = (interface RWire;
                   method wget() ;
                      return (_r.whas? (tagged Valid (_r.wget)) : tagged Invalid);
                   endmethod: wget

                   method Action wset(x);
                      _r.wset(x);
                   endmethod
                endinterface);
      end
   return (ifc);
endmodule: mkUnsafeRWire

module mkUnsafeRWireSBR (RWire#(a))
   provisos (Bits #(a, sa)) ;
   RWire#(a) ifc;
   if (valueOf(sa) == 0)
      begin
         (* hide *)
         VRWire0 _r <- vMkUnsafeRWire0SBR;

         ifc = (interface RWire;
                   method wget() ;
                      return (_r.whas ? (tagged Valid (unpack(0))) : tagged Invalid);
                   endmethod: wget

                   method Action wset(x);
                      _r.wset;
                   endmethod
                endinterface);
      end
   else
      begin
         (* hide *)
         VRWire#(a) _r <-  vMkUnsafeRWireSBR;

         ifc = (interface RWire;
                   method wget() ;
                      return (_r.whas? (tagged Valid (_r.wget)) : tagged Invalid);
                   endmethod: wget

                   method Action wset(x);
                      _r.wset(x);
                   endmethod
                endinterface);
      end
   return (ifc);
endmodule: mkUnsafeRWireSBR

// ====

/*
instance Connectable#(RWire#(a), RWire#(a));
   module mkUnsafeConnection#(RWire#(a) w1, RWire#(a) w2)(Empty);
      rule connect_rwires_lr (isValid(w1.wget));
         w2.wset(validValue(w1.wget));
      endrule
      rule connect_rwires_rl (isValid(w2.wget));
         w1.wset(validValue(w2.wget));
      endrule
   endmodule
endinstance
*/

//@ \index{Wire@\te{Wire} (interface)|textbf}
//@ \index{mkUnsafeWire@\te{mkUnsafeWire} (module)|textbf}
//@ The Wire interface and module are simular to RWire, but the valid
//@ bit is hidden from the user and the validity is automatically
//@ checked in an implicit condition.  The Wire interface works like
//@ the Reg interface, so mentioning the name of the wire gets at its
//@ contents whenever they're valid, and using \texttt{<=} writes the wire.

//@ # 1
module mkUnsafeWire(Wire#(data_t)) provisos (Bits#(data_t, data_t_size));
   (* hide *)
   RWire#(data_t) _wire <- mkUnsafeRWire;
   method data_t _read() if (_wire.wget() matches (tagged Valid .value));
      return value;
   endmethod: _read
   method Action _write(data_t new_value);
      _wire.wset(new_value);
   endmethod: _write
endmodule: mkUnsafeWire

import "BVI" BypassWire =
   module vMkUnsafeBypassWire (VWire#(a))
      provisos (Bits#(a,sa));
      parameter width = valueOf(sa);
      default_clock clk();
      // reset is needed, to guarantee that the source and destination
      // are on the same reset -- if the source has no reset, use
      // "reset_by noReset" on the instantiation
      default_reset rst();
      method wset(WVAL) enable((*inhigh*)WSET);
      method WGET wget ;
      schedule wset SB (wget) ;
      schedule wset C  wset ;
      schedule wget CF wget ;
      path (WVAL, WGET) ;
   endmodule: vMkUnsafeBypassWire

//@ \index{mkUnsafeBypassWire@\te{mkUnsafeBypassWire} (module)|textbf}
//@ BypassWire is an implementation of the Wire interface where
//@ the _write method is an always_enabled method. The compiler
//@ will issue a warning if the method does not appear to be called
//@ every clock cycle. The advantage of this tradeoff is that
//@ the _read method of this interface does not carry any implicit
//@ condition (so it can satisfy a "no_implicit_conditions" assertion
//@ or an always_ready method).
module mkUnsafeBypassWire(Wire#(data_t)) provisos (Bits#(data_t, data_t_size));
   // using VWire is an ugly hack to work around
   // the _read desugaring
   VWire#(data_t) ifc;
   if (valueOf(data_t_size) == 0)
      begin
         (* hide *)
         VWire0 _r <- vMkBypassWire0;

         ifc = (interface VWire
                   method Action wset(x);
                     _r.wset;
                   endmethod
                   method wget = unpack(0);
                endinterface);
      end
   else
      begin
         (* hide *)
         VWire#(data_t) _r <- vMkUnsafeBypassWire;


         ifc = _r;
      end

   method _write = ifc.wset;
   method _read  = ifc.wget;

endmodule: mkUnsafeBypassWire

module mkUnsafeDWire#(data_t dflt) (Wire#(data_t))
   provisos (Bits#(data_t, data_t_size));

   (* hide *)
   RWire#(data_t) _wire <- mkUnsafeRWire();

   method data_t _read();
      if (_wire.wget() matches (tagged Valid .value))
         return value;
      else
         return dflt;
   endmethod
   method Action _write(data_t new_value);
      _wire.wset(new_value);
   endmethod

endmodule

//@ # 1
module mkUnsafePulseWire(PulseWire);

   (* hide *)
   VRWire0 _rw <- vMkUnsafeRWire0;

   method send  = _rw.wset;
   method _read = _rw.whas ;

endmodule


module mkUnsafePulseWireOR(PulseWire);

   (* hide *)
   VRWire0 _rw <- vMkUnsafeRWire0SBR;

   method send  = _rw.wset;
   method _read = _rw.whas ;

endmodule

// =========================

interface CReg5 #(type t);
   interface Reg#(t) port0;
   interface Reg#(t) port1;
   interface Reg#(t) port2;
   interface Reg#(t) port3;
   interface Reg#(t) port4;
endinterface

import "BVI" CRegN5 =
   module vMkCReg5#(parameter a init) (CReg5#(a))
      provisos (Bits#(a,sa));

      parameter width = valueOf(sa);
      parameter init  = pack(init);

      default_clock   clk(CLK, (*unused*)CLK_GATE);
      default_reset rst(RST);

      interface Reg port0;
         method Q_OUT_0 _read();
         method         _write(D_IN_0) enable(EN_0);
      endinterface
      interface Reg port1;
         method Q_OUT_1 _read();
         method         _write(D_IN_1) enable(EN_1);
      endinterface
      interface Reg port2;
         method Q_OUT_2 _read();
         method         _write(D_IN_2) enable(EN_2);
      endinterface
      interface Reg port3;
         method Q_OUT_3 _read();
         method         _write(D_IN_3) enable(EN_3);
      endinterface
      interface Reg port4;
         method Q_OUT_4 _read();
         method         _write(D_IN_4) enable(EN_4);
      endinterface

      schedule port0._read  CF  port0._read;
      schedule port1._read  CF  port1._read;
      schedule port2._read  CF  port2._read;
      schedule port3._read  CF  port3._read;
      schedule port4._read  CF  port4._read;

      schedule port0._write SBR port0._write;
      schedule port1._write SBR port1._write;
      schedule port2._write SBR port2._write;
      schedule port3._write SBR port3._write;
      schedule port4._write SBR port4._write;

      schedule port0._read  SB  port0._write;
      schedule port1._read  SB  port1._write;
      schedule port2._read  SB  port2._write;
      schedule port3._read  SB  port3._write;
      schedule port4._read  SB  port4._write;

      schedule port0._read  SBR (port1._read, port1._write,
                                 port2._read, port2._write,
                                 port3._read, port3._write,
                                 port4._read, port4._write);
      schedule port0._write SBR (port1._read, port1._write,
                                 port2._read, port2._write,
                                 port3._read, port3._write,
                                 port4._read, port4._write);
      schedule port1._read  SBR (port2._read, port2._write,
                                 port3._read, port3._write,
                                 port4._read, port4._write);
      schedule port1._write SBR (port2._read, port2._write,
                                 port3._read, port3._write,
                                 port4._read, port4._write);
      schedule port2._read  SBR (port3._read, port3._write,
                                 port4._read, port4._write);
      schedule port2._write SBR (port3._read, port3._write,
                                 port4._read, port4._write);
      schedule port3._read  SBR (port4._read, port4._write);
      schedule port3._write SBR (port4._read, port4._write);

      path (EN_0, Q_OUT_1);
      path (D_IN_0, Q_OUT_1);
      path (EN_0, Q_OUT_2);
      path (D_IN_0, Q_OUT_2);
      path (EN_0, Q_OUT_3);
      path (D_IN_0, Q_OUT_3);
      path (EN_0, Q_OUT_4);
      path (D_IN_0, Q_OUT_4);

      path (EN_1, Q_OUT_2);
      path (D_IN_1, Q_OUT_2);
      path (EN_1, Q_OUT_3);
      path (D_IN_1, Q_OUT_3);
      path (EN_1, Q_OUT_4);
      path (D_IN_1, Q_OUT_4);

      path (EN_2, Q_OUT_3);
      path (D_IN_2, Q_OUT_3);
      path (EN_2, Q_OUT_4);
      path (D_IN_2, Q_OUT_4);

      path (EN_3, Q_OUT_4);
      path (D_IN_3, Q_OUT_4);

   endmodule: vMkCReg5

import "BVI" CRegUN5 =
   module vMkCRegU5 (CReg5#(a))
      provisos (Bits#(a,sa));

      parameter width = valueOf(sa);

      default_clock   clk(CLK, (*unused*)CLK_GATE);
      default_reset rst(RST);

      interface Reg port0;
         method Q_OUT_0 _read();
         method         _write(D_IN_0) enable(EN_0);
      endinterface
      interface Reg port1;
         method Q_OUT_1 _read();
         method         _write(D_IN_1) enable(EN_1);
      endinterface
      interface Reg port2;
         method Q_OUT_2 _read();
         method         _write(D_IN_2) enable(EN_2);
      endinterface
      interface Reg port3;
         method Q_OUT_3 _read();
         method         _write(D_IN_3) enable(EN_3);
      endinterface
      interface Reg port4;
         method Q_OUT_4 _read();
         method         _write(D_IN_4) enable(EN_4);
      endinterface

      schedule port0._read  CF  port0._read;
      schedule port1._read  CF  port1._read;
      schedule port2._read  CF  port2._read;
      schedule port3._read  CF  port3._read;
      schedule port4._read  CF  port4._read;

      schedule port0._write SBR port0._write;
      schedule port1._write SBR port1._write;
      schedule port2._write SBR port2._write;
      schedule port3._write SBR port3._write;
      schedule port4._write SBR port4._write;

      schedule port0._read  SB  port0._write;
      schedule port1._read  SB  port1._write;
      schedule port2._read  SB  port2._write;
      schedule port3._read  SB  port3._write;
      schedule port4._read  SB  port4._write;

      schedule port0._read  SBR (port1._read, port1._write,
                                 port2._read, port2._write,
                                 port3._read, port3._write,
                                 port4._read, port4._write);
      schedule port0._write SBR (port1._read, port1._write,
                                 port2._read, port2._write,
                                 port3._read, port3._write,
                                 port4._read, port4._write);
      schedule port1._read  SBR (port2._read, port2._write,
                                 port3._read, port3._write,
                                 port4._read, port4._write);
      schedule port1._write SBR (port2._read, port2._write,
                                 port3._read, port3._write,
                                 port4._read, port4._write);
      schedule port2._read  SBR (port3._read, port3._write,
                                 port4._read, port4._write);
      schedule port2._write SBR (port3._read, port3._write,
                                 port4._read, port4._write);
      schedule port3._read  SBR (port4._read, port4._write);
      schedule port3._write SBR (port4._read, port4._write);

      path (EN_0, Q_OUT_1);
      path (D_IN_0, Q_OUT_1);
      path (EN_0, Q_OUT_2);
      path (D_IN_0, Q_OUT_2);
      path (EN_0, Q_OUT_3);
      path (D_IN_0, Q_OUT_3);
      path (EN_0, Q_OUT_4);
      path (D_IN_0, Q_OUT_4);

      path (EN_1, Q_OUT_2);
      path (D_IN_1, Q_OUT_2);
      path (EN_1, Q_OUT_3);
      path (D_IN_1, Q_OUT_3);
      path (EN_1, Q_OUT_4);
      path (D_IN_1, Q_OUT_4);

      path (EN_2, Q_OUT_3);
      path (D_IN_2, Q_OUT_3);
      path (EN_2, Q_OUT_4);
      path (D_IN_2, Q_OUT_4);

      path (EN_3, Q_OUT_4);
      path (D_IN_3, Q_OUT_4);

   endmodule: vMkCRegU5

import "BVI" CRegA5 =
   module vMkCRegA5#(parameter a init) (CReg5#(a))
      provisos (Bits#(a,sa));

      parameter width = valueOf(sa);
      parameter init  = pack(init);

      default_clock   clk(CLK, (*unused*)CLK_GATE);
      default_reset rst(RST);

      interface Reg port0;
         method Q_OUT_0 _read();
         method         _write(D_IN_0) enable(EN_0);
      endinterface
      interface Reg port1;
         method Q_OUT_1 _read();
         method         _write(D_IN_1) enable(EN_1);
      endinterface
      interface Reg port2;
         method Q_OUT_2 _read();
         method         _write(D_IN_2) enable(EN_2);
      endinterface
      interface Reg port3;
         method Q_OUT_3 _read();
         method         _write(D_IN_3) enable(EN_3);
      endinterface
      interface Reg port4;
         method Q_OUT_4 _read();
         method         _write(D_IN_4) enable(EN_4);
      endinterface

      schedule port0._read  CF  port0._read;
      schedule port1._read  CF  port1._read;
      schedule port2._read  CF  port2._read;
      schedule port3._read  CF  port3._read;
      schedule port4._read  CF  port4._read;

      schedule port0._write SBR port0._write;
      schedule port1._write SBR port1._write;
      schedule port2._write SBR port2._write;
      schedule port3._write SBR port3._write;
      schedule port4._write SBR port4._write;

      schedule port0._read  SB  port0._write;
      schedule port1._read  SB  port1._write;
      schedule port2._read  SB  port2._write;
      schedule port3._read  SB  port3._write;
      schedule port4._read  SB  port4._write;

      schedule port0._read  SBR (port1._read, port1._write,
                                 port2._read, port2._write,
                                 port3._read, port3._write,
                                 port4._read, port4._write);
      schedule port0._write SBR (port1._read, port1._write,
                                 port2._read, port2._write,
                                 port3._read, port3._write,
                                 port4._read, port4._write);
      schedule port1._read  SBR (port2._read, port2._write,
                                 port3._read, port3._write,
                                 port4._read, port4._write);
      schedule port1._write SBR (port2._read, port2._write,
                                 port3._read, port3._write,
                                 port4._read, port4._write);
      schedule port2._read  SBR (port3._read, port3._write,
                                 port4._read, port4._write);
      schedule port2._write SBR (port3._read, port3._write,
                                 port4._read, port4._write);
      schedule port3._read  SBR (port4._read, port4._write);
      schedule port3._write SBR (port4._read, port4._write);

      path (EN_0, Q_OUT_1);
      path (D_IN_0, Q_OUT_1);
      path (EN_0, Q_OUT_2);
      path (D_IN_0, Q_OUT_2);
      path (EN_0, Q_OUT_3);
      path (D_IN_0, Q_OUT_3);
      path (EN_0, Q_OUT_4);
      path (D_IN_0, Q_OUT_4);

      path (EN_1, Q_OUT_2);
      path (D_IN_1, Q_OUT_2);
      path (EN_1, Q_OUT_3);
      path (D_IN_1, Q_OUT_3);
      path (EN_1, Q_OUT_4);
      path (D_IN_1, Q_OUT_4);

      path (EN_2, Q_OUT_3);
      path (D_IN_2, Q_OUT_3);
      path (EN_2, Q_OUT_4);
      path (D_IN_2, Q_OUT_4);

      path (EN_3, Q_OUT_4);
      path (D_IN_3, Q_OUT_4);

   endmodule: vMkCRegA5

module mkCReg#(parameter Integer n, parameter a_type init)(Reg#(a_type) ifc[])
   provisos (Bits#(a_type, sizea));

   if (n>5) error(quote("mkCReg") + " cannot have more than five ports");
   if (n<0) error(quote("mkCReg") + " cannot have a negative number of ports");

   CReg5#(a_type) _ifc = ?;
   if (valueOf(sizea) > 0)
      (* hide *) _ifc <- vMkCReg5(init);

   Reg#(a_type) v[n];
   if (n>0) v[0] = _ifc.port0;
   if (n>1) v[1] = _ifc.port1;
   if (n>2) v[2] = _ifc.port2;
   if (n>3) v[3] = _ifc.port3;
   if (n>4) v[4] = _ifc.port4;
   return v;
endmodule

module mkCRegU#(parameter Integer n)(Reg#(a_type) ifc[])
   provisos (Bits#(a_type, sizea));

   if (n>5) error(quote("mkCRegU") + " cannot have more than five ports");
   if (n<0) error(quote("mkCRegU") + " cannot have a negative number of ports");

   CReg5#(a_type) _ifc = ?;
   if (valueOf(sizea) > 0)
      (* hide *) _ifc <- vMkCRegU5;

   Reg#(a_type) v[n];
   if (n>0) v[0] = _ifc.port0;
   if (n>1) v[1] = _ifc.port1;
   if (n>2) v[2] = _ifc.port2;
   if (n>3) v[3] = _ifc.port3;
   if (n>4) v[4] = _ifc.port4;
   return v;
endmodule

module mkCRegA#(parameter Integer n, parameter a_type init)(Reg#(a_type) ifc[])
   provisos (Bits#(a_type, sizea));

   if (n>5) error(quote("mkCRegA") + " cannot have more than five ports");
   if (n<0) error(quote("mkCRegA") + " cannot have a negative number of ports");

   CReg5#(a_type) _ifc = ?;
   if (valueOf(sizea) > 0)
      (* hide *) _ifc <- vMkCRegA5(init);

   Reg#(a_type) v[n];
   if (n>0) v[0] = _ifc.port0;
   if (n>1) v[1] = _ifc.port1;
   if (n>2) v[2] = _ifc.port2;
   if (n>3) v[3] = _ifc.port3;
   if (n>4) v[4] = _ifc.port4;
   return v;
endmodule

// =========================

function a when(Bool p, a arg);
  return(_when_(p, arg));
endfunction

interface ReadOnly #( type a_type ) ;
   method a_type _read() ;
endinterface

function ReadOnly#(a) regToReadOnly(Reg#(a) ifc);
   return (interface ReadOnly
              method _read = ifc._read;
           endinterface);
endfunction

function ReadOnly#(Bool) pulseWireToReadOnly(PulseWire ifc);
   return (interface ReadOnly
              method _read = ifc._read;
           endinterface);
endfunction

function a readReadOnly(ReadOnly#(a) r);
   return r;
endfunction

interface WriteOnly #( type a_type ) ;
   method Action _write (a_type x) ;
endinterface

//Get parity
function Bit#(1) parity(Bit#(n) v);
   return (^ v);
endfunction

//reverse truncate
function Bit#(n) truncateLSB(Bit#(m) x)
   provisos(Add#(n,k,m));
   match {.r,.s} = split(x);
   return r;
endfunction

// greatest common divisor
function Integer gcd(Integer a, Integer b);
   if (b == 0)
      return a;
   else
      return gcd(b, rem(a,b));
endfunction: gcd

// least common multiple
function Integer lcm(Integer a, Integer b);
   if (a == 0 || b == 0)
      return 0;
   else
      return abs(quot(a,gcd(a,b))*b);
endfunction: lcm

// =========================

// Alias, NumAlias and StrAlias

typeclass Alias#(type a, type b)
   dependencies (a determines b,
                 b determines a);
endtypeclass

instance Alias#(a,a);
endinstance

typeclass NumAlias#(numeric type a, numeric type b)
   dependencies (a determines b,
                 b determines a);
endtypeclass

instance NumAlias#(a,a);
endinstance

typeclass StrAlias#(string type a, string type b)
   dependencies (a determines b,
                 b determines a);
endtypeclass

instance StrAlias#(a,a);
endinstance

// =========================

// Saturation Modes
typedef enum {
              Sat_Wrap             // ignore overflow and underflow, just wrap around
              ,Sat_Bound           // on overflow or underflow set to maxBound or minBound
              ,Sat_Zero            // on overflow or underflow set to 0
              ,Sat_Symmetric       // on overflow or underflow set to maxBound or (minBound+1)
   } SaturationMode
deriving (Bits, Eq);

typeclass SaturatingArith#( type t);
   function t satPlus (SaturationMode mode, t x, t y);
   function t satMinus (SaturationMode mode, t x, t y);
   function t boundedPlus  (t x, t y) = satPlus (Sat_Bound, x, y);
   function t boundedMinus (t x, t y) = satMinus(Sat_Bound, x, y);
endtypeclass

instance SaturatingArith#(Int#(n));
   function Int#(n) satPlus (SaturationMode smode, Int#(n) x, Int#(n) y);
      let sum = x + y;
      let overflow  = msb(x) == 0 && msb(y) == 0 && msb(sum) == 1;
      let underflow = msb(x) == 1 && msb(y) == 1 && msb(sum) == 0;
      let isMinBound = sum == minBound;
      sum = case (smode)
               Sat_Wrap:        return sum;
               Sat_Bound:       return overflow ? maxBound : (underflow ? minBound : sum);
               Sat_Zero:        return (overflow || underflow) ? 0 : sum;
               Sat_Symmetric:   return overflow ? maxBound : ((underflow || isMinBound) ? minBound+1 : sum);
      endcase;
      return sum;
   endfunction
   function Int#(n) satMinus (SaturationMode smode, Int#(n) x, Int#(n) y);
      let diff = x - y;
      let overflow  = msb(x) == 0 && msb(y) == 1 && msb(diff) == 1;
      let underflow = msb(x) == 1 && msb(y) == 0 && msb(diff) == 0;
      let isMinBound = diff == minBound;
      diff = case (smode)
               Sat_Wrap:        return diff;
               Sat_Bound:       return overflow ? maxBound : (underflow ? minBound : diff);
               Sat_Zero:        return (overflow || underflow) ? 0 : diff;
               Sat_Symmetric:   return overflow ? maxBound : ((underflow || isMinBound) ? minBound+1 : diff);
      endcase;
      return diff;
   endfunction
endinstance

instance SaturatingArith#(UInt#(n));
   function UInt#(n) satPlus (SaturationMode smode, UInt#(n) x, UInt#(n) y);
      let sum = x + y;
      let overflow  = ((msb(x) == 0 && msb(y) == 1 && msb(sum) == 0) ||
                       (msb(x) == 1 && msb(y) == 0 && msb(sum) == 0) ||
                       (msb(x) == 1 && msb(y) == 1 )
                       );
      sum = case (smode)
               Sat_Wrap:        return sum;
               Sat_Bound:       return  overflow ? maxBound : sum;
               Sat_Zero:        return  overflow ? 0 : sum;
               Sat_Symmetric:   return  overflow ? maxBound : sum;
      endcase;
      return sum;
   endfunction
   function UInt#(n) satMinus (SaturationMode smode, UInt#(n) x, UInt#(n) y);
      let diff = x - y;
      let underflow = ((msb(x) == 0 && msb(y) == 0 && msb(diff) == 1) ||
                       (msb(x) == 0 && msb(y) == 1)                   ||
                       (msb(x) == 1 && msb(y) == 1 && msb(diff) == 1)
                       );
      diff = case (smode)
               Sat_Wrap:        return diff;
               Sat_Bound:       return underflow ? minBound : diff;
               Sat_Zero:        return underflow ? 0 : diff;
               Sat_Symmetric:   return underflow ? minBound : diff;
      endcase;
      return diff;
   endfunction
endinstance

// =========================

endpackage: PreludeBSV
