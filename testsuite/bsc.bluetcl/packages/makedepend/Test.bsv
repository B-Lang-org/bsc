import Vector::*;


// --------------------
// Types and Interfaces

typedef 9 Sz;

typedef Tuple2#(b,a) T#(type a, type b);

typedef enum { Red, Yellow, Blue } Bar deriving(Bits);
typedef enum { Red2 = 1, Yellow2, Blue2 } BarSet deriving(Bits);

typedef struct { Bool f1;
		 Bit#(n) f2;
		 Vector#(n,t) v;
	       } Baz#(type t, type n) deriving (Bits);

interface TopIFC#(type a);
   method Bool f(a x, a y);
   interface Clock clk_out;
   interface Reset rst_out;
   method Bool g(a z) provisos (Eq#(a));
   interface SubIFC#(a) s;
endinterface

interface SubIFC#(type a);
   interface Reg#(a) r;
endinterface

interface InoutIFC;
   interface Inout#(Bar) b;
endinterface

interface InoutRegIFC#(type a);
   interface Reg#(a) r;
   interface Inout#(Bar) b;
endinterface

typedef union tagged {
   void F1;
   a F2;
   List#(a) F3;
   function Bool f(Bool x) F4;
} U#(type a);

typedef union tagged {
   void F1;
   a F2;
} U2#(type a) deriving(Bits);

// for the import-BVI below
interface Foo#(type a) ;
   method Action wset(a x1);
   method a wget() ;
   method Bool whas() ;
   interface Inout#(Bool) io_out;
endinterface

// Alias for Vector
// (to test synonym expansion and make writing the below ifc easier)
typedef Vector#(2,t)  V2#(type t);

// Interface with Vector subinterfaces and Vector methods
interface IfcWithVec;
   interface V2#(Reg#(Bool))           vec1;
   interface V2#(V2#(Reg#(Bool)))      vec2;
   interface V2#(V2#(V2#(Reg#(Bool)))) vec3;
   method V2#(Bool)           data1();
   method V2#(V2#(Bool))      data2();
   method V2#(V2#(V2#(Bool))) data3();
endinterface

// --------------------
// Functions and Modules

Bool x = True;

function Bool f(Bool y1, Bool y2);
   return (y1 && y2);
endfunction

(* synthesize *)
module mkT #(Inout#(Bar) i) (InoutRegIFC#(Bool));
   Reg#(Bool) r1 <- mkM;
   Reg#(Bool) r2 <- mkM;
   InoutIFC mi <- mkI(i);
   Foo#(Bit#(4)) mb <- mkBVI(17, i);
   IfcWithVec iv <- mkIfcWithVec;
   interface Reg r;
      method _read = False;
      method _write(x) = noAction;
   endinterface
   interface b = mi.b;
endmodule

(* synthesize *)
module mkM(Reg#(Bool));
   Reg#(Bool) ptr <- mkReg(True);
   Reg#(Bool) r1 <- mkReg(True);
   Reg#(Bool) r2 <- mkReg(True);

   (* fire_when_enabled, no_implicit_conditions *)
   (* doc = "This is a rule" *)
   rule rHello (r1);
      $display("Hello");
   endrule

   rule rWorld;
      $display("World");
   endrule

   method _read = r1 && r2;

   method _write(v) = action
			 if (ptr)
			    r1 <= v;
			 else
			    r2 <= v;
		      endaction;
endmodule

(* synthesize *)
module mkI #(Inout#(Bar) i) (InoutIFC);
   interface b = i;
endmodule

import "BVI" VFoo =
   module mkBVI (int v, Inout#(Bar) io_in, Foo#(a) ifc)
      provisos (Bits#(a,sa));
      parameter width = valueOf(sa);
      default_clock clk();
      default_reset rst();
      port V = v + 1;
      inout I_IN = io_in;
      method wset(WVAL) enable(WSET);
      method WHAS whas ;
      method WGET wget ;
      ifc_inout io_out (I_OUT);
      schedule (wget, whas) CF (wget, whas) ;
      schedule wset SB (wget, whas) ;
      schedule wset C wset;
      path (WSET, WHAS) ;
      path (WVAL, WGET) ;
   endmodule

// A module for testing the dumping of scheduling information.
// This module has warnings during the scheduling phase and
// paths from inputs to outputs.
(* synthesize *)
module mkS(RWire#(Bool));

   RWire#(Bool) rw <- mkRWire();

   // Two conflicting rules, triggering an arbitrary urgency warning
   // and a warning that the less-urgent rule can never fire
   Reg#(int) rg1 <- mkReg(0);
   rule c1;
      rg1 <= rg1 + 1;
   endrule
   rule c2;
      rg1 <= rg1 + 2;
   endrule

   method wset = rw.wset;
   method wget = rw.wget;

endmodule

(* synthesize *)
module mkIfcWithVec (IfcWithVec);
   interface vec1 = ?;
   interface vec2 = ?;
   interface vec3 = ?;
   method data1 = ?;
   method data2 = ?;
   method data3 = ?;
endmodule

// --------------------
