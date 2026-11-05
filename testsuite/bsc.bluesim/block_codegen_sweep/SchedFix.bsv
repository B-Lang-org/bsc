// Pressure -c codegen-mode byte-identity across the "access count" dimensions,
// stepping each 0 -> 1 -> 2 -> n.  Every module here is a submodule of the
// testbench in SchedFixTb.bsv; the testsuite's codegen-mode check then
// confirms each module's per-module C++ is byte-identical whether built on its
// own (-c) or as part of the design.
package SchedFix;

// ---------------------------------------------------------------------------
// D1: number of internal rules that read a shared value (0,1,2,3 readers)
interface Acc;
  method Action set(Bit#(8) x);
  method Bit#(8) get();
endinterface

(* synthesize *) module mkD1_0 (Acc);            // 0 reader rules
  Reg#(Bit#(8)) r <- mkReg(0);
  method Action set(Bit#(8) x); r <= x; endmethod
  method Bit#(8) get(); return r; endmethod
endmodule

(* synthesize *) module mkD1_1 (Acc);            // 1 reader rule
  Reg#(Bit#(8)) r <- mkReg(0); Reg#(Bit#(8)) a <- mkReg(0);
  rule u1; a <= a + r; endrule
  method Action set(Bit#(8) x); r <= x; endmethod
  method Bit#(8) get(); return a; endmethod
endmodule

(* synthesize *) module mkD1_2 (Acc);            // 2 reader rules
  Reg#(Bit#(8)) r <- mkReg(0); Reg#(Bit#(8)) a <- mkReg(0); Reg#(Bit#(8)) b <- mkReg(0);
  rule u1; a <= a + r; endrule
  rule u2; b <= b + (r << 1); endrule
  method Action set(Bit#(8) x); r <= x; endmethod
  method Bit#(8) get(); return a + b; endmethod
endmodule

(* synthesize *) module mkD1_3 (Acc);            // 3 reader rules
  Reg#(Bit#(8)) r <- mkReg(0);
  Reg#(Bit#(8)) a <- mkReg(0); Reg#(Bit#(8)) b <- mkReg(0); Reg#(Bit#(8)) c <- mkReg(0);
  rule u1; a <= a + r; endrule
  rule u2; b <= b + (r << 1); endrule
  rule u3; c <= c + (r << 2); endrule
  method Action set(Bit#(8) x); r <= x; endmethod
  method Bit#(8) get(); return a + b + c; endmethod
endmodule

// ---------------------------------------------------------------------------
// D2: number of method arguments (0,1,2,3)
interface Arg;
  method Action go0();
  method Action go1(Bit#(8) a);
  method Action go2(Bit#(8) a, Bit#(8) b);
  method Action go3(Bit#(8) a, Bit#(8) b, Bit#(8) c);
  method Bit#(8) v();
endinterface

(* synthesize *) module mkD2_args (Arg);
  Reg#(Bit#(8)) r <- mkReg(0);
  method Action go0(); r <= r + 1; endmethod
  method Action go1(Bit#(8) a); r <= a; endmethod
  method Action go2(Bit#(8) a, Bit#(8) b); r <= a + b; endmethod
  method Action go3(Bit#(8) a, Bit#(8) b, Bit#(8) c); r <= a + b + c; endmethod
  method Bit#(8) v(); return r; endmethod
endmodule

// ---------------------------------------------------------------------------
// D3: number of methods in the interface (1,2,3 value methods)
interface M1; method Bit#(8) a(); endinterface
interface M2; method Bit#(8) a(); method Bit#(8) b(); endinterface
interface M3; method Bit#(8) a(); method Bit#(8) b(); method Bit#(8) c(); endinterface

(* synthesize *) module mkD3_1 (M1);
  Reg#(Bit#(8)) r <- mkReg(1);
  method Bit#(8) a(); return r; endmethod
endmodule
(* synthesize *) module mkD3_2 (M2);
  Reg#(Bit#(8)) r <- mkReg(1);
  method Bit#(8) a(); return r; endmethod
  method Bit#(8) b(); return r + 1; endmethod
endmodule
(* synthesize *) module mkD3_3 (M3);
  Reg#(Bit#(8)) r <- mkReg(1);
  method Bit#(8) a(); return r; endmethod
  method Bit#(8) b(); return r + 1; endmethod
  method Bit#(8) c(); return r + 2; endmethod
endmodule

// ---------------------------------------------------------------------------
// D4: method kind (value, action, actionvalue)
interface KV;  method Bit#(8) v(); endinterface
interface KA;  method Action a(Bit#(8) x); endinterface
interface KAV; method ActionValue#(Bit#(8)) av(Bit#(8) x); endinterface

(* synthesize *) module mkD4_val (KV);
  Reg#(Bit#(8)) r <- mkReg(7);
  method Bit#(8) v(); return r; endmethod
endmodule
(* synthesize *) module mkD4_act (KA);
  Reg#(Bit#(8)) r <- mkReg(0);
  method Action a(Bit#(8) x); r <= r + x; endmethod
endmodule
(* synthesize *) module mkD4_av (KAV);
  Reg#(Bit#(8)) r <- mkReg(0);
  method ActionValue#(Bit#(8)) av(Bit#(8) x); r <= r + x; return r; endmethod
endmodule

// ---------------------------------------------------------------------------
// D5: number of (non-primitive) submodule instances (0,1,2,3)
interface Cnt; method Bit#(8) tot(); endinterface

(* synthesize *) module mkLeaf (Acc);
  Reg#(Bit#(8)) r <- mkReg(0);
  method Action set(Bit#(8) x); r <= x; endmethod
  method Bit#(8) get(); return r; endmethod
endmodule

(* synthesize *) module mkD5_0 (Cnt);
  Reg#(Bit#(8)) r <- mkReg(3);
  method Bit#(8) tot(); return r; endmethod
endmodule
(* synthesize *) module mkD5_1 (Cnt);
  Acc s0 <- mkLeaf;
  rule t; s0.set(1); endrule
  method Bit#(8) tot(); return s0.get(); endmethod
endmodule
(* synthesize *) module mkD5_2 (Cnt);
  Acc s0 <- mkLeaf; Acc s1 <- mkLeaf;
  rule t; s0.set(1); s1.set(2); endrule
  method Bit#(8) tot(); return s0.get() + s1.get(); endmethod
endmodule
(* synthesize *) module mkD5_3 (Cnt);
  Acc s0 <- mkLeaf; Acc s1 <- mkLeaf; Acc s2 <- mkLeaf;
  rule t; s0.set(1); s1.set(2); s2.set(3); endrule
  method Bit#(8) tot(); return s0.get() + s1.get() + s2.get(); endmethod
endmodule

// ---------------------------------------------------------------------------
// D7: subinterface forwarding to a submodule (the cache shape)
interface Fwd;
  interface Acc inner;
endinterface

(* synthesize *) module mkD7_fwd (Fwd);
  Acc s <- mkLeaf;
  Reg#(Bit#(8)) n <- mkReg(0);
  rule tick; n <= n + 1; endrule
  interface Acc inner = s;
endmodule

// ---------------------------------------------------------------------------
// D8: several distinct submodule instances, named so insertion order differs
// from name order (stresses state-instance / symbol-table ordering).
(* synthesize *) module mkD8_insts (Cnt);
  Acc zz <- mkLeaf; Acc aa <- mkLeaf; Acc mm <- mkLeaf;
  rule t; zz.set(1); aa.set(2); mm.set(3); endrule
  method Bit#(8) tot(); return zz.get() + aa.get() + mm.get(); endmethod
endmodule

// ---------------------------------------------------------------------------
// D9: kitchen sink -- many registers (declared out of name order), several
// rules (named out of order), and several methods of mixed kinds, to stress
// the member-def, state, rule and method orderings together.
interface Sink;
  method Action poke(Bit#(8) x);
  method Bit#(8) red();
  method ActionValue#(Bit#(8)) step();
endinterface
(* synthesize *) module mkD9_sink (Sink);
  Reg#(Bit#(8)) z <- mkReg(0); Reg#(Bit#(8)) a <- mkReg(0);
  Reg#(Bit#(8)) m <- mkReg(0); Reg#(Bit#(8)) b <- mkReg(0);
  Reg#(Bit#(8)) y <- mkReg(0); Reg#(Bit#(8)) c <- mkReg(0);
  rule rz; z <= z + a; endrule
  rule ra; a <= a + b; endrule
  rule rm; m <= m + z + y; endrule
  rule rb; b <= b + c; endrule
  method Action poke(Bit#(8) x); c <= c + x; endmethod
  method Bit#(8) red(); return z + a + m + b + y + c; endmethod
  method ActionValue#(Bit#(8)) step(); y <= y + 1; return m; endmethod
endmodule

endpackage
