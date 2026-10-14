package BNotShared;

// Regression test for exponential PrimBNot-push-through-PrimIf over a
// SHARED conditional DAG in the evaluator (IExpand).
//
// Structure: K stages of odd-even conditional swaps over a
// Vector#(N, Bool) of register values.  Every swap condition negates a
// previous-stage element (!v[j-1] && v[j]), and that element is ALSO
// referenced in both branches of the stage's PrimIf muxes, so the
// elaborated value graph is a DAG whose if-depth grows by ~2 per stage
// (depth ~ 2K) while every node is shared.  An evaluator that pushes
// PrimBNot through PrimIf once per PATH (evalStaticOp: no memoization,
// plus a fresh evalAp heap application per leaf visit) must walk
// ~2^(2K) branch paths: at K=64 that is ~10^38 operations, i.e. it
// never terminates.  The per-heap-cell memoized push is O(N*K) cells
// and compiles in a few seconds.
//
// Deliberately NO pack/unpack (and no (* noinline *)) anywhere in the
// dataflow: the vector stays Vector#(N, Bool) end to end, so even a
// compiler that materializes pack/unpack coercions eagerly (stock
// upstream bsc) preserves the sharing and hits the same blowup.

import Vector :: *;

typedef 16 N;   // vector width  (leaf register cells)
typedef 64 K;   // full odd-even steps (if-depth grows ~2 per step)

// One full odd-even transposition step over plain Bools.
// "less than" for Bools is (!l && r), as in the byte-enable sort.
function Vector#(n, Bool) oestep (Vector#(n, Bool) vx);
   Vector#(n, Bool) evn = vx;
   for (Integer j = 1; j < valueOf(n); j = j + 2)
      if (!vx[j-1] && vx[j]) begin
         evn[j-1] = vx[j];
         evn[j]   = vx[j-1];
      end
   Vector#(n, Bool) odd = evn;
   for (Integer j = 2; j < valueOf(n); j = j + 2)
      if (!evn[j-1] && evn[j]) begin
         odd[j-1] = evn[j];
         odd[j]   = evn[j-1];
      end
   return odd;
endfunction

(* synthesize *)
module mkBNotShared (Empty);
   Vector#(N, Reg#(Bool)) rs <- replicateM(mkRegU);

   rule step;
      Vector#(N, Bool) v = readVReg(rs);
      for (Integer s = 0; s < valueOf(K); s = s + 1)
         v = oestep(v);
      writeVReg(rs, v);
   endrule
endmodule

endpackage
