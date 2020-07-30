import Vector::*;

import TypeUtil::*;
import SatMath::*;
import Sudoku::*;

// This type describes the existing tactic types
typedef union tagged
{ struct { Group#(order) group; Index#(order) idx;  } Singleton;
  struct { Group#(order) group; Index#(order) idx;  } Elimination;
  struct { Group#(order) group; Index#(order) idx;  } Pairs;
  struct { Group#(order) group; Index#(order) idx;  } HiddenPairs;
  struct { Group#(order) group; Mask#(order)  mask; } Intersect; 
} Tactic#(numeric type order)
deriving (Bits);

// A Mask is used to apply an analysis to a subset of a Group
typedef Vector#(TSquare#(order), Bool) Mask#(numeric type order);

// Create a mask based on parameters describing a coordinate,
// a conversion from the coordinate to the mask index, and
// a step interval.
function Mask#(order) make_mask(Index#(order) n, Integer step);
   Mask#(order) m = replicate(True);
   for (Integer i = 0; i < valueOf(order); i = i + 1)
      m[n+fromInteger(i*step)] = False;
   return m;
endfunction: make_mask				   

// Apply a mask bit to a cell value
function Cell#(order) applyMask(Cell#(order) c, Bool m);
   return (m ? c : impossible());
endfunction: applyMask

// Mask one cell in the group
function Group#(order) maskOne(Group#(order) g, Index#(order) n);
   return update(g,n,impossible());
endfunction: maskOne

// Mask several cells in a group
function Group#(order) maskN(Group#(order) g, Mask#(order) m);
   return zipWith(applyMask, g, m);
endfunction: maskN

// Determine all values which are possible in a group
function Cell#(order) possibles(Group#(order) g)
   provisos(Add#(1,_,SizeOf#(Cell#(order))));
   return fold(\| , g);
endfunction: possibles

// Determine all singletons which appear in a group
function Cell#(order) singletons(Group#(order) g)
   provisos(Add#(1,_,SizeOf#(Cell#(order))));   
   return possibles(maskN(g, map(isComplete, g)));
endfunction: singletons

// Test if two cells are equal
function Bool eq(Cell#(order) x, Cell#(order) y);
   return (x == y);
endfunction: eq

// Determine if a value is repeated in a group
function Bool repeated(Group#(order) g, Index#(order) n)
   provisos(Add#(1,_,TSquare#(order)));
   UInt#(2) count = fold(addSat(2), map(boolToSat, map(eq(g[n]), g)));
   return (count == 2);
endfunction: repeated

// Determine if a cell has only 2 possibilities
function Bool is2set(Cell#(order) c) provisos(Add#(1,_,TSquare#(order)));   
   UInt#(2) count = fold(addSat(3), map(boolToSat, bitsToVector(c)));
   return (count == 2);
endfunction: is2set
      
// Each solver tactic takes some arguments such as the index of
// the current cell in the group, the group values themselves, etc.
// It must return a cell value based on applying the tactic.
// The new cell value is determined by ANDing the existing value
// with the one returned by the tactic method.
interface Tactics#(numeric type order);
   
   // Tactic: Eliminate all values from this cell which appear as
   //         singletons in another cell in the group.
   // Arguments: g - constraint group containing the cell
   //            n - index of this cell in the group
   method Cell#(order) elim_other_singletons(Group#(order) g, Index#(order) n);
   
   // Tactic: If a value doesn't appear in any other cell in the group,
   //         then this cell must contain exactly that value (all the
   //         values that appear in other cells can be eliminated).
   // Arguments: g - constraint group containing the cell
   //            n - index of this cell in the group
   method Cell#(order) process_of_elimination(Group#(order) g, Index#(order) n);

   // Tactic: If in a constraint group which intersects a constraint group
   //         containing this cell (but which does not itself contain the cell),
   //         a value does not appear in the portion outside of the
   //         intersection, then it must appear within the intersection and
   //         can therefore be eliminated from this cell.
   // Arguments: g - constraint group intersecting a group containing the cell
   //                but not containing the cell itself
   //            m - mask of the portion of g outside of the intersection
   method Cell#(order) forced_in_intersection(Group#(order) g, Mask#(order) m);

   // Tactic: If a value appears in a 2-set which is repeated twice in the
   //         group (excluding this cell), then it can be eliminated from this
   //         cell.
   // Arguments: g - constraint group containing the cell
   //            n - index of this cell in the group
   method Cell#(order) repeated_2_set(Group#(order) g, Index#(order) n);
   
   // Tactic: If 2 of the values in this cell also appear together in one
   //         other cell, but neither appears outside of those cells, then
   //         all other values can be removed from this cell.
   // Arguments: g - constraint group containing the cell
   //            n - index of this cell in the group
   method Cell#(order) hidden_pair(Group#(order) g, Index#(order) n);
      
endinterface: Tactics

// mkTactics is a parameterized module in which each tactic is encapsulated
// as a single method of the module.  mkTactics cannot be
// separately synthesized because its interface contains an unbound type
// parameter.
module mkTactics(Tactics#(order))
   provisos(Mul#(order,order,size), Add#(1,_,SizeOf#(Cell#(order))));
   
   method Cell#(order) elim_other_singletons(Group#(order) g, Index#(order) n);
      return ~singletons(maskOne(g,n));
   endmethod: elim_other_singletons

   method Cell#(order) process_of_elimination(Group#(order) g, Index#(order) n);
      let ps = possibles(maskOne(g,n));
      if (ps == unknown())
	 return unknown();  // all values appear, conclude nothing
      else
	 return ~ps;        // some value does not appear, so remove all that do
   endmethod: process_of_elimination

   method Cell#(order) forced_in_intersection(Group#(order) g, Mask#(order) m);
      return possibles(maskN(g,m));
   endmethod: forced_in_intersection

   method Cell#(order) repeated_2_set(Group#(order) g, Index#(order) n);
      let two_set_mask = map(is2set, g);
      let indices = map(fromInteger, genVector());
      Mask#(order) repeat_mask = map(repeated(maskOne(g,n)), indices);
      return ~possibles(maskN(g, zipWith(\&& , two_set_mask, repeat_mask)));
   endmethod: repeated_2_set
      
   method Cell#(order) hidden_pair(Group#(order) g, Index#(order) n);
      let g1 = maskOne(g,n);
      Cell#(order) out = unknown();
      for (Integer i = 1; i < valueOf(size); i = i + 1)
      begin
	 let common = g1[i] & g[n];   
	 let ps = possibles(maskOne(g1,fromInteger(i)));
	 let test = is2set(common) && ((common & ps) == impossible());
	 out = test ? (out & common) : out;
      end
      return out;      
   endmethod: hidden_pair
   
endmodule: mkTactics

// Create separately-synthesized tactic modules for common sudoku
// orders, along with a typeclass that allows the automatic selection
// of the appropriate tactic module.

(* synthesize *)
module mkTactics2(Tactics#(2));
   Tactics#(2) _t <- mkTactics();
   return (_t);
endmodule: mkTactics2

(* synthesize *)
module mkTactics3(Tactics#(3));
   Tactics#(3) _t <- mkTactics();
   return (_t);
endmodule: mkTactics3

(* synthesize *)
module mkTactics4(Tactics#(4));
   Tactics#(4) _t <- mkTactics();
   return (_t);
endmodule: mkTactics4

typeclass HasTactics#(numeric type order);
   module mkSudokuTactics(Tactics#(order));
endtypeclass: HasTactics

instance HasTactics#(2);
   module mkSudokuTactics(Tactics#(2));
      Tactics#(2) _t <- mkTactics2();
      return (_t);
   endmodule: mkSudokuTactics
endinstance: HasTactics

instance HasTactics#(3);
   module mkSudokuTactics(Tactics#(3));
      Tactics#(3) _t <- mkTactics3();
      return (_t);
   endmodule: mkSudokuTactics
endinstance: HasTactics

instance HasTactics#(4);
   module mkSudokuTactics(Tactics#(4));
      Tactics#(4) _t <- mkTactics4();
      return (_t);
   endmodule: mkSudokuTactics
endinstance: HasTactics
