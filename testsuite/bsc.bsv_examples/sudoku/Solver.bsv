import Vector::*;
import FIFOF::*;
import StmtFSM::*;

import TypeUtil::*;
import Sudoku::*;
import Tactics::*;

// A SudokuSolver interface allows the grid to be set and examined
// and allows the solver to be started.  When the solver
// is finished, some status of the solution can be retrieved.
interface SudokuSolver#(numeric type order);

   // set the cell value indexed by row and column to a given value
   method Action setCellValue(Index#(order) r, Index#(order) c, Cell#(order) v);

   // retrieve the cell value at given row and column
   method Cell#(order) getCellValue(Index#(order) r, Index#(order) c);

   // start solving the current grid
   method Action startSolver();

   // test if the solver is finished
   method Bool done();

   // test if the current grid configuration is known to be consistent
   method Bool isConsistent();

   // test if the current grid configuration is known to be a complete
   // and consistent solution
   method Bool isSolved();
   
   // used to monitor the tactics as they are applied 
   method TacticResult#(order) watchTactic();
      
endinterface: SudokuSolver

// A TacticResult describes the result of applying a solver tactic
// to a particular cell location.
typedef struct
{ Tactic#(order) tactic;
  Index#(order)  row;
  Index#(order)  column;
  Cell#(order)   original;
  Cell#(order)   result;
} TacticResult#(numeric type order)
deriving (Bits);

// This solver operates by scanning through the grid and applying
// each tactic to each cell.  As it scans it keeps track of whether
// it has made progress in any cell as well as if any cell is incomplete.
// It uses that information to determine when it is stuck and when it
// has solved the grid.
module mkSolver(SudokuSolver#(order))
   provisos(Mul#(order,order,size), Mul#(size,size,num_cells),
	    HasTactics#(order), Add#(1,x,TSquare#(order)),
	    Add#(_,TLog#(order),TLog#(TSquare#(order))),
	    Bits#(Tactic#(order),sz0),
	    Bits#(TacticResult#(order),sz1));
	    
   SudokuRegGrid#(order) grid <- mkReg(replicate(replicate(unknown())));
   
   Tactics#(order) tactics <- mkSudokuTactics();
   
   Reg#(LIndex#(order))         row_idx <- mkReg(0);
   Reg#(LIndex#(order))         col_idx <- mkReg(0);
   Reg#(RFIndex#(order))        tactic_idx <- mkReg(0);
   FIFOF#(TacticResult#(order)) results <- mkFIFOF();
   
   Reg#(Bool) found_inconsistent <- mkReg(False);   
   Reg#(Bool) all_cells_complete <- mkReg(False);
   Reg#(Bool) made_some_progress <- mkReg(True);
   
   // indexes used by solvers
   Index#(order)   row     = l2i(row_idx);
   Index#(order)   col     = l2i(col_idx);
   Index#(order)   box_idx = gridToBoxGroup(row,col);
   RFIndex#(order) rank    = gridToRF(row);
   RFIndex#(order) file    = gridToRF(col);
   
   function Index#(order) other(Index#(order) n);
      let rf = gridToRF(n);
      let i  = gridToBox(n);
      if (tactic_idx < i)
	 return boxToGrid(rf,tactic_idx);
      else
	 return boxToGrid(rf,tactic_idx + 1);
   endfunction: other
   
   function RFIndex#(order) other_rf(RFIndex#(order) n);
      if (tactic_idx < n)
	 return tactic_idx;
      else
	 return tactic_idx + 1;
   endfunction: other_rf
   
   function Index#(order) startOfRF(Index#(order) n);
      let i = gridToBox(n);
      return (n - extend(i));
   endfunction: startOfRF
   
   // groups used by tactics
   Group#(order) current_row = getRow(grid, row);
   Group#(order) current_col = getColumn(grid, col);
   Group#(order) current_box = getBox(grid, rank, file);
   Group#(order) other_row   = getRow(grid, other(row));
   Group#(order) other_col   = getColumn(grid, other(col));
   Group#(order) other_box_rank = getBox(grid, rank, other_rf(file));
   Group#(order) other_box_file = getBox(grid, other_rf(rank), file);
					 
   // masks used by tactics
   Mask#(order) mask_row  = make_mask(gridToBoxGroup(row,0),1);
   Mask#(order) mask_col  = make_mask(gridToBoxGroup(0,col),valueOf(order));
   Mask#(order) mask_rank = make_mask(startOfRF(row),1);
   Mask#(order) mask_file = make_mask(startOfRF(col),1);

   // Apply a given tactic, record the result of applying it, and use
   // the result to constrain the current cell.
   function Action apply(Tactic#(order) tactic);
   action
      let tactic_result = unknown();
      case (tactic) matches
	 tagged Singleton {group: .g, idx: .i}:
	    tactic_result = tactics.elim_other_singletons(g,i);
	 tagged Elimination {group: .g, idx: .i}:
	    tactic_result = tactics.process_of_elimination(g,i);
 	 tagged Pairs {group: .g, idx: .i}:
	    tactic_result = tactics.repeated_2_set(g,i);
 	 tagged HiddenPairs {group: .g, idx: .i}:
	    tactic_result = tactics.hidden_pair(g,i);
	 tagged Intersect {group: .g, mask: .m}:
	    tactic_result = tactics.forced_in_intersection(g,m);
      endcase

      let orig = grid[row][col];
      grid[row][col] <= orig & tactic_result;      
      results.enq(tagged TacticResult { tactic:   tactic
				      , row:      row
				      , column:   col
	                              , original: orig
	                              , result:   tactic_result
				       });
   endaction                  
   endfunction: apply

   Stmt tactic_sequence =
      seq
	 while (True)
	 seq
	    action
	       found_inconsistent <= False;
	       all_cells_complete <= True;
	       made_some_progress <= False;
	    endaction
	    for (row_idx <= 0; row_idx < fromInteger(valueOf(size)); row_idx <= row_idx + 1)
	    seq
	       for (col_idx <= 0; col_idx < fromInteger(valueOf(size)); col_idx <= col_idx + 1)
	       seq
		  apply(tagged Singleton { group: current_row
					 , idx:   col
					 });
		  apply(tagged Singleton { group: current_col
					 , idx:   row
					  });
		  apply(tagged Singleton { group: current_box
					 , idx:   box_idx
					 });
		  apply(tagged Elimination { group: current_row
					   , idx:   col
					   });
		  apply(tagged Elimination { group: current_col
					   , idx:   row
					   });
		  apply(tagged Elimination { group: current_box
					   , idx:   box_idx
					   });
		  apply(tagged Pairs { group: current_row
				     , idx:   col
				     });
		  apply(tagged Pairs { group: current_col
				     , idx:   row
				     });
		  apply(tagged Pairs { group: current_box
				     , idx:   box_idx
				      });
		  apply(tagged HiddenPairs { group: current_row
					    , idx:   col
					    });
		  apply(tagged HiddenPairs { group: current_col
					    , idx:   row
					    });
		  apply(tagged HiddenPairs { group: current_box
					    , idx:   box_idx
					    });
		  for (tactic_idx <= 0; tactic_idx < fromInteger(valueOf(order)-1); tactic_idx <= tactic_idx + 1)
		  seq
		     apply(tagged Intersect { group: other_col
					    , mask:  mask_rank
					    });
		     apply(tagged Intersect { group: other_row
					    , mask:  mask_file
					     });
		     apply(tagged Intersect { group: other_box_rank
					    , mask:  mask_row
					    });
		     apply(tagged Intersect { group: other_box_file
					    , mask:  mask_col
					    });		     
		  endseq
	       endseq
	    endseq
	    await(!results.notEmpty());
	    if (found_inconsistent || all_cells_complete || !made_some_progress)
	       break;
	 endseq
      endseq;
   
   FSM controller <- mkFSM(tactic_sequence);
      
   rule monitor_results;
      let res = results.first();
      results.deq();           

      let restricted_value = res.original & res.result;
      
      if (restricted_value == impossible())
         found_inconsistent <= True;
      
      if (!isComplete(restricted_value))
	 all_cells_complete <= False;
      
      if (restricted_value != res.original)
	 made_some_progress <= True;
   endrule: monitor_results
  
   // ====================================================================
   // Interface methods for controlling the solver
   // ====================================================================
      
   method Action setCellValue(Index#(order) r, Index#(order) c, Cell#(order) v) if (controller.done());
      grid[r][c] <= v;
   endmethod: setCellValue

   method Cell#(order) getCellValue(Index#(order) r, Index#(order) c) if (controller.done());
      return (grid[r][c]);
   endmethod: getCellValue

   method Action startSolver();
      controller.start();	      
   endmethod: startSolver
   
   method Bool done();
      return (controller.done());
   endmethod: done

   method Bool isConsistent() if (controller.done());
      return !found_inconsistent;
   endmethod: isConsistent

   method Bool isSolved() if (controller.done());
      return all_cells_complete;
   endmethod: isSolved
   
   method TacticResult#(order) watchTactic();
      return (results.first());
   endmethod: watchTactic
   
endmodule: mkSolver


// Create separately-synthesized solver modules for common sizes, along
// with a typeclass that allows the automatic selection of the
// appropriate module.

(* synthesize *)
module mkSolver2(SudokuSolver#(2));
   SudokuSolver#(2) _s <- mkSolver();
   return (_s);
endmodule: mkSolver2

(* synthesize *)
module mkSolver3(SudokuSolver#(3));
   SudokuSolver#(3) _s <- mkSolver();
   return (_s);
endmodule: mkSolver3

(* synthesize *)
module mkSolver4(SudokuSolver#(4));
   SudokuSolver#(4) _s <- mkSolver();
   return (_s);
endmodule: mkSolver4

typeclass HasSolver#(numeric type order);
   module mkSudokuSolver(SudokuSolver#(order));
endtypeclass: HasSolver

instance HasSolver#(2);
   module mkSudokuSolver(SudokuSolver#(2));
      SudokuSolver#(2) _s <- mkSolver2();
      return (_s);
   endmodule: mkSudokuSolver
endinstance: HasSolver

instance HasSolver#(3);
   module mkSudokuSolver(SudokuSolver#(3));
      SudokuSolver#(3) _s <- mkSolver3();
      return (_s);
   endmodule: mkSudokuSolver
endinstance: HasSolver

instance HasSolver#(4);
   module mkSudokuSolver(SudokuSolver#(4));
      SudokuSolver#(4) _s <- mkSolver4();
      return (_s);
   endmodule: mkSudokuSolver
endinstance: HasSolver
