import StmtFSM::*;

import TypeUtil::*;
import Sudoku::*;

// A SudokuSolver interface allows the grid to be set and examined
// and allows the solver to be started.  When the solver
// is finished, some status of the solution can be retrieved.
interface SudokuSolver#(numeric type order);

   // start solving the current grid
   method Action startSolver();

   // test if the solver is finished
   method Bool done();

endinterface: SudokuSolver

// This solver operates by scanning through the grid and applying
// each tactic to each cell.  As it scans it keeps track of whether
// it has made progress in any cell as well as if any cell is incomplete.
// It uses that information to determine when it is stuck and when it
// has solved the grid.
module mkSolver(SudokuSolver#(order))
   provisos(Mul#(order,order,size), Mul#(size,size,num_cells),
	    Add#(1,x,TSquare#(order)),
	    Add#(_,TLog#(order),TLog#(TSquare#(order))));
	    
   Reg#(Bool) all_cells_complete <- mkReg(False);

   Stmt tactic_sequence =
      seq
	 all_cells_complete <= True;
      endseq;
   
   FSM controller <- mkFSM(tactic_sequence);
      
   method Action startSolver();
      controller.start();	      
   endmethod: startSolver
   
   method Bool done();
      return (controller.done());
   endmethod: done

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
