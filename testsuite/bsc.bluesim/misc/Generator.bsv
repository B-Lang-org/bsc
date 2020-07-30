import Vector::*;
import StmtFSM::*;
import LFSR::*;

import TypeUtil::*;
import Sudoku::*;
import Solver::*;

// A SudokuGenerator interface allows the generator to be seeded,
// and a puzzle generated based on that seed.  Once the puzzle
// has been generated, the givens can be read from the generator.
interface SudokuGenerator#(numeric type order);

   // start generating a puzzle
   method Action start();
      
   // test if puzzle generation is complete
   method Bool done();

endinterface: SudokuGenerator

module mkGenerator(SudokuGenerator#(order))
   provisos(Mul#(order, order, size), Log#(size, index_bits),
	    HasSolver#(order), Add#(1,_,TSquare#(order)),
	    Add#(a,TLog#(order),TLog#(TSquare#(order))),
	    Log#(size, TLog#(TSquare#(order))),
	    Add#(b, TLog#(TSquare#(order)), 16),
	    Add#(c, TLog#(TAdd#(TSquare#(order),1)), 16),
	    Add#(d, TLog#(TAdd#(1,TSquare#(order))), 16));
      
   // Solver used in generation process
   SudokuSolver#(order) solver <- mkSudokuSolver();
   
  Stmt generate_puzzle =
         seq
            while (True)
	    seq
              solver.startSolver();
              await(solver.done());
            endseq
         endseq;

   FSM fsm <- mkFSM(generate_puzzle);
   
   method Action start() if (fsm.done());
      fsm.start();
   endmethod: start

   method Bool done();
      return fsm.done();
   endmethod: done
   
endmodule: mkGenerator

// Create separately-synthesized generator modules for common sizes, along
// with a typeclass that allows the automatic selection of the
// appropriate module.

(* synthesize *)
module mkGenerator2(SudokuGenerator#(2));
   SudokuGenerator#(2) _g <- mkGenerator();
   return (_g);
endmodule: mkGenerator2

(* synthesize *)
module mkGenerator3(SudokuGenerator#(3));
   SudokuGenerator#(3) _g <- mkGenerator();
   return (_g);
endmodule: mkGenerator3

(* synthesize *)
module mkGenerator4(SudokuGenerator#(4));
   SudokuGenerator#(4) _g <- mkGenerator();
   return (_g);
endmodule: mkGenerator4

typeclass HasGenerator#(numeric type order);
   module mkSudokuGenerator(SudokuGenerator#(order));
endtypeclass: HasGenerator

instance HasGenerator#(2);
   module mkSudokuGenerator(SudokuGenerator#(2));
      SudokuGenerator#(2) _g <- mkGenerator2();
      return (_g);
   endmodule: mkSudokuGenerator
endinstance: HasGenerator

instance HasGenerator#(3);
   module mkSudokuGenerator(SudokuGenerator#(3));
      SudokuGenerator#(3) _g <- mkGenerator3();
      return (_g);
   endmodule: mkSudokuGenerator
endinstance: HasGenerator

instance HasGenerator#(4);
   module mkSudokuGenerator(SudokuGenerator#(4));
      SudokuGenerator#(4) _g <- mkGenerator4();
      return (_g);
   endmodule: mkSudokuGenerator
endinstance: HasGenerator
