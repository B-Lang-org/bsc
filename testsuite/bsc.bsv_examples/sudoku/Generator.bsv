import Vector::*;
import StmtFSM::*;
import LFSR::*;

import TypeUtil::*;
import Sudoku::*;
import Tactics::*;
import Solver::*;

// A SudokuGenerator interface allows the generator to be seeded,
// and a puzzle generated based on that seed.  Once the puzzle
// has been generated, the givens can be read from the generator.
interface SudokuGenerator#(numeric type order);

   // seed the pseudo-random number generator
   method Action seed(Bit#(16) s);
   
   // start generating a puzzle
   method Action start();
      
   // test if puzzle generation is complete
   method Bool done();

   // get the cell value for a particular cell
   method Cell#(order) getCellValue(Index#(order) r, Index#(order) c);
      
   // get the value of a given in a puzzle cell
   method Maybe#(UInt#(TLog#(TSquare#(order)))) getGiven(Index#(order) r, Index#(order) c);
         
endinterface: SudokuGenerator

module mkGenerator(SudokuGenerator#(order))
   provisos(Mul#(order, order, size), Log#(size, index_bits),
	    HasSolver#(order), Add#(1,_,TSquare#(order)),
	    Add#(a,TLog#(order),TLog#(TSquare#(order))),
	    Log#(size, TLog#(TSquare#(order))),
	    Add#(b, TLog#(TSquare#(order)), 16),
	    Add#(c, TLog#(TAdd#(TSquare#(order),1)), 16),
	    Add#(d, TLog#(TAdd#(1,TSquare#(order))), 16),
	    Bits#(Tactic#(order),sz0),
	    Bits#(TacticResult#(order),sz1));
      
   // Grid holding generated puzzle (givens)
   SudokuRegGrid#(order) puzzle <- mkReg(replicate(replicate(unknown())));

   // Solver used in generation process
   SudokuSolver#(order) solver <- mkSudokuSolver();
   
   // Row and column counters
   Reg#(LIndex#(order)) row <- mkReg(0);  
   Reg#(LIndex#(order)) col <- mkReg(0);  
      
   // Registers used for selecting allowed values
   Reg#(Cell#(order))  val <- mkReg(0);
   Reg#(Index#(order)) idx <- mkReg(0);

   // LFSR for generating a pseudo-random stream
   LFSR#(Bit#(16)) lfsr <- mkLFSR_16;
   
   // Registers used only for debug display
   Reg#(UInt#(16)) ri <- mkReg(0);
   Reg#(UInt#(16)) ci <- mkReg(0);
   
   function UInt#(16) randomValue(UInt#(16) x);
      UInt#(16) rv = unpack(lfsr.value());
      return (rv % x);
   endfunction: randomValue
   
  Stmt reset_puzzle =
         seq
           for (row <= 0; row <= fromInteger(valueOf(size)-1); row <= row + 1)
             for (col <= 0; col <= fromInteger(valueOf(size)-1); col <= col + 1)
		puzzle[row][col] <= unknown();
           $display("Puzzle reset.");
         endseq;

  Stmt load_solver = 
         seq
           for (row <= 0; row <= fromInteger(valueOf(size)-1); row <= row + 1)
             for (col <= 0; col <= fromInteger(valueOf(size)-1); col <= col + 1)
               solver.setCellValue(l2i(row), l2i(col),
				       getCell(puzzle, l2i(row), l2i(col)));
           $display("Solver loaded.");
         endseq;

  Stmt run_solver =
         seq
           $display("Running solver.");
           solver.startSolver();
           await(solver.done());
           $display("Solver done.");
           if (!solver.isConsistent())
             $display("Inconsistency detected");
           else
           seq
             if (solver.isSolved())
               $display("Solution completed");
             else
               $display("Need to specify more starting numbers");
           endseq
         endseq;

  Stmt randomize_location = 
         seq
           row <= truncate(randomValue(fromInteger(valueOf(size))));
           lfsr.next();
           col <= truncate(randomValue(fromInteger(valueOf(size))));
           lfsr.next();
         endseq;

  Stmt next_location =
         seq
           if (col == fromInteger(valueOf(size)-1))
           par
             col <= 0;
             if (row == fromInteger(valueOf(size)-1))
               row <= 0;
             else
               row <= row + 1;
           endpar
           else
             col <= col + 1; 
         endseq;

  Stmt find_incomplete_cell =
         seq
           $display("looking for incomplete cell");
           randomize_location;
           while (isComplete(solver.getCellValue(l2i(row), l2i(col))))
             next_location;
           $display("found incomplete cell at (%d,%d)", row, col);
         endseq;         
   
  Stmt select_allowed_value =
         seq
	    par
	       val <= solver.getCellValue(l2i(row), l2i(col));	    
	       idx <= truncate(randomValue(fromInteger(valueOf(size))));
	       lfsr.next();
	    endpar
	    while (val[idx] == 0)
	    seq
	       if (idx == 0)
		  idx <= fromInteger(valueOf(size) - 1);
	       else
		  idx <= idx - 1;
	    endseq	  
	    puzzle[l2i(row)][l2i(col)] <= (1 << idx);
         endseq;
   
  Stmt add_one_given = 
         seq
           find_incomplete_cell;
           select_allowed_value;
           solver.setCellValue(l2i(row), l2i(col),
			       getCell(puzzle, l2i(row), l2i(col)));
           $display("Adding given %d at (%d,%d)",
                    fromMaybe(?,cellValueUser(getCell(puzzle, l2i(row), l2i(col)))), 
                    row, col);
         endseq;

  Stmt try_to_generate = 
         seq
           reset_puzzle;
           load_solver;
           while (True)
           seq
              run_solver;
              if (!solver.isConsistent() || solver.isSolved()) break;
	      add_one_given;
           endseq
         endseq;
   
  Stmt generate_puzzle =
         seq
            while (True)
	    seq
               try_to_generate;	    
	       if (solver.isConsistent()) break;
               $display("discarding puzzle.");
            endseq
            $display("successfully generated puzzle:");
            displaySudoku(getCell(puzzle),asReg(ri),asReg(ci));
         endseq;

   FSM fsm <- mkFSM(generate_puzzle);
   
   method Action seed(Bit#(16) s) if (fsm.done());
      lfsr.seed(s);
   endmethod: seed

   method Action start() if (fsm.done());
      fsm.start();
   endmethod: start

   method Bool done();
      return fsm.done();
   endmethod: done
   
   method Cell#(order) getCellValue(Index#(order) r, Index#(order) c);
      return getCell(puzzle,r,c);
   endmethod: getCellValue
   
   method Maybe#(UInt#(value_bits)) getGiven(Index#(order) r, Index#(order) c)
      provisos(Mul#(order,order,size), Log#(size,value_bits));
      return cellValue(getCell(puzzle,r,c));
   endmethod: getGiven
   
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
