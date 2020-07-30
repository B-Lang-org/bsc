import Vector::*;
import StmtFSM::*;

import Sudoku::*;
import Solver::*;
import Generator::*;

(* synthesize *)
module mkGenerateTest3();

  SudokuGenerator#(3) generator <- mkSudokuGenerator();

  SudokuSolver#(3) solver <- mkSudokuSolver();

  Reg#(LIndex#(3)) r <- mkReg(0);  
  Reg#(LIndex#(3)) c <- mkReg(0);  

  // Registers used for debug display only      
  Reg#(UInt#(16)) x <- mkReg(0);
  Reg#(UInt#(16)) y <- mkReg(0);
   
  Stmt load_puzzle = seq
                       for (r <= 0; r <= 8; r <= r + 1)
                         for (c <= 0; c <= 8; c <= c + 1)
                           solver.setCellValue(l2i(r),l2i(c),generator.getCellValue(l2i(r),l2i(c)));
                     endseq;

  Stmt test = seq
                generator.start();
                await(generator.done());
                load_puzzle;
                solver.startSolver();
                await(solver.done());
                if (!solver.isConsistent())
                  $display("Puzzle has no solution!");
                if (solver.isSolved())
                  $display("I solved it!");
                displaySudoku(solver.getCellValue, asReg(x), asReg(y));
                if (!solver.isSolved())
                  debugSudoku(solver.getCellValue, asReg(x), asReg(y));
              endseq;

  Empty fsm <- mkAutoFSM(test);

endmodule: mkGenerateTest3
