import Vector::*;
import StmtFSM::*;

import Sudoku::*;
import Generator::*;

(* synthesize *)
module mkGenerateTest3();

  SudokuGenerator#(3) generator <- mkSudokuGenerator();

  Stmt test = seq
                generator.start();
                await(generator.done());
              endseq;

  Empty fsm <- mkAutoFSM(test);

endmodule: mkGenerateTest3
