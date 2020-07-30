import ListN::*;

import Array::*;

`define ROWS 16
`define COLS 16

//The goal is to exercise the evaluator with arrays



(* synthesize *)
module mkPATest ();

  Reg#(int) v[`ROWS][`COLS];
  int vs[`ROWS][`COLS];

  for (Integer x = 0; x < `ROWS; x = x + 1)
  begin
    for (Integer y = 0; y < `COLS; y = y + 1)
    begin
      v[x][y] <- mkReg(0);
      vs[x][y] = (v[x][y])._read;
      rule foo (True);
        $display("%.0d", vs[x][y]);
      endrule
    end
  end
  
endmodule

(* synthesize *)
module mkListNTest ();

  ListN#(`ROWS, ListN#(`COLS, Reg#(int))) v = replicate(replicate(?));
  ListN#(`ROWS, ListN#(`COLS, int)) vs = replicate(replicate(?));
  
  for (Integer x = 0; x < `ROWS; x = x + 1)
  begin
    for (Integer y = 0; y < `COLS; y = y + 1)
    begin
      v[x][y] <- mkReg(0);
      vs[x][y] = (v[x][y])._read;
      rule foo (True);
        $display("%.0d", vs[x][y]);
      endrule
    end
  end
  
endmodule
