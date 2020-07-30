(* noinline *)
function (function int f(int x, int y)) testLessPatternsBSVFunction();
    return (constFn(constFn(2)));
endfunction

(* synthesize *)
module sysNoInline_LessPatternsThanArgs_BSV_Function ();
    Reg#(int) r <- mkReg(0);
    Reg#(Bool) set <- mkReg(False);

    rule do_set (!set);
      r <= testLessPatternsBSVFunction(r,7);
      set <= True;
    endrule

    rule do_finish (set);
      if (r == 2)
        $display("Pass");
      else
        $display("Fail");
      $finish(0);
    endrule

endmodule

