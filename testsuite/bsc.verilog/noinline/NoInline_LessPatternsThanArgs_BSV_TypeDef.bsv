typedef function int f(int x, int y) MyFunc;

(* noinline *)
function MyFunc testLessPatternsBSVTypeDef();
    return (constFn(constFn(2)));
endfunction

(* synthesize *)
module sysNoInline_LessPatternsThanArgs_BSV_TypeDef ();
    Reg#(int) r <- mkReg(0);
    Reg#(Bool) set <- mkReg(False);

    rule do_set (!set);
      r <= testLessPatternsBSVTypeDef(r,7);
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

