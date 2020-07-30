// two rules that are mutually exclusive 
// should still be that way with exec order
typedef enum
  { Rule1, Rule2, Exit } 
  State deriving(Eq, Bits);

(* synthesize *)
module sysMEExecOrder1();

  Reg#(State) state <- mkReg(Rule1);

  (* execution_order="rule1, rule2, exit, print_last" *)
  rule rule1(state == Rule1);
    $display("rule1");
    state <= Rule2;
  endrule

  rule rule2(state == Rule2);
    $display("rule2");
    state <= Exit;
  endrule

  rule print_last;
    $display("print_last");
  endrule

  rule exit(state == Exit);
    $display("exit");
    $finish(0);
  endrule

endmodule