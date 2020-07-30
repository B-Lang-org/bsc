(*split*)
function Action foo (int x) ;
    Action a=action
      $display(100);
    endaction;
    Action b= action
      $display(200);
    endaction;
        if (x==10)
        return a;
        else
        return b;
endfunction

(* synthesize *)
module sysx () ;
  Reg#(Bool) myregister <- mkRegU();

  rule foobar;
        let m=foo(10);
        m;
  endrule
endmodule
