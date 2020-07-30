(* synthesize *)
module sysx () ;
  Reg#(Bool) myregister <- mkRegU();
  rule foobar;
        // exponential in the size of "5"
        // thus pedantically doubly-exponential in the size of this code
        (*split*)
        action
        int i=0;
        // in order to avoid updated variables, the declaration must
        // be within ths split
        while (i<5)
        action
        if (myregister)
        $display(i);
        else
        $display("foo");
        i=i+1;
        endaction
        endaction

  endrule
endmodule
