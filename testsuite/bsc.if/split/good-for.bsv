(* synthesize *)
module sysx () ;
  Reg#(Bool) myregister <- mkRegU();
  rule foobar;
        // exponential in the size of "5"
        // thus pedantically doubly-exponential in the size of this code
        (*split*)
        for(int i=0;i<5;i=i+1)
        if (myregister)
        $display(i);
        else
        $display("foo");

  endrule
endmodule
