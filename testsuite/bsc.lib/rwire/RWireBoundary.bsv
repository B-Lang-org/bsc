interface Test;
  method Action poke();
  method Bool poked(); // was it poked in this clock cycle?
endinterface

(* synthesize *)
module sysPokeTest(Test);
  // hack because Icarus can't deal with a wire of size 0
  RWire#(Bool) rw();
  mkRWire i_rw(rw);

  method poke();
    action
      rw.wset(True);
    endaction
  endmethod
  method poked();
    return(rw.wget() != Invalid);
  endmethod
endmodule
  
module sysRWireBoundary(Empty);
  Test tester();
  sysPokeTest i_tester(tester);

  rule check(tester.poked);
    $display("Pass");
    $finish(0);
  endrule
  
  rule poke(True);
    tester.poke();
  endrule

endmodule
