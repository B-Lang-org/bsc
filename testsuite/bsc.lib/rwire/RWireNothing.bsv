(* synthesize *)
module sysRWireNothing(Empty);

  RWire#(Bit#(16)) rw();
  mkRWire i_rw(rw);

  rule test (rw.wget() == Invalid);
    $display("Pass");
    $finish(0);
  endrule
endmodule
