(* synthesize *)
module sysUnsetRWire(Empty);
  RWire#(Bit#(16)) rw <- mkRWire;
  rule test (True);
    case (rw.wget()) matches
      Invalid : $display("InvalidNothing");
      tagged Valid {.v} : $display("ValidJust: %0d", v);
    endcase
    $finish(0);
  endrule
endmodule
