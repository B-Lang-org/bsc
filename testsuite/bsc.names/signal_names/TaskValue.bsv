(* synthesize *)
module sysTaskValue ();
  rule r;
     Bit#(32) v <- $sformatAV(0);
     $display(v + 8);
  endrule

endmodule

