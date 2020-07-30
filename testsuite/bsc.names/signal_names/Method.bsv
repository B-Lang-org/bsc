(* synthesize *)
module sysMethod ();
  RWire#(Bit#(8)) rg <- mkRWire;

  rule r;
     $display(rg.wget);
     $display(rg.wget);
  endrule

endmodule

