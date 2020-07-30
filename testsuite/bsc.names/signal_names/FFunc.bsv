import "BDPI" function Bit#(8) fnFFunc(Bit#(8) x);

(* synthesize *)
module sysFFunc ();
  rule r;
     $display(fnFFunc(0) + 8);
  endrule

endmodule

