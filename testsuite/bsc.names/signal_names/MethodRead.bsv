(* synthesize *)
module sysMethodRead ();
  Reg#(Bit#(8)) rg <- mkRegU;

  rule r;
     $display(rg + 8);
     $display(rg - 1);
  endrule

endmodule

