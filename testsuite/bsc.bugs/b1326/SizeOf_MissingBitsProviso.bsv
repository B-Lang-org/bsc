function Action fn (t x);
    Bit#(SizeOf#(t)) n = 0;
    $display(" n = %d", n); 
endfunction

(* synthesize *)
module mkTest ();
  Reg#(Bool) rg <- mkRegU;

  rule r;
    fn(rg);
  endrule

endmodule

