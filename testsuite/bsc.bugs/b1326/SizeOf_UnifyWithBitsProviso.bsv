function Action fn (t x) provisos( Bits#(t,n) );
    Bit#(SizeOf#(t)) n = pack(x);
    $display(" n = %d", n); 
endfunction

(* synthesize *)
module mkTest ();
  Reg#(Bool) rg <- mkRegU;

  rule r;
    fn(rg);
  endrule

endmodule

