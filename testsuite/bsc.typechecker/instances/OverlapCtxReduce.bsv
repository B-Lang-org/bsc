// Test for Bug 1499: CtxReduce does not reduce a proviso too early

(* synthesize *)
module sysOverlapCtxReduce ();
  Reg#(Bit#(4)) rg <- mkReg(0);

  rule r;
    $display("%x", tcm(rg));
    $finish(0);
  endrule
endmodule

// ----

typeclass TC #(type t);
  function Bool tcm(t x);
endtypeclass

// general instance
instance TC #( at );
  function Bool tcm (at x);
    return False;
  endfunction
endinstance

// more specific instance
instance TC #( Bit#(4) );
  function Bool tcm (Bit#(4) x);
    return True;
  endfunction
endinstance

