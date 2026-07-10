package FrameScope;

// The solved-dictionary pool is scoped per definition: dictionaries
// deposited while checking one binding are emitted with that
// binding's letseq and reused by later equal predicates.  Nested and
// sibling bindings demanding the same closed dictionaries stress the
// frame push/pop and emission scoping (regressions here are internal
// errors, not acceptance changes).

function Bit#(8) packer(UInt#(8) x);
  function Bit#(8) inner1(UInt#(8) a) = pack(a);
  function Bit#(8) inner2(UInt#(8) a);
    function Bit#(8) innermost(UInt#(8) b) = pack(b) + 1;
    return innermost(a);
  endfunction
  return inner1(x) ^ inner2(x);
endfunction

(* synthesize *)
module mkFrameScope();
  rule r;
    UInt#(8) v = 42;
    $display(packer(v), pack(v));
  endrule
endmodule
endpackage
