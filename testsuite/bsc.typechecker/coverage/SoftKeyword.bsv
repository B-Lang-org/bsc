package SoftKeyword;
// `coherent' and `incoherent' are soft keywords: still valid identifiers
(* synthesize *)
module mkSoftKeyword();
  rule r;
    Integer coherent = 1;
    Integer incoherent = 2;
    $display(coherent + incoherent);
  endrule
endmodule
endpackage
