package UncovInc;
typeclass incoherent C#(type a, type b) dependencies (a determines b);
  function b f(a x);
endtypeclass
instance C#(Bool, v);
  function f(x) = ?;
endinstance
(* synthesize *)
module mkUncovInc();
  rule r; Bool b = True; Bit#(8) y = f(b); $display(y); endrule
endmodule
endpackage
