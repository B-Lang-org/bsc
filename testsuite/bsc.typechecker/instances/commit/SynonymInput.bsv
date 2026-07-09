package SynonymInput;

// A2: a type synonym at an input position selects the same clause as
// its expansion.  Passing proves the Bool clause was selected through
// the synonym: the catch-all's output (MyFlag = Bool) conflicts with
// the demanded Bit#(8), so only the specific clause satisfies it.

typedef Bool MyFlag;

typeclass F#(type a, type b) dependencies (a determines b);
  function b ff(a x);
endtypeclass

instance F#(Bool, Bit#(8));
  function ff(x) = x ? 255 : 0;
endinstance

instance F#(a, a);
  function ff(x) = x;
endinstance

(* synthesize *)
module mkSynonymInput();
  rule r;
    MyFlag flag = True;
    Bit#(8) y = ff(flag);
    $display(y);
  endrule
endmodule
endpackage
