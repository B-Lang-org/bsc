
(* synthesize *)
module mkCommentOnRule();

   Reg#(Bool) b <- mkRegU;
   Reg#(Bool) x <- mkRegU;

   // tests also: \n in string, multiple doc in same list, multiple lists
   (* doc = "This rule is important", doc = "Foo\nBar" *)
   (* doc = "Baz" *)
   rule do_something (b);
      x <= !x;
   endrule

   // This rule is not :)
   rule do_another_thing (!b);
      b <= !b;
   endrule

endmodule

