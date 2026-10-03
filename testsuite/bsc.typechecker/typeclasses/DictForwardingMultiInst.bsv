package DictForwardingMultiInst;

typedef struct {
   a value;
} At#(numeric type stage, type a);

typeclass Stamp#(type x, numeric type n)
   dependencies (x determines n);
   function Bit#(n) stamp(x value);
endtypeclass

instance Stamp#(At#(1, Bit#(3)), 3);
   function stamp(value) = value.value + 3'd1;
endinstance

instance Stamp#(At#(2, Bit#(5)), 5);
   function stamp(value) = value.value + 5'd2;
endinstance

(* synthesize *)
module sysDictForwardingMultiInst(Empty);
   // With -let-gen, this binding is generalized over both its value type
   // and width.  The two identical Stamp predicates are joined, leaving a
   // dictionary forwarding edge which must be applied to both calls.
   function twice(value);
      return tuple2(stamp(value), stamp(value));
   endfunction

   // Generalize a second binding which instantiates twice twice.  Its body
   // therefore needs type-variable rewriting at the same time that its own
   // duplicate dictionary predicates are forwarded.
   function relay(value);
      return tuple2(tpl_1(twice(value)), tpl_2(twice(value)));
   endfunction

   rule check;
      At#(1, Bit#(3)) x1 = At { value: 3'd1 };
      At#(2, Bit#(5)) x2 = At { value: 5'd3 };
      Tuple2#(Bit#(3), Bit#(3)) y1 = relay(x1);
      Tuple2#(Bit#(5), Bit#(5)) y2 = relay(x2);

      $display("%0d %0d %0d %0d",
               tpl_1(y1), tpl_2(y1), tpl_1(y2), tpl_2(y2));
      $finish(0);
   endrule
endmodule

endpackage
