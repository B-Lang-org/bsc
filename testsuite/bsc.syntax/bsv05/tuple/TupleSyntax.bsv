// Tuple#(...) and tuple(...) of 0 to 8 elements

typedef Tuple#(Bool, UInt#(8)) Pair;

function Tuple#(UInt#(8), UInt#(8), UInt#(8)) rot3(Tuple#(UInt#(8), UInt#(8), UInt#(8)) t);
   match {.a, .b, .c} = t;
   return tuple(b, c, a);
endfunction

function Bool inv(Bool b) = !b;

(* synthesize *)
module sysTupleSyntax();

   Tuple#() zero = tuple();
   void compatible = zero;
   Bit#(0) zeroBits = pack(zero);
   Tuple#(Bool) one = tuple(True);

   // Arity 2, through a typedef
   Pair p = tuple(True, 8'd7);

   // Arity 3, interchangeable with Tuple3/tuple3
   Tuple3#(UInt#(8), UInt#(8), UInt#(8)) t3old = tuple3(1, 2, 3);
   Tuple#(UInt#(8), UInt#(8), UInt#(8))  t3new = rot3(t3old);
   Tuple3#(UInt#(8), UInt#(8), UInt#(8)) t3back = tuple(2, 3, 1);

   // Arity 8, the largest supported
   Tuple#(Bit#(1), Bit#(2), Bit#(3), Bit#(4), Bit#(5), Bit#(6), Bit#(7), Bit#(8))
      t8 = tuple(1, 2, 3, 4, 5, 6, 7, 8);

   // More than 8 elements: nest tuples, as with Tuple8; tpl_8 is the nested
   // tuple, exactly as for Tuple8
   Tuple#(UInt#(4), UInt#(4), UInt#(4), UInt#(4), UInt#(4), UInt#(4), UInt#(4),
          Tuple#(UInt#(4), UInt#(4)))
      n8 = tuple(1, 2, 3, 4, 5, 6, 7, tuple(8, 9));

   // Tuples in a register (Bits) and compared (Eq)
   Reg#(Tuple#(Bool, UInt#(4), Bit#(3))) r <- mkReg(tuple(False, 5, 3'b101));

   rule show;
      $display("empty = %b %b, bits = %0d", zero == compatible,
               zero == unpack(zeroBits), valueOf(SizeOf#(Tuple#())));
      $display("one = %b, calls = %b %b", one, tuple(inv)(one), (tuple(inv))(one));
      $display("p = %b %d", tpl_1(p), tpl_2(p));
      $display("t3new = %d %d %d", tpl_1(t3new), tpl_2(t3new), tpl_3(t3new));
      $display("t3 equal = %b", t3new == t3back);
      $display("t8 = %d %d", tpl_1(t8), tpl_8(t8));
      match {.a1, .a2, .a3, .a4, .a5, .a6, .a7, {.a8, .a9}} = n8;
      $display("n8 = %d %d %d %d %d %d %d %d %d",
               a1, a2, a3, a4, a5, a6, a7, a8, a9);
      $display("n8 bits = %h", pack(n8));
      Tuple#(UInt#(4), UInt#(4)) tl = tpl_8(n8);
      $display("n8 tpl_7 = %d, tpl_8 = %h, declared tpl_8 = %h",
               tpl_7(n8), pack(tpl_8(n8)), pack(tl));
      match {.b, .u, .x} = r;
      $display("r = %b %d %b", b, u, x);
      $display("r eq = %b", r == tuple(False, 5, 3'b101));
      $finish(0);
   endrule

endmodule
