import List::*;

typedef struct {
  UInt#(10) key;
  Bool      special;
  Bit#(32)  payload;
} Record deriving (Eq, Bits);

function Record rec(UInt#(10) k, Bool s, Bit#(32) p);
   Record r;
   r.key = k;
   r.special = s;
   r.payload = p;
   return r;
endfunction

function Action printRec(Integer i, Record r);
   action
      if (r.special) $write("!!! ");
      $display("%0d: %0d %h", i, r.key, r.payload);
   endaction
endfunction

function Action printGroup(Integer i, List#(Record) rs);
   action
      $display("============= Group %0d =========", i);
      joinActions(zipWith(printRec,upto(1,30),rs));
      $display("=================================");
   endaction
endfunction

function Ordering onKey(Record r1, Record r2);
   return compare(r1.key,r2.key);
endfunction

function Bool equiv(Record r1, Record r2);
   return (r1.key == r2.key && r1.special == r2.special);
endfunction

(* synthesize *)
module sysSortGroupTest();

   List#(Record) rs = Cons(rec( 78, True,  32'h00000000),
		      Cons(rec( 36, False, 32'h11111111),
		      Cons(rec(772, False, 32'h22222222),
		      Cons(rec(771, True,  32'h33333333),
		      Cons(rec(221, True,  32'h44444444),
		      Cons(rec(770, False, 32'h55555555),
		      Cons(rec( 55, True,  32'h66666666),
		      Cons(rec(769, False, 32'h77777777),
		      Cons(rec(255, False, 32'h88888888),
		      Cons(rec( 11, False, 32'h99999999),
		      Cons(rec(309, False, 32'haaaaaaaa),
		      Cons(rec(770, True,  32'hbbbbbbbb),
		      Cons(rec( 99, False, 32'hcccccccc),
		      Cons(rec( 78, False, 32'hdddddddd),
		      Cons(rec(929, True,  32'heeeeeeee),
		      Cons(rec(770, True,  32'hffffffff),
		      Cons(rec(329, False, 32'h00112233),
		      Cons(rec(443, False, 32'h44556677),
		      Cons(rec(  7, False, 32'h8899aabb),
		      Cons(rec(999, False, 32'hccddeeff),
		      Cons(rec(329, False, 32'hdeadbeef),
		      Cons(rec(240, True, 32'hcafef00d),
		      Cons(rec(329, False, 32'hdefac8ed),
		      Cons(rec( 24, False, 32'h2bad2bad),
		      Cons(rec(770, True,  32'h12345678),
		      Cons(rec(123, True,  32'h87654321),
		      Cons(rec(138, False, 32'head2face),
		      Cons(rec(622, True, 32'hb100b100),
		      Cons(rec(929, False, 32'hac1dba5e),
		      Cons(rec(240, False, 32'h1337babe),
		      Nil))))))))))))))))))))))))))))));

   List#(Record) sorted_rs = sortBy(onKey,rs);
   List#(List#(Record)) grouped_rs = groupBy(equiv,sorted_rs);

   Reg#(UInt#(2)) state <- mkReg(0);

   rule incr_state;
      state <= state + 1;
   endrule

   rule print_sorted if (state == 1);
      joinActions(zipWith(printRec,upto(1,30),sorted_rs));
   endrule

   rule print_groups if (state == 2);
      joinActions(zipWith(printGroup,upto(1,30),grouped_rs));
   endrule

   rule done if (state == 3);
      $finish(0);
   endrule

endmodule