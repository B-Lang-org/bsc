
module sysSimpleTest();

Reg#(Bit#(20)) a <- mkReg(923984);
Reg#(Bit#(20)) b <- mkReg(395);

Reg#(Bit#(48)) c <- mkReg(83746029473);
Reg#(Bit#(48)) d <- mkReg(668347);

Reg#(Bit#(96)) e <- mkReg(32900384394827463);
Reg#(Bit#(96)) f <- mkReg(883927018473);

Reg#(UInt#(12)) g <- mkReg(473);
Reg#(UInt#(12)) h <- mkReg(66);

Reg#(UInt#(55)) i <- mkReg(612829320823048);
Reg#(UInt#(55)) j <- mkReg(393484736649394);

Reg#(UInt#(71)) k <- mkReg(1029283747300245);
Reg#(UInt#(71)) l <- mkReg(738495);

Reg#(Int#(17)) m <- mkReg(-28320);
Reg#(Int#(17)) n <- mkReg(19483);

Reg#(Int#(38)) o <- mkReg(77362310293);
Reg#(Int#(38)) p <- mkReg(-8392);

Reg#(Int#(128)) q <- mkReg(-129243847020238474293847263749);
Reg#(Int#(128)) r <- mkReg(-2394373293284005527324983);

Reg#(Int#(22)) s <- mkReg(128320);
Reg#(Int#(22)) t <- mkReg(98333);

Reg#(Int#(32)) u <- mkReg(923847384);
Reg#(Int#(32)) v <- mkReg(-1);

Reg#(Int#(45)) w <- mkReg(-3423889347);
Reg#(Int#(45)) x <- mkReg(-3423889347);

Reg#(Int#(99)) y <- mkReg(-4636606101667698306638);
Reg#(Int#(99)) z <- mkReg(662372300238342615234);

function Action check(a dividend, a divisor)
    provisos(Bits#(a,sa), Eq#(a), Arith#(a));
  let q = dividend / divisor;
  let r = dividend % divisor;
  if (((divisor * q) + r) == dividend)
    $display("OK:  %0d * %0d + %0d == %0d", divisor, q, r, dividend);
  else
    $display("BAD: %0d * %0d + %0d != %0d", divisor, q, r, dividend);
endfunction

function Action check_signed(Int#(n) dividend, Int#(n) divisor);
  let q = dividend / divisor;
  let r = dividend % divisor;
  if (((divisor * q) + r) == dividend)
    $display("OK:  %0d * %0d + %0d == %0d", divisor, q, r, dividend);
  else
    $display("BAD: %0d * %0d + %0d != %0d", divisor, q, r, dividend);
endfunction

rule test;
  // check that Integer div/mod and quot/rem work
  Integer ia = -823487234;
  Integer ib = 93248;
  $display("div(%0d,%0d) = %0d", ia, ib, div(ia,ib));
  $display("mod(%0d,%0d) = %0d", ia, ib, mod(ia,ib));
  $display("quot(%0d,%0d) = %0d", ia, ib, quot(ia,ib));
  $display("rem(%0d,%0d) = %0d", ia, ib, rem(ia,ib));
  $display("%0d / %0d = %0d", ia, ib, ia / ib);
  $display("%0d %% %0d = %0d", ia, ib, ia % ib);

  // check / and % for various different types and sizes
  check(a, b);
  check(c, d);
  check(e, f);
  check(g, h);
  check(i, j);
  check(k, l);
  check_signed(m, n);
  check_signed(o, p);
  check_signed(q, r);
  check_signed(s, t);
  check_signed(u, v);
  check_signed(w, x);
  check_signed(y, z);

  $finish(0);
endrule

endmodule
