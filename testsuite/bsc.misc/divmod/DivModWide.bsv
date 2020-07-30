import FIFOF::*;

typedef struct { Int#(128) n; Int#(128) d; Int#(128) q; Int#(128) r; } Result
  deriving (Bits);

(* synthesize *)
module sysDivModWide();

  Reg#(Int#(128)) n <- mkReg(-20);
  Reg#(Int#(128)) d <- mkReg(-20);
  Reg#(Bool)      failed <- mkReg(False);
  FIFOF#(Result)  results <- mkFIFOF;

rule incr;
  if ((d > 0) && ((n == 0) || (d == abs(n))))
  begin
    let newN = n + 1;
    n <= newN;
    d <= (newN == 0) ? -1 : -abs(newN);
  end
  else
    d <= (d == -1) ? 1 : (d + 1);
endrule: incr

rule compute (n <= 20);
  results.enq(Result { n: n, d: d, q: (n / d), r: (n % d) });
endrule: compute

rule check;
  match tagged Result { n: .n, d: .d, q: .q, r: .r } = results.first;
  results.deq;
  if (((q * d) + r) != n)
  begin
    $display("BAD: %0d * %0d + %0d != %0d", q, d, r, n);
    failed <= True;
  end
  else
    $display("OK:  %0d * %0d + %0d == %0d", q, d, r, n);
endrule: check

rule done (n >= 20 && !results.notEmpty);
  if (failed)
    $display("FAILED");
  else
    $display("PASSED");
  $finish(0);
endrule: done

endmodule
