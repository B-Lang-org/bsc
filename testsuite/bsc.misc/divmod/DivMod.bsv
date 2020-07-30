import FIFOF::*;

typedef struct { Int#(16) n; Int#(16) d; Int#(16) q; Int#(16) r; } Result
  deriving (Bits);

(* synthesize *)
module sysDivMod();

  Reg#(Int#(16)) n <- mkReg(-20);
  Reg#(Int#(16)) d <- mkReg(-20);
  Reg#(Bool)     failed <- mkReg(False);
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
    $display("BAD: %d * %d + %d != %d", q, d, r, n);
    failed <= True;
  end
  else
    $display("OK:  %d * %d + %d == %d", q, d, r, n);
endrule: check

rule done (n >= 20 && !results.notEmpty);
  if (failed)
    $display("FAILED");
  else
    $display("PASSED");
  $finish(0);
endrule: done

endmodule
