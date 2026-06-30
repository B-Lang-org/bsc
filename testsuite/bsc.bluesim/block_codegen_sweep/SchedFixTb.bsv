// Instantiates every SchedFix child so each gets a nested per-module C++, which
// the block-codegen check compares against the standalone (-block-codegen)
// form.  Driving is split across mutually-exclusive rules so no two conflicting
// methods of the same instance are called in one rule.
package SchedFixTb;

import SchedFix::*;
import SchedFixMeths::*;

(* synthesize *)
module sysSchedFixTb();
  Reg#(Bit#(8)) n <- mkReg(0);

  // D1
  Acc d1_0 <- mkD1_0; Acc d1_1 <- mkD1_1; Acc d1_2 <- mkD1_2; Acc d1_3 <- mkD1_3;
  // D2
  Arg d2 <- mkD2_args;
  // D3
  M1 d3_1 <- mkD3_1; M2 d3_2 <- mkD3_2; M3 d3_3 <- mkD3_3;
  // D4
  KV d4v <- mkD4_val; KA d4a <- mkD4_act; KAV d4av <- mkD4_av;
  // D5
  Cnt d5_0 <- mkD5_0; Cnt d5_1 <- mkD5_1; Cnt d5_2 <- mkD5_2; Cnt d5_3 <- mkD5_3;
  // D7
  Fwd d7 <- mkD7_fwd;
  // D6
  Many d6 <- mkSchedFixMeths;
  // D8, D9
  Cnt d8 <- mkD8_insts;
  Sink d9 <- mkD9_sink;

  Reg#(Bit#(8)) acc <- mkReg(0);

  rule drive (n < 8);
    d1_0.set(n); d1_1.set(n); d1_2.set(n); d1_3.set(n);
    // d2's four methods all write the same reg, so call only one per cycle
    case (n[1:0])
      0: d2.go0();
      1: d2.go1(n);
      2: d2.go2(n, n);
      default: d2.go3(n, n, n);
    endcase
    d4a.a(n);
    let av <- d4av.av(n);
    d7.inner.set(n);
    d6.load(zeroExtend(n));
    d9.poke(n);
    acc <= acc + av;
    n <= n + 1;
  endrule

  rule done (n == 8);
    Bit#(8) s = d1_0.get() + d1_1.get() + d1_2.get() + d1_3.get() +
                d2.v() +
                d3_1.a() + d3_2.a() + d3_2.b() + d3_3.a() + d3_3.b() + d3_3.c() +
                d4v.v() +
                d5_0.tot() + d5_1.tot() + d5_2.tot() + d5_3.tot() +
                d7.inner.get() + d8.tot() + d9.red() + acc +
                // d6's many wide methods, truncated and summed.  Calling them
                // exercises every (wide) method return port, whose declaration
                // and initialization order is the thing the port-order
                // canonicalization keeps context-independent.
                truncate(d6.wa() + d6.wb() + d6.wc() + d6.wd() + d6.we() +
                         d6.wf() + d6.wg() + d6.wh() + d6.wi() + d6.wj() +
                         d6.wk() + d6.wm() + d6.wq() + d6.wr() + d6.ws() +
                         d6.wt() + d6.wu() + d6.wv() + d6.ww() + d6.wx() +
                         d6.wy() + d6.wz());
    $display("sum=%0d", s);
    $finish(0);
  endrule
endmodule

endpackage
