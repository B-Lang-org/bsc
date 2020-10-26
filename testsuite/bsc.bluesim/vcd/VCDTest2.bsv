(* synthesize *)
module sysVCDTest2 ();
   Reg#(UInt#(32)) counter <- mkReg(0);
   Mixer mid1 <- mkVCDTest2_Mid;
   Mixer mid2 <- mkVCDTest2_Mid;

   rule count;
     counter <= counter + 1;
   endrule: count

   rule startVCD (counter == 2);
     $dumpfile("test2.vcd");
     $dumplimit(100000);
     $dumpvars;
   endrule: startVCD

   rule flushVCD (counter == 50);
     $dumpflush;
   endrule: flushVCD

   rule stopVCD (counter == 100);
     $dumpoff;
   endrule: stopVCD

   rule checkpoint1 (counter == 110);
     $dumpall;
   endrule: checkpoint1

   rule restartVCD (counter == 125);
     $dumpon;
   endrule: restartVCD

   rule checkpoint2 (counter == 150);
     $dumpall;
   endrule: checkpoint2

   rule done (counter >= 200);
     $finish(0);
   endrule: done

   rule doStuff (counter < 200);
     mid1.in({pack(counter),'0,pack(counter)}, mid2.out());
     mid2.in(mid1.out(), {'0,pack(counter),pack(counter),32'h0});
   endrule: doStuff

endmodule

interface Mixer;
  method Action in(Bit#(128) a, Bit#(128) b);
  method Bit#(128) out();
endinterface: Mixer

(* synthesize *)
module mkVCDTest2_Mid (Mixer);

  Mixer sub1 <- mkVCDTest2_Sub;
  Mixer sub2 <- mkVCDTest2_Sub;

  method Bit#(128) out();
    return sub1.out() ^ sub2.out();
  endmethod: out

  method Action in(Bit#(128) a, Bit#(128) b);
  action
    sub1.in({b[63:0],a[127:64]}, {a[63:0],b[127:64]});
    sub2.in({a[127:64],b[127:64]}, {b[63:0],a[63:0]});
  endaction
  endmethod: in

endmodule

(* synthesize *)
module mkVCDTest2_Sub (Mixer);

  Reg#(Bit#(128)) x <- mkReg(0);
  Reg#(Bit#(128)) y <- mkReg(0);

  rule rotate;
    x <= {x[0], x[127:1]};
    y <= {y[126:0], y[127]};
  endrule: rotate

  method Bit#(128) out();
    return x ^ y;
  endmethod: out

  method Action in(Bit#(128) a, Bit#(128) b);
  action
    x <= y ^ a;
    y <= x ^ b;
  endaction
  endmethod: in

endmodule
