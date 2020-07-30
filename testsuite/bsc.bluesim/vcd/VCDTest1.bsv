(* synthesize *)
module sysVCDTest1 ();
   Reg#(UInt#(8)) counter <- mkReg(0);
   Mixer mid1 <- mkMid;
   Mixer mid2 <- mkMid;

   rule count;
     counter <= counter + 1;
   endrule: count

   rule startVCD (counter == 2);
     $dumpfile("test1.vcd");
     $dumpvars;
   endrule: startVCD

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
     mid2.in(mid1.out(), {'0,pack(counter),pack(counter),8'h0});
   endrule: doStuff

endmodule

interface Mixer;
  method Action in(Bit#(32) a, Bit#(32) b);
  method Bit#(32) out();
endinterface: Mixer

(* synthesize *)
module mkMid (Mixer);

  Mixer sub1 <- mkSub;
  Mixer sub2 <- mkSub;

  method Bit#(32) out();
    return sub1.out() ^ sub2.out();
  endmethod: out

  method Action in(Bit#(32) a, Bit#(32) b);
  action
    sub1.in({b[15:0],a[31:16]}, {a[15:0],b[31:16]});
    sub2.in({a[31:16],b[31:16]}, {b[15:0],a[15:0]});
  endaction
  endmethod: in

endmodule: mkMid

(* synthesize *)
module mkSub (Mixer);

  Reg#(Bit#(32)) x <- mkReg(0);
  Reg#(Bit#(32)) y <- mkReg(0);

  rule rotate;
    x <= {x[0], x[31:1]};
    y <= {y[30:0], y[31]};
  endrule: rotate

  method Bit#(32) out();
    return x ^ y;
  endmethod: out

  method Action in(Bit#(32) a, Bit#(32) b);
  action
    x <= y ^ a;
    y <= x ^ b;
  endaction
  endmethod: in

endmodule: mkSub


