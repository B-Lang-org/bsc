import Counter :: *;

(* synthesize *)
module sysCounterTest();
   Counter#(16) counter <- mkCounter(0);

   Reg#(UInt#(8)) t <- mkReg(0);

   rule do_stuff;
      case (t)
         3:   counter.inc(100);
         5:   $display("%d", counter.value());
         7:   counter.dec(50);
         10:  $display("%d", counter.value());
         11:  counter.up();
         12:  counter.up();
         13:  counter.up();
         15:  $display("%d", counter.value());
         20:  begin
                 counter.down();
                 counter.inc(5);
              end
         25:  $display("%d", counter.value());
         30:  begin
                 counter.setC(70);
                 counter.inc(10);
                 counter.dec(5);
              end
         35:  $display("%d", counter.value());
         50:  counter.clear();
         55:  $display("%d", counter.value());
         60:  counter.setF(150);
         65:  $display("%d", counter.value());
         100: $finish(0);
      endcase
      t <= t + 1;
   endrule
endmodule