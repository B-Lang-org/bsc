interface BugIfc;
  method Action test(UInt#(16) arg);
endinterface

interface BugIfc2;
  method ActionValue#(Bool) test();
endinterface

// We should warn about this
import "BVI" Bug =
module vBug (BugIfc);
  default_clock clk(CLK);
  default_reset rst(RST_N);
  method test(VAL) enable(TEST_EN) clocked_by(no_clock);
endmodule

// this one we cannot catch during parsing because noClock is
// an Id defined in the prelude...
import "BVI" Bug2 =
module vBug2 (BugIfc2);
  default_clock clk = noClock;
  no_reset;
  method TEST_OUT test() enable(TEST_EN);
endmodule

// We should warn about this
import "BVI" Bug2 =
module vBug3 (BugIfc2);
  default_clock no_clock;
  no_reset;
  method TEST_OUT test() enable(TEST_EN);
endmodule


(* synthesize *)
module sysBVIActionMethodNoClock();

  BugIfc  b1 <- vBug();
  BugIfc2 b2 <- vBug2();
  BugIfc2 b3 <- vBug3();

  rule r1;
    b1.test(17);
  endrule

  rule r2;
    $display(b2.test());
  endrule

  rule r3;
    $display(b3.test());
  endrule

endmodule
