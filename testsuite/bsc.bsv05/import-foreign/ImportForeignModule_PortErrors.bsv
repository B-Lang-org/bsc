interface TestSub;
  interface Reset rst1;
  interface Reset rst2;
  method Action sub(Bit#(1) sub_in);
  interface Clock clk4;
endinterface

interface TestIFC;
  method Bit#(16) out;
  method Bit#(16) out2;
  method Bit#(16) out3;
  method Bit#(16) out4;
  method Bit#(16) in_out(Bit#(16) in, Bit#(16) in5);
  method ActionValue#(Bit#(16)) in_out2(Bit#(16) in0, Bit#(16) in1);
  method Bit#(16) in_out3(Bit#(16) in3, Bit#(16) in4);
  interface Clock clk2;
  method Action action1;
endinterface

import "BVI" Test = module mkTest(TestIFC);
  port PORT1 = 1;
  port PORT1 = 1;
  port PORT2 = 2;
  parameter PORT2 = 3;
  parameter PARAM1 = 2;
  method PARAM1 out();
  method OUTPUT1 out2();
  port OUTPUT1 = 0;
  method GATE1 out2();
  port CLK1 = 4;
  input_clock clk(CLK1, GATE1) <- extractCurrentClock;
  output_clock clk2(CLK2);
  input_reset rst(CLK2) <- extractCurrentReset;
  method EN1 in_out(EN1, EN1);
  method OUTPUT2 in_out2(ARG1, ARG2) enable (EN2) ready(RDY2);
  method EN2 out3 ready(ARG1);
  method ARG2 in_out3(RDY2, OUTPUT2);  
  input_clock clk3(CLK3) <- extractCurrentClock;
  method action1 enable(CLK3) ready(RDY1);
  port RDY1 = 6;
  input_clock clk4(CLK4) = noClock;
  interface TestSub ts;
     output_reset rst1(RST1);
     output_reset rst2(RST2);
     method sub(GATE2) enable(RST1) ready(RST2);
     output_clock clk4(CLK4, GATE2);
  endinterface
  // RST2 only conflicts once (for the input-output overlap)
  port RST2 = 8;
endmodule

