import AssertionWires::*;

module [AssertModule] mkTest(Empty);
  AssertionReg a();
  mkAssertionReg#(0) i_a(a);

  AssertionReg b();
  mkAssertionReg#(0) i_b(b);

  Reg#(Bool) flip();
  mkReg#(True) i_flip(flip);
  
  rule do_flip;
    flip <= !flip;
  endrule

  rule go(flip);
    a.set();
  endrule

endmodule

(* synthesize *)
module [Module] mkTestWires(AssertionWires#(2));
  AssertIfc#(Empty, 2) test();
  exposeAssertionWires#(mkTest) i_test(test);

  return(getAssertionWires(test));
endmodule

(* synthesize *)
module [Module] sysAssertionWiresTest(Empty);

  AssertionWires#(2) test_wires();
  mkTestWires i_test_wires(test_wires);

  Reg#(Bit#(5)) counter();
  mkReg#(0) i_counter(counter);

  rule count;
   counter <= counter + 1;
  endrule

  rule wires;
    $display("Time: %0t Wires: %b", $time, test_wires.wires);
  endrule
  
  rule clear(counter == 3);
    $display("Time: %0t Clear", $time);
    test_wires.clear;
  endrule
  
  rule exit (counter == 8); 
    $finish(0);
  endrule

endmodule
