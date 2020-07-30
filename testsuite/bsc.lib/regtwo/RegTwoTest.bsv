// basic RegTwo test - see if the right method call "wins"
import RegTwo::*;
(* synthesize *)
module sysRegTwoTest(Empty);

  Reg#(Bit#(2)) done();
  mkReg#(0) i_done(done);

  RegTwo#(Bit#(2)) test();
  mkRegTwo#(0) i_test(test);

  rule start(done == 0);
     test.setB(2);
     test.setA(1);
     done <= 1;
  endrule

  rule check(done == 1);
     $display("Result: %0d", test.get);
     if(test.get == 1)
       $display("Pass");
     else
       $display("Fail");
     done <= 2 ;
  endrule

  rule exit(done == 2) ;
     $finish(0);
  endrule
endmodule
