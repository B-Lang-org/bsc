
import GCD::*;

// The following is an attribute that tells the compiler to generate
// separate code for mkTbGCD
(* synthesize *)
module mkTbGCD(Empty);
  // The instantiation of GCD block is called the_gcd.
  // The interface to this block is called gcd and is of type ArithIO_IFC
  ArithIO_IFC#(NumTyp) gcd <- mkGCD;

  // Registers used to generate numbers to feed to the GCD block   
  Reg#(NumTyp) count1();
  mkReg#(19) the_count1(count1);
  Reg#(NumTyp) count2();
  mkReg#(5) the_count2(count2);
  
  // Register to hold the GCD result
  Reg#(NumTyp) tbresult();
  mkReg#(0) the_tbresult(tbresult);

  rule rule1SendInput (True);
      gcd.start(count1, count2);
      count1 <= count1 + 3;
      count2 <= count2 + 2;
  endrule: rule1SendInput
  rule rule2GetResult (True); 
      tbresult <= gcd.result;
  endrule: rule2GetResult

  rule exit(count1 > 100);
    $finish(0);
  endrule

endmodule: mkTbGCD

