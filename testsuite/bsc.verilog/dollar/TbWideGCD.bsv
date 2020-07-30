import WideGCD::*;

// The following is an attribute that tells the compiler to generate
// separate code for mkTbGCD
(* synthesize *)
module sysTbWideGCD(Empty);
  // The instantiation of GCD block is called the_gcd.
  // The interface to this block is called gcd and is of type ArithIO_IFC
  ArithIO_IFC#(NumTyp) gcd();
  mkWideGCD the_gcd(gcd);

  ArithIO_IFCken#(NumTyp) the <- mkWideGCDken();
  // Registers used to generate numbers to feed to the GCD block   
  Reg#(NumTyp) count1();
  mkReg#(19) the_count1(count1);
  Reg#(NumTyp) count2();
  mkReg#(5) the_count2(count2);


  //these identifiers designed to test the name collisions
  Reg#(NumTyp) the_count1_D_IN <- mkReg(123);
  Reg#(NumTyp) the_count1_1D_IN <- mkReg(123);
  Reg#(NumTyp) the_count1_2D_IN <- mkReg(123);
  Reg#(NumTyp) the_count1_EN <- mkReg(123);
  Reg#(NumTyp) the_count1_1EN <- mkReg(123);
  Reg#(NumTyp) the_count1_2EN <- mkReg(123);
  Reg#(NumTyp) the_gcd_EN_start <- mkReg(123);
  Reg#(NumTyp) the_gcd_RDY_start <- mkReg(123);
  Reg#(NumTyp) the_gcd_result <- mkReg(123);
  Reg#(NumTyp) the_gcd_RDY_result <- mkReg(123);
  Reg#(NumTyp) the_gcd_start_num1 <- mkReg(123);
  Reg#(NumTyp) the_gcd_1start_num1 <- mkReg(123);
  Reg#(NumTyp) start_num1 <- mkReg(123);

  rule rule1SendInput (True);
      $display("computing gcd(%d,%d)", count1, count2);
      gcd.start(count1, count2);
      count1 <= count1 + 3;
      count2 <= count2 + 2;
  endrule: rule1SendInput

  rule rule2GetResult (True); 
      $display("result = %d", gcd.result);
  endrule: rule2GetResult

  rule exit(count1 > 100);
    $finish(0);
  endrule

endmodule: sysTbWideGCD

interface ArithIO_IFCken #(type aTyp); // aTyp is a paramerized type
    method Action gcd_start(aTyp num1, aTyp num2);
endinterface: ArithIO_IFCken

// The following is an attribute that tells the compiler to generate
// separate code for mkGCD
(* synthesize *)
module mkWideGCDken(ArithIO_IFCken#(NumTyp)); // here aTyp is defined to be type Int
    Reg#(NumTyp) x();  // x is the interface to the register
    mkReg#(?) the_x(x); // the_x is the register instance

    Reg#(NumTyp) y();
    mkReg#(0) the_y(y);

    rule flip (x > y && y != 0);
        x <= y;
        y <= x;
    endrule

    rule sub (x <= y && y != 0);
        y <= y - x;
    endrule

    method Action gcd_start(NumTyp num1, NumTyp num2) if (y == 0);
        action
            x <= num1;
            y <= num2;
        endaction
    endmethod: gcd_start

endmodule: mkWideGCDken

// the following code taken from bug 982

// ----------------------------------

(* synthesize *)
module mkTestInput#(Bool odd_name, Bool odd_name2_x) ();
   FOO odd <- mkFoo2;

   // compiles, but name-clash
   rule r;
      $display(odd.name);
      $display(odd.name2(True));
   endrule

endmodule

interface FOO;
   method Bool name();
   method Bool name2(Bool x);
endinterface

(* synthesize *)
module mkFoo2 (FOO);
   method name = False;
   method name2 (x);
      return !x;
   endmethod
endmodule

//----------------------------------
interface BAR;
   method Bool odd_name();
endinterface

(* synthesize *)
module mkTestMethod2 (BAR);
   method odd_name = True;
endmodule

(* synthesize *)
module mkTestMethod (BAR);
   FOO3 odd <- mkFoo3;

   rule r;
      $display(odd.name);
   endrule

   method odd_name = True;
endmodule

interface FOO3;
   method Bool name();
endinterface

(* synthesize *)
module mkFoo3 (FOO3);
   method name = False;
endmodule

