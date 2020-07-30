package StepCounter;

interface StepCounter#(parameter type a); 
  // an Action method maps to an enable signal in the generated hardware
  method Action count();
  // a value method maps to an output bus
  method a value();
  // can use the hardware reset or provide a reset method
  // the hardware reset (by library convention) is active low
  // method Action reset();
endinterface

// polymorphic implementation that works for any type that
// can be turned into bits and has arithmetic operations
// defined on it
// a simpler, less flexible implementation could use Bit#(n) 
// and would not require provisos
module mkStepCounter#(a init, a step)(StepCounter#(a)) 
 provisos(Arith#(a), Bits#(a,sa));   
   Reg#(a) counter();
   mkReg#(init) i_counter(counter);
   // mkRegU is an alternative when a reset method is used
   // it starts with an unknown value 
   // and does not use the hardware reset signal

   method count();
     action 
       counter <= counter + step;
     endaction
   endmethod

   method value();
     return(counter);
   endmethod

/*
   method reset();
     action
       counter <= init;
     endaction
   endmethod
*/

endmodule

endpackage 
