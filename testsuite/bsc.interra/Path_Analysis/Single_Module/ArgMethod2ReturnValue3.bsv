//This case creates a pair of cross coupled NAND gates.
//Cycle from Argument of a method to its return Value.
//Cycle is created through the use of two different rules
//Should report an error with -verilog flag

package ArgMethod2ReturnValue3;

interface Inout;
  method Action nandgate (Bool in1, Bool in2);
endinterface


(* synthesize *)
module mkArgMethod2ReturnValue3 (Inout);
  
  RWire #(Bool) temp1();
  mkRWire the_temp1(temp1);
      
  RWire #(Bool) temp2();
  mkRWire the_temp2(temp2);
  
  RWire #(Bool) inp1();
  mkRWire the_inp1(inp1);
      
  RWire #(Bool) inp2();
  mkRWire the_inp2(inp2);
  
  rule gate1;
      Bool i1 = unJust (inp1.wget);
      Bool i2 = unJust (temp2.wget);
      temp1.wset (i1 && i2);
  endrule

  rule gate2;
      Bool i1 = unJust (inp2.wget);
      Bool i2 = unJust (temp1.wget);
      temp2.wset (i1 && i2);
  endrule
      
  
  method Action nandgate (in1, in2);
      inp1.wset (in1);
      inp2.wset (in2);
  endmethod

endmodule

endpackage

