export ArithIO(..);
		   
export mkGCD;
export GCDInt;
	     	     
typedef  UInt#(51) GCDInt;
		       
interface ArithIO#(parameter type a);
    method Action setInput(a x1, a x2);
    method Maybe#(a) getOutput;
endinterface: ArithIO
		     
module mkGCD(ArithIO#(GCDInt));
  Reg#(GCDInt) x();
  mkRegU the_x(x);
  Reg#(GCDInt) y();
  mkRegU the_y(y);
  Reg#(Bool) done();
  mkReg#(True) the_done(done);
  rule flip 
   (!done &&  x > y &&  y != 0);
	x <= y; y <= x;
  endrule
  rule stop 
   (!done &&  y == 0); done <= True;
  endrule
  rule sub 
   (!done &&  x <= y &&  y != 0); y <= y - x;
  endrule
  
  method setInput(a, b) if (done);
	     action
	       done <= False; x <= a; y <= b;
	     endaction
  endmethod: setInput
  method getOutput(); return (done ? Valid(x) : Invalid);
  endmethod: getOutput
  
endmodule: mkGCD
		


