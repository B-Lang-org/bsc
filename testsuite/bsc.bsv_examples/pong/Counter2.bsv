// Counter with start value, and upper and lower limits
// possible to increment and decrement
		   
interface Counter#(parameter type a);
    method a get;
    method Action set(a x1);
    method Action inc_dec(Bool x1); // increment if True, otherwise decrement
endinterface: Counter
		     
module mkCounter#(parameter a lower, parameter a start, parameter a upper)(Counter#(a))
  provisos (Bits #(a,b) , Eq #(a), Literal #(a), Arith #(a));
  Reg#(a) value_reg();
  mkReg#(start) the_value_reg(value_reg);
  method a get(); 
    return value_reg;
  endmethod: get
  method Action set(a x1); 
    action  
      value_reg <= x1;
    endaction
  endmethod: set
  method Action inc_dec(Bool up);
    action
      value_reg <= (up && (value_reg != upper)) ? (value_reg + 1) : 
                   ((!up && (value_reg != lower)) ? 
                   (value_reg - 1) : 
                   (value_reg));
    endaction 
  endmethod: inc_dec
  
endmodule: mkCounter
		    


