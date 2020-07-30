//////////////////////////////////////////////////////////////////////
/*
This package has the following arithmetic modules:
1. Pipelined multipliers: mult_W1W2W3, mult_W5W6W7.
2. Adder/Subtractor: mkAddSub
3. Multiplication by 181, adding 128 and shifting the result right by 8:
   mkConstMult 
*/
package ArithModules;

import ConfigReg ::*;

////////////////////////////////////////////////////////////////////////
interface Mult_IFC#(type x);
    method Action multiply (Int#(x) input_data, Int#(2) select);
    method Int#(32) result;
endinterface: Mult_IFC


(* synthesize *)
module mult_W1W2W3 (Mult_IFC#(16) );
   Mult_IFC#(16) mult();
   mult_W5W6W7_W1W2W3#(0) i_mult(mult);
   return (mult);  
endmodule 
    
(* synthesize *)
module mult_W5W6W7 (Mult_IFC#(16) );
   Mult_IFC#(16) mult();
   mult_W5W6W7_W1W2W3#(1) i_mult(mult);
   return (mult);   
endmodule 


//////////////////////Pipelined Multiplier//////////////////////////////////////

//multtype = 0 => Multiply input by W1, W2 or W3 depending on the select signal. 
// If select signal is 3, shift the input by 11 bits.
//multtype = 1 => Multiply input by W4, W5 or W6 depending on the select signal. 
// If select signal is 3, shift the input by 11 bits.

module mult_W5W6W7_W1W2W3#(bit multtype) (Mult_IFC#(x))
   provisos (Add#(x,y,32));
    
    Reg#(Int#(32)) add_1();
    mkConfigReg#(0) the_add_1(add_1);
    Reg#(Int#(32)) add_2();
    mkConfigReg#(0) the_add_2(add_2);
    Reg#(Int#(32)) add_3();
    mkConfigReg#(0) the_add_3(add_3);
    Reg#(Int#(32)) result_in();
    mkReg#(0) the_result_in(result_in);
   
    rule always_fire (True);
        result_in <= add_1 + add_2 + add_3;
    endrule
    
    method Action multiply (input_data,select);
      Int#(32) in1 = signExtend (input_data);
      Int#(32) a, b, c, d, e, f;
        case (select)
           0 : begin
                 a  = (multtype==1) ? in1 << 10: in1 <<11 ;
                 b = in1;
                 c = in1 << 9;
                 d = in1 << 3;
                 e = (multtype ==1) ? in1 << 6 : in1 << 8;
                 f = (multtype ==1) ? 0 : in1 << 4;
                 end
           1 : begin
                 a  = (multtype==1) ? in1 << 10: in1 <<11 ;
		         b = (in1 << 2);
                 c  = (multtype==1) ? in1 << 6 : in1 <<9 ;
				 d = (in1 << 4);
                 e = (multtype ==1) ? 0 : in1 << 6;
                 f = (multtype ==1) ? 0 : in1 << 5;
                 end
           2'b10  :begin
                 a  = (multtype==1) ? in1 << 9: in1 << 11 ;
                 b  = (multtype==1) ? in1: 0 ;
                 c  = (multtype==1) ? in1 << 5: in1 << 8 ;
                 d  = (multtype==1) ? in1 << 2: in1 << 3 ;
                 e  = (multtype==1) ? in1 << 4: in1 << 6 ;
                 f = (multtype ==1) ? 0 : in1 << 5;
                 end
           default  :begin
                 a = in1 << 11;
                 b = 0;
                 c = 0;
                 d = 0;
                 e = 0;
                 f = 0;
                 end
         endcase
         add_1 <= a+b;
         add_2 <= c+d;
         add_3 <= e+f;
     endmethod 

     method result ();
         result = result_in;
     endmethod
endmodule : mult_W5W6W7_W1W2W3

/////////////////////////////////////////////////////////////////////
interface AddSub_IFC;
    method Int#(32) start (Int#(32) a, Int#(32) b, Bool c);
endinterface: AddSub_IFC

(* synthesize *)
// Adder or subtractor
module mkAddSub(AddSub_IFC);
    method start (a,b,c);
       Int#(32) b_in = c ? b : (~b+1);
       return (a+b_in);
    endmethod : start
endmodule : mkAddSub


///////////////////////////////////////////////////////////////////////
interface ConstMult_IFC;
    method Int#(32) start (Int#(32) a);
endinterface: ConstMult_IFC

(* synthesize *)
// implements start = (181*a + 128) >> 8
module mkConstMult(ConstMult_IFC);
    method start (a);
       Int#(32) b1 = 181*a + 128;
       Int#(32) b2 = b1 >> 8;
       return (b2);
    endmethod : start
endmodule : mkConstMult

endpackage : ArithModules
