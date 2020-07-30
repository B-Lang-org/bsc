package ArithModules;

import ConfigReg ::*;

////////////////////////////////////////////////////////////////////////
interface Mult #(type x);
    method Action multiply (Bit #(x) input_data, Bit #(2) select);
    method Bit #(32) result;
endinterface: Mult


(* synthesize *)
module mult_W1W2W3 (Mult #(16));
    Mult #(16) mult <- mult_W5W6W7_W1W2W3 (0);
    return (mult);
endmodule 
    
(* synthesize *)
module mult_W5W6W7 (Mult #(16));
    Mult #(16) mult <- mult_W5W6W7_W1W2W3 (1);
    return (mult);
endmodule 


//multtype = 0 for W1W2W3
module mult_W5W6W7_W1W2W3 #(Bit #(1) multtype) (Mult #(x)) provisos (Add#(x,y,32));
    
    Reg #(Bit #(32)) add_1 <- mkConfigReg (0);
    Reg #(Bit #(32)) add_2 <- mkConfigReg (0);
    Reg #(Bit #(32)) add_3 <- mkConfigReg (0);
    Reg #(Bit #(32)) result_in <- mkReg (0);

   
    rule always_fire (True);
        result_in <= add_1 + add_2 + add_3;
    endrule
    
    method multiply (input_data,select);
    action
      Bit #(32) in1 = signExtend (input_data);
      Bit #(32) a = 0, b, c, d, e, f;
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
           2  :begin
                 a  = (multtype==1) ? in1 << 9: in1 << 11 ;
                 b  = (multtype==1) ? in1: 0 ;
                 c  = (multtype==1) ? in1 << 5: in1 << 8 ;
                 d  = (multtype==1) ? in1 << 2: in1 << 3 ;
                 e  = (multtype==1) ? in1 << 4: in1 << 6 ;
                 f = (multtype ==1) ? 0 : in1 << 5;
                 end
           default :begin
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
      endaction
     endmethod 

     method result ();
         result = result_in;
     endmethod
endmodule : mult_W5W6W7_W1W2W3

/////////////////////////////////////////////////////////////////////



interface AddSub_IFC;
    method Bit #(32) start (Bit #(32) a, Bit #(32) b, Bool c);
endinterface: AddSub_IFC

(* synthesize *)
module mkAddSub(AddSub_IFC);
    method start (a,b,c);
       Bit #(32) b_in = c ? b : (~b+1);
       return (a+b_in);
    endmethod : start
endmodule : mkAddSub


///////////////////////////////////////////////////////////////////////
                 
interface ConstMult_IFC;
    method Bit #(32) start (Bit #(32) a);
endinterface: ConstMult_IFC

(* synthesize *)
module mkConstMult(ConstMult_IFC);
    method start (a);
       Bit #(32) b1 = 181*a + 128;
       Int #(32) b2 = unpack (b1) >> 8;
       return (pack (b2));
    endmethod : start
endmodule : mkConstMult


endpackage : ArithModules
