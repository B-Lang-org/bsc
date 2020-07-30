import List::*;

interface Design_IFC ;
    method Action shift_and_mult(Bit#(5) multiplicand,Bit#(8) multiplier,Bit#(1)
load);
    method Bit#(1) done();
    method Bit#(12) product();
endinterface: Design_IFC 

(* always_ready, always_enabled *)
module mkDesign (Design_IFC);

 Reg#(Bit#(12)) regeAQ <- mkReg(0);
 Reg#(Bit#(4)) regB <- mkReg(0);
 Reg#(Bit#(1)) productsign <- mkReg(0);
 Reg#(Bit#(1)) add_shiftb <- mkReg(0);
 Reg#(Bit#(4)) sequencecount <- mkReg(0);
 Reg#(Bit#(1)) done_reg <- mkReg(0);
 Reg#(Bit#(1)) enable <- mkReg(0);

 method  shift_and_mult(multiplicand,multiplier,load);
  action
   begin
     Bit#(5) x;  
     Bit#(5) y;  
/*
     if (load == 1) 
       begin
         productsign <= multiplicand[4] ^ multiplier[7]; 
         regeAQ <= {5'b00000,multiplier[6:0]};
         regB <= multiplicand[3:0];
         add_shiftb <= multiplier[0];
         sequencecount <= 6;
         done_reg <= 0;
         enable <= 1;
       end
     else if ((add_shiftb == 1) && (enable == 1)) 
       begin
         y = {1'b0,regeAQ[10:7]};
         x = regB._read + y;
         regeAQ <= {x,regeAQ[6:0]};
         add_shiftb <= 0;
       end
     else if ((done_reg != 1) && (enable == 1)) 
       begin
         regeAQ <= regeAQ >> 1;
         if (regeAQ[1:1] == 1) 
           add_shiftb <= 1 ;
         else 
           add_shiftb <= 0;
         if (sequencecount == 0) 
           done_reg <= 1 ;
         else 
           sequencecount <= sequencecount -1;
         if (sequencecount == 0) 
           enable <= 0 ;
         else 
           enable <= 1;
       end
     else 
       begin
         done_reg <= done_reg;
       end
*/
   end
  endaction

 endmethod: shift_and_mult

 method  done();
    done = done_reg;
 endmethod: done

 method  product();
    product = {productsign,regeAQ[10:0]};
 endmethod: product

endmodule: mkDesign
