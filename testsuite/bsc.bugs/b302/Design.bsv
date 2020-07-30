package Design;


//here type1 is of type Bit#(10)
//type2 is of type Bit#(5)

interface Design_IFC #(parameter type type1,parameter type type2);
    method Bit#(11) result(type1 a,type2 b);
endinterface:  Design_IFC


function Bit#(11) funcQR(Bit#(10) a ,Bit#(5) b);
Bit#(1)  overflow;
Bit#(5)  notB;
Bit#(6)  znotB;
Bit#(6)  za;
Bit#(6)  cmp1;
Bit# (5) partRem1;
Bit#(1)  q4;
Bit#(5) partRem1_Abit;
Bit#(6) zPartRem1; 
Bit#(6) compare1;

Bit#(6)  cmp2;
Bit#(5) partRem2;
Bit#(1)  q3;
Bit#(5) partRem2_Abit;
Bit#(6) zPartRem2; 
Bit#(6) compare2;

Bit#(6)  cmp3;
Bit#(5) partRem3;
Bit#(1)  q2;
Bit#(5) partRem3_Abit;
Bit#(6) zPartRem3; 
Bit#(6) compare3;

Bit#(6)  cmp4;
Bit# (5) partRem4;
Bit#(1)  q1;
Bit#(5) partRem4_Abit;
Bit#(6) zPartRem4; 
Bit#(6) compare4;
Bit#(1) q0;
Bit#(6) cmp5;
Bit#(6) compare5;
Bit#(5) remainder;
Bit#(5) quotient;
Bit#(11) result;

      if(a[9:5] >= b)
        begin  
           overflow = 1;
        end
      else
        begin
           overflow = 0;
        end

      notB =  ~ b ;
      compare1 = {0,a[8:4]} + zeroExtend( notB ) + 1 ;

      if(compare1[5:5] == 1) begin
         partRem1 =  compare1[4:0];
         q4 = 1;
      end
      else begin
         partRem1 =  a[8:4];
         q4 = 0;
      end // else: !if(compare1[5:5] == 1)
      
      partRem1_Abit = { partRem1[3:0] , a[3:3]};
      compare2 = {0,partRem1_Abit[4:0]} + zeroExtend( notB ) + 'd1 ;
      

      if(compare2[5:5] == 1) begin
         partRem2 =  compare2[4:0];
         q3 =   1;
         end
      else  begin
         partRem2 = partRem1_Abit[4:0];
         q3 = 0;
      end // else: !if(compare2[5:5] == 1)
      

      partRem2_Abit = { partRem2[3:0] , a[2:2]};
      compare3 = {0,partRem2_Abit[4:0]} + zeroExtend( notB ) + 'd1 ;
      

      if(compare3[5:5] == 1) begin
         partRem3 =   compare3[4:0];
         q2 =   1;
      end // if (compare3[5:5] == 1)
      else  begin
         partRem3 = partRem2_Abit[4:0];
         q2 = 0;
      end // else: !if(compare3[5:5] == 1)
      
      partRem3_Abit = { partRem3[3:0] , a[1:1]};
      compare4 = {0,partRem3_Abit[4:0]} + zeroExtend( notB ) + 'd1;
      


      if(compare4[5:5] == 1) begin
         partRem4 = compare4[4:0];
         q1 =  1;
      end // if (compare4[5:5] == 1)
      else  begin
         partRem4 = partRem3_Abit[4:0];
         q1 =  0;
      end // else: !if(compare4[5:5] == 1)
     

      partRem4_Abit = { partRem4[3:0], a[0:0]};
      compare5 = {0,partRem4_Abit[4:0]} + zeroExtend( notB ) + 'd1 ;
      

      if(compare5[5:5] == 1) begin
         remainder = compare5[4:0];
         q0 = 1;
      end // if (compare5[5:5] == 1)
      else  begin
         remainder = partRem4_Abit[4:0];
         q0 = 0 ;
      end // else: !if(compare5[5:5] == 1)
      
      quotient = { q4, q3, q2, q1, q0};
      result = {overflow , remainder, quotient};

      return result;
      
endfunction: funcQR

(* synthesize,
       always_ready ,
       always_enabled,
       CLK = "clk",
       RST_N = "reset" 
*)

module mkDesign (Design_IFC #(Bit#(10),Bit#(5)));

   method Bit#(11) result(Bit#(10) a,Bit#(5) b);
     result = funcQR(a, b);
   endmethod: result
endmodule: mkDesign
                 
endpackage: Design



