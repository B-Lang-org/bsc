package Division;
// This function takes a 12 bit dividend and a 10 bit divisor
// and returns and quotient.Due to the nature of the algorithm used for 
// dividing 2 numbers it cannot be parameterized.

interface Division_IFC;
  method Bit#(12) div_func(Bit#(24) dividend,Bit#(12) divisor);
endinterface: Division_IFC

function Tuple3#(Bit#(1), Bit#(12),Bit#(12)) funcQR(Bit#(24) a ,Bit#(12) b);
Bit#(24) tmp_a;

if (a[23] == 1)
  tmp_a = ~a + 1;
else
  tmp_a = a;

Bit#(1) overflow;
if(tmp_a[23:12] >= b)
 begin  
   overflow = 1;
 end
else
 begin
   overflow = 0;
 end

Bit#(13)  znotB = zeroExtend(~b + 1);
Bit#(13) compare1 = zeroExtend(tmp_a[22:11]) + znotB;

Bit#(12) partRem1;
Bit#(1)  q11;
if(compare1[12] == 1) 
 begin
    partRem1 =  compare1[11:0];
    q11 = 1;
 end
else
 begin 
   partRem1 =  tmp_a[22:11];
   q11 = 0;
 end

Bit#(12) partRem1_Abit = { partRem1[10:0] , tmp_a[10]};
compare1 = zeroExtend(partRem1_Abit[11:0]) + znotB;
Bit#(12) partRem2;
Bit#(1)  q10;
if(compare1[12] == 1)
 begin
   partRem2 =  compare1[11:0];
   q10 = 1;
 end
else
 begin  
   partRem2 = partRem1_Abit[11:0];
   q10 = 0;
 end

Bit#(12) partRem2_Abit = { partRem2[10:0] , tmp_a[9]};
compare1 = zeroExtend(partRem2_Abit[11:0]) + znotB;
Bit#(12) partRem3;
Bit#(1)  q9;
if(compare1[12] == 1)
 begin
   partRem3 =  compare1[11:0];
   q9 = 1;
 end
else
 begin  
   partRem3 = partRem2_Abit[11:0];
   q9 = 0;
 end

Bit#(12) partRem3_Abit = { partRem3[10:0] , tmp_a[8]};
compare1 = zeroExtend(partRem3_Abit[11:0]) + znotB;
Bit#(12) partRem4;
Bit#(1)  q8;
if(compare1[12] == 1)
 begin
   partRem4 =  compare1[11:0];
   q8 = 1;
 end
else
 begin  
   partRem4 = partRem3_Abit[11:0];
   q8 = 0;
 end

Bit#(12) partRem4_Abit = { partRem4[10:0] , tmp_a[7]};
compare1 = zeroExtend(partRem4_Abit[11:0]) + znotB;
Bit#(12) partRem5;
Bit#(1)  q7;
if(compare1[12] == 1)
 begin
   partRem5 =  compare1[11:0];
   q7 = 1;
 end
else
 begin  
   partRem5 = partRem4_Abit[11:0];
   q7 = 0;
 end

Bit#(12) partRem5_Abit = { partRem5[10:0] , tmp_a[6]};
compare1 = zeroExtend(partRem5_Abit[11:0]) + znotB;
Bit#(12) partRem6;
Bit#(1)  q6;
if(compare1[12] == 1)
 begin
   partRem6 =  compare1[11:0];
   q6 = 1;
 end
else
 begin  
   partRem6 = partRem5_Abit[11:0];
   q6 = 0;
 end

Bit#(12) partRem6_Abit = { partRem6[10:0] , tmp_a[5]};
compare1 = zeroExtend(partRem6_Abit[11:0]) + znotB;
Bit#(12) partRem7;
Bit#(1)  q5;
if(compare1[12] == 1)
 begin
   partRem7 =  compare1[11:0];
   q5 = 1;
 end
else
 begin  
   partRem7 = partRem6_Abit[11:0];
   q5 = 0;
 end

Bit#(12) partRem7_Abit = { partRem7[10:0] , tmp_a[4]};
compare1 = zeroExtend(partRem7_Abit[11:0]) + znotB;
Bit#(12) partRem8;
Bit#(1)  q4;
if(compare1[12] == 1)
 begin
   partRem8 =  compare1[11:0];
   q4 = 1;
 end
else
 begin  
   partRem8 = partRem7_Abit[11:0];
   q4 = 0;
 end

Bit#(12) partRem8_Abit = { partRem8[10:0] , tmp_a[3]};
compare1 = zeroExtend(partRem8_Abit[11:0]) + znotB;
Bit#(12) partRem9;
Bit#(1)  q3;
if(compare1[12] == 1)
 begin
   partRem9 =  compare1[11:0];
   q3 = 1;
 end
else
 begin  
   partRem9 = partRem8_Abit[11:0];
   q3 = 0;
 end

Bit#(12) partRem9_Abit = { partRem9[10:0] , tmp_a[2]};
compare1 = zeroExtend(partRem9_Abit[11:0]) + znotB;
Bit#(12) partRem10;
Bit#(1)  q2;
if(compare1[12] == 1)
 begin
   partRem10 =  compare1[11:0];
   q2 = 1;
 end
else
 begin  
   partRem10 = partRem9_Abit[11:0];
   q2 = 0;
 end

Bit#(12) partRem10_Abit = { partRem10[10:0] , tmp_a[1]};
compare1 = zeroExtend(partRem10_Abit[11:0]) + znotB;
Bit#(12) partRem11;
Bit#(1)  q1;
if(compare1[12] == 1)
 begin
   partRem11 =  compare1[11:0];
   q1 = 1;
 end
else
 begin  
   partRem11 = partRem10_Abit[11:0];
   q1 = 0;
 end

Bit#(12) partRem11_Abit = { partRem11[10:0] , tmp_a[0]};
compare1 = zeroExtend(partRem11_Abit[11:0]) + znotB;
Bit#(12) remainder;
Bit#(1)  q0;
if(compare1[12] == 1)
 begin
   remainder =  compare1[11:0];
   q0 = 1;
 end
else
 begin  
   remainder = partRem11_Abit[11:0];
   q0 = 0;
 end


Bit#(12) quotient={ q11,q10,q9,q8,q7,q6,q5,q4, q3, q2, q1, q0};
Tuple3#(Bit#(1), Bit#(12),Bit#(12)) result;
result = tuple3(overflow,remainder,quotient);
return result;

endfunction: funcQR

module  mkDiv(Division_IFC);

method Bit#(12) div_func(Bit#(24) dividend,Bit#(12) divisor);
  Bit#(12) tmp_func;
  Tuple3#(Bit#(1), Bit#(12),Bit#(12)) res = funcQR(dividend,divisor);
  match {.overflow,.remainder,.quotient} = res;
  if (remainder >= zeroExtend(divisor[9:1]))
    tmp_func = quotient + 1;
  else
    tmp_func = quotient ;

  if (dividend[23] == 1)
    div_func = ~tmp_func + 1;
  else
    div_func = tmp_func ;
endmethod: div_func

endmodule : mkDiv
endpackage : Division
