// This function takes a 10 bit dividend and a 5 bit divisor
// and returns a tuple consisting of overflow,remainder
// and quotient.Due to the nature of the algorithm used for 
// dividing 2 numbers it cannot be parameterized.

function Tuple3#(Bit#(1), Bit#(5),Bit#(5)) funcQR(Bit#(10) a ,Bit#(5) b);

Bit#(1) overflow;
if(a[9:5] >= b)
 begin  
   overflow = 1;
 end
else
 begin
   overflow = 0;
 end

Bit#(6)  znotB = zeroExtend(primInv(b) + 1);
Bit#(6) compare1 = zeroExtend(a[8:4]) + znotB;

Bit#(5) partRem1;
Bit#(1)  q4;
if(compare1[5] == 1) 
 begin
    partRem1 =  compare1[4:0];
    q4 = 1;
 end
else
 begin 
   partRem1 =  a[8:4];
   q4 = 0;
 end

                      
Bit#(5) partRem1_Abit = { partRem1[3:0] , a[3]};
compare1 = zeroExtend(partRem1_Abit[4:0]) + znotB;

Bit#(5) partRem2;
Bit#(1)  q3;
if(compare1[5] == 1)
 begin
   partRem2 =  compare1[4:0];
   q3 = 1;
 end
else
 begin  
   partRem2 = partRem1_Abit[4:0];
   q3 = 0;
 end



Bit#(5) partRem2_Abit = { partRem2[3:0] , a[2]};
compare1 = zeroExtend(partRem2_Abit[4:0]) + znotB;

Bit#(5) partRem3;
Bit#(1)  q2;
if(compare1[5] == 1)
 begin
   partRem3 =   compare1[4:0];
   q2 = 1;
 end
else
 begin  
   partRem3 = partRem2_Abit[4:0];
   q2 = 0;
 end

Bit#(5) partRem3_Abit = { partRem3[3:0] , a[1]};
compare1 = zeroExtend(partRem3_Abit[4:0]) + znotB;

Bit#(5) partRem4;
Bit#(1)  q1;
if(compare1[5] == 1)
 begin
   partRem4 = compare1[4:0];
   q1  = 1;
 end
else
 begin  
   partRem4 = partRem3_Abit[4:0];
   q1 = 0;
 end

Bit#(5) partRem4_Abit = { partRem4[3:0], a[0]};
compare1 = zeroExtend(partRem4_Abit[4:0]) + znotB;

Bit#(5) remainder;
Bit#(1) q0;
if(compare1[5] == 1)
 begin
   remainder = compare1[4:0];
   q0 = 1;
 end
else
 begin  
   remainder = partRem4_Abit[4:0];
   q0 = 0;
 end
Bit#(5) quotient={ q4, q3, q2, q1, q0};
Tuple3#(Bit#(1), Bit#(5),Bit#(5)) result;
result = tuple3(overflow,remainder,quotient);
return result;

endfunction: funcQR


