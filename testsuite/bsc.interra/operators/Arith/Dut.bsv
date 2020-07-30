package Dut;
import Vector::*;

interface DUT;
method Action start(Bit#(129) a,Bit#(129) b);
method Bit#(129) sum;
method Bit#(129) diff;
method Bit#(129) mult;

method Bit#(128) sum_127;
method Bit#(127) sum_126;
method Bit#(97) sum_96;
method Bit#(96) sum_95;
method Bit#(95) sum_94;
method Bit#(65) sum_64;
method Bit#(64) sum_63;
method Bit#(63) sum_62;
method Bit#(33) sum_32;
method Bit#(32) sum_31;
method Bit#(31) sum_30;
method Bit#(2) sum_1;
method Bit#(1) sum_0;

method Bit#(128) diff_127;
method Bit#(127) diff_126;
method Bit#(97) diff_96;
method Bit#(96) diff_95;
method Bit#(95) diff_94;
method Bit#(65) diff_64;
method Bit#(64) diff_63;
method Bit#(63) diff_62;
method Bit#(33) diff_32;
method Bit#(32) diff_31;
method Bit#(31) diff_30;
method Bit#(2) diff_1;
method Bit#(1) diff_0;

method Bit#(128) mult_127;
method Bit#(127) mult_126;
method Bit#(97) mult_96;
method Bit#(96) mult_95;
method Bit#(95) mult_94;
method Bit#(65) mult_64;
method Bit#(64) mult_63;
method Bit#(63) mult_62;
method Bit#(33) mult_32;
method Bit#(32) mult_31;
method Bit#(31) mult_30;
method Bit#(2) mult_1;
method Bit#(1) mult_0;

method Bit#(70) logical;
endinterface : DUT


(*synthesize, always_ready, always_enabled*)
module mkDut(DUT);

Reg#(Bit#(129)) a <- mkReg(0);
Reg#(Bit#(129)) b <- mkReg(0);

method Action start(Bit#(129) in1, Bit#(129) in2);
 a <= in1;
 b <= in2;
endmethod

 
method Bit#(129) sum;
sum = (a+b);
endmethod

method Bit#(129) diff;
diff = (a-b);
endmethod

method Bit#(129) mult;
 mult = (a*b);
endmethod 

method Bit#(128) sum_127;
sum_127 = (a[127:0]+b[127:0]);
endmethod

method Bit#(127) sum_126;
sum_126 = (a[126:0]+b[126:0]);
endmethod

method Bit#(97) sum_96;
sum_96 = (a[96:0]+b[96:0]);
endmethod

method Bit#(96) sum_95;
sum_95 = (a[95:0]+b[95:0]);
endmethod

method Bit#(95) sum_94;
 sum_94 = (a[94:0]+b[94:0]);
endmethod

method Bit#(65) sum_64;
sum_64 = (a[64:0]+b[64:0]);
endmethod

method Bit#(64) sum_63;
sum_63 = (a[63:0]+b[63:0]);
endmethod

method Bit#(63) sum_62;
sum_62 = (a[62:0]+b[62:0]);
endmethod

method Bit#(33) sum_32;
sum_32 = (a[32:0]+b[32:0]);
endmethod

method Bit#(32) sum_31;
sum_31 = (a[31:0]+b[31:0]);
endmethod

method Bit#(31) sum_30;
sum_30 = (a[30:0]+b[30:0]);
endmethod

method Bit#(2) sum_1;
sum_1 = (a[1:0]+b[1:0]);
endmethod

method Bit#(1) sum_0;
sum_0 = (a[0]+b[0]);
endmethod


method Bit#(128) diff_127;
diff_127 = (a[127:0]-b[127:0]);
endmethod

method Bit#(127) diff_126;
diff_126 = (a[126:0]-b[126:0]);
endmethod

method Bit#(97) diff_96;
diff_96 = (a[96:0]-b[96:0]);
endmethod

method Bit#(96) diff_95;
diff_95 = (a[95:0]-b[95:0]);
endmethod

method Bit#(95) diff_94;
diff_94 = (a[94:0]-b[94:0]);
endmethod

method Bit#(65) diff_64;
diff_64 = (a[64:0]-b[64:0]);
endmethod

method Bit#(64) diff_63;
diff_63 = (a[63:0]-b[63:0]);
endmethod

method Bit#(63) diff_62;
diff_62 = (a[62:0]-b[62:0]);
endmethod

method Bit#(33) diff_32;
diff_32 = (a[32:0]-b[32:0]);
endmethod

method Bit#(32) diff_31;
diff_31 = (a[31:0]-b[31:0]);
endmethod

method Bit#(31) diff_30;
diff_30 = (a[30:0]-b[30:0]);
endmethod

method Bit#(2) diff_1;
diff_1 = (a[1:0]-b[1:0]);
endmethod


method Bit#(1) diff_0;
diff_0 = (a[0]-b[0]);
endmethod

method Bit#(128) mult_127;
 mult_127 = (a[127:0]*b[127:0]);
endmethod

method Bit#(127) mult_126;
mult_126 = (a[126:0]*b[126:0]);
endmethod

method Bit#(97) mult_96;
mult_96 = (a[96:0]*b[96:0]);
endmethod

method Bit#(96) mult_95;
mult_95 = (a[95:0]*b[95:0]);
endmethod


method Bit#(95) mult_94;
mult_94 = (a[94:0]*b[94:0]);
endmethod


method Bit#(65) mult_64;
mult_64 = (a[64:0]*b[64:0]);
endmethod

method Bit#(64) mult_63;
mult_63 = (a[63:0]*b[63:0]);
endmethod

method Bit#(63) mult_62;
mult_62 = (a[62:0]*b[62:0]);
endmethod

method Bit#(33) mult_32;
mult_32 = (a[32:0]*b[32:0]);
endmethod

method Bit#(32) mult_31;
mult_31 = (a[31:0]*b[31:0]);
endmethod

method Bit#(31) mult_30;
mult_30 = (a[30:0]*b[30:0]);
endmethod

method Bit#(2) mult_1;
mult_1 = (a[1:0]*b[1:0]);
endmethod

method Bit#(1) mult_0;
mult_0 = (a[0]*b[0]);
endmethod
method Bit#(70) logical;
 
 Vector#(70,Bool) vec =  
  cons(a < b,
  cons(a > b,
  cons(a <= b,
  cons(a >= b,
  cons(a == b,
  cons(a[127:0] < b[127:0],
  cons(a[126:0] < b[126:0],
  cons(a[96:0] < b[96:0],
  cons(a[95:0] < b[95:0],
  cons(a[94:0] < b[94:0],
  cons(a[64:0] < b[64:0],
  cons(a[63:0] < b[63:0],
  cons(a[62:0] < b[62:0],
  cons(a[32:0] < b[32:0],
  cons(a[31:0] < b[31:0],
  cons(a[30:0] < b[30:0],
  cons(a[1:0] < b[1:0],
  cons(a[0] < b[0],
  cons(a[127:0] > b[127:0],
  cons(a[126:0] > b[126:0],
  cons(a[96:0] > b[96:0],
  cons(a[95:0] > b[95:0],
  cons(a[94:0] > b[94:0],
  cons(a[64:0] > b[64:0],
  cons(a[63:0] > b[63:0],
  cons(a[62:0] > b[62:0],
  cons(a[32:0] > b[32:0],
  cons(a[31:0] > b[31:0],
  cons(a[30:0] > b[30:0],
  cons(a[1:0] > b[1:0],
  cons(a[0] > b[0],
  cons(a[127:0] <= b[127:0],
  cons(a[126:0] <= b[126:0],
  cons(a[96:0] <= b[96:0],
  cons(a[95:0] <= b[95:0],
  cons(a[94:0] <= b[94:0],
  cons(a[64:0] <= b[64:0],
  cons(a[63:0] <= b[63:0],
  cons(a[62:0] <= b[62:0],
  cons(a[32:0] <= b[32:0],
  cons(a[31:0] <= b[31:0],
  cons(a[30:0] <= b[30:0],
  cons(a[1:0]<= b[1:0],
  cons(a[0] <= b[0],
  cons(a[127:0] >= b[127:0],
  cons(a[126:0] >= b[126:0],
  cons(a[96:0] >= b[96:0],
  cons(a[95:0] >= b[95:0],
  cons(a[94:0] >= b[94:0],
  cons(a[64:0] >= b[64:0],
  cons(a[63:0] >= b[63:0],
  cons(a[62:0] >= b[62:0],
  cons(a[32:0] >= b[32:0],
  cons(a[31:0] >= b[31:0],
  cons(a[30:0] >= b[30:0],
  cons(a[1:0] >= b[1:0],
  cons(a[0] >= b[0],
  cons(a[127:0] == b[127:0],
  cons(a[126:0] == b[126:0],
  cons(a[96:0] == b[96:0],
  cons(a[95:0] == b[95:0],
  cons(a[94:0] == b[94:0],
  cons(a[64:0] == b[64:0],
  cons(a[63:0] == b[63:0],
  cons(a[62:0] == b[62:0],
  cons(a[32:0] == b[32:0],
  cons(a[31:0] == b[31:0],
  cons(a[30:0] == b[30:0],
  cons(a[1:0] == b[1:0],
  cons(a[0] == b[0],nil))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))));

  return (pack(Vector::reverse(vec)));
 
 endmethod

 endmodule

 endpackage
