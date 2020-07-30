import Vector::*;

function UInt#(32) pswitch(Vector#(n,Bool) v, UInt#(32) a, UInt#(32) b);
   UInt#(32) result1 = a;
   UInt#(32) result2 = b;
   for(Integer i = 0; i < valueof(n); i = i + 1)
      begin
	 if(v[i]) begin
	    let temp = result1;
	    result1 = result2;
	    result2 = temp;
	 end
      end
   return(result1);
endfunction

function a readReg(Reg#(a) r);
   return(r);
endfunction

typedef 64 Size;

(* synthesize *)
module mkParitySwitch2();

   Vector#(Size, Reg#(Bool)) regs <- replicateM(mkRegU);
   Vector#(Size, Bool) data = map(readReg, regs);
   
   Reg#(UInt#(32)) a <- mkRegU;
   Reg#(UInt#(32)) b <- mkRegU;
   Reg#(UInt#(32)) c <- mkRegU;
   
   rule test;
      c <= pswitch(data,a,b);
   endrule
   
endmodule
