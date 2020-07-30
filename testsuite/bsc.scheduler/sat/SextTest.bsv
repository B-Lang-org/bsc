import Vector::*;

typedef 4 Width;
typedef 11 Width2;

typedef  UInt#(Width) Data_t;
typedef  UInt#(Width2) Data2_t;


//  A roll your own version of sign extend
function Data2_t sx (Data_t x);
   Data2_t z = 0;
   Bit#(1) m = msb(x);
   Vector#(Width, Bit#(1)) xv = unpack(pack(x));
   Vector#(TSub#(Width2, Width), Bit#(1)) mx = replicate(m);
   Vector#(Width2, Bit#(1)) zz = append(xv,mx);
   z = unpack(pack(zz));
   return z;
endfunction

(*synthesize*)
module sysSextTest();
   Reg#(Data_t) ua <- mkReg(0);
   Reg#(Data2_t) ub <- mkReg(0);
   Reg#(Data_t) uc <- mkReg(0);
   

   // predicates for aa and ab are disjoint
   
   
   rule aa (signExtend(ua) == ub);
      uc <= uc + 1;
   endrule

   rule ab (sx(ua) != ub);
      uc <= uc + 2;
   endrule

   //  expect warning that bb can never fire
   rule  bb (ua != 0 );
      uc <= uc + 3;
   endrule

endmodule
