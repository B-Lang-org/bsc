import Vector::*;

typedef union tagged {
   Vector#(n, Bool) T1;
   Bool             T2;
   } State#(type n) deriving (Bits, Eq);

module mkStateReg (Reg#(State#(n)));
   Reg#(State#(n)) rg <- mkRegU;
   return rg;
endmodule

