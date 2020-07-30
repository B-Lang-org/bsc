import Vector::*;

module mkMod();
   Vector#(8,Reg#(Bool)) pipe <- replicate(mkRegU);
endmodule
