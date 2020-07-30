
module mkTest(Reg#(Bool));
   Reg#(Bool) rg <- mkRegU;

   method Action _write(x);
      rg <= x;
   endmethod

   method _read = rg;
endmodule

