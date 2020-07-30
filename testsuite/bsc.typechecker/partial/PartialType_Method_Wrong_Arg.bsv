
module mkTest(Reg#(Bool));
   Reg#(Bool) rg <- mkRegU;

   method _write(int x);
      action
         rg <= x;
      endaction
   endmethod

   method _read = rg;
endmodule

