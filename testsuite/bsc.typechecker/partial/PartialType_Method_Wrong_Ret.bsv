
module mkTest(Reg#(Bool));
   Reg#(Bool) rg <- mkRegU;

   method Bool _write(x);
      action
         rg <= x;
      endaction
   endmethod

   method _read = rg;
endmodule

