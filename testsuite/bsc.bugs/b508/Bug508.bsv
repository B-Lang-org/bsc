(* synthesize *)
module sysFoo(Reg#(Bool));
   Bool x = ("abc" == "a");
   method _read();
      return x;
   endmethod
   method _write(y);
      action
      endaction
   endmethod
endmodule