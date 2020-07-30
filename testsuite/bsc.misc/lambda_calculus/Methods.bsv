typedef UInt#(51) T;

interface Ifc;
   // value method
   method T result();
   // action method
   method Action start(T num1, T num2);
   // actionvalue method
   method ActionValue#(T) start_and_result(T num1, T num2);
endinterface

(* synthesize *)
module sysMethods(Ifc);

   Reg#(T) x <- mkReg(?);
   Reg#(T) y <- mkReg(0);

   rule flip (x > y && y != 0);
       x <= y;
       y <= x;
   endrule

   rule sub if (x <= y && y != 0);
       y <= y - x;
   endrule

   method T result() if (y == 0);
      return x;
   endmethod

   method Action start(T num1, T num2) if (y == 0);
      x <= num1;
      y <= num2;
   endmethod

   method ActionValue#(T) start_and_result(T num1, T num2);
      x <= num1;
      y <= num2;
      return x;
   endmethod

endmodule

