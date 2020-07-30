interface IFC;
   method Action a();
   method Action b();
   method Action c();
endinterface

(* synthesize *)
module mkEx1 (IFC);

  Reg#(Bool) r1 <- mkRegU;
  Reg#(Bool) r2 <- mkRegU;
  Reg#(Bool) r3 <- mkRegU;

  method Action a ;
     r1 <= r2 ;
  endmethod

  method Action b ;
     r2 <= r3 ;
  endmethod

  method Action c ;
     r3 <= True ;
  endmethod
endmodule
