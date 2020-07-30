interface IFC;
   method Action a();
   method Action c();
endinterface

(* synthesize *)
module mkEx2 (IFC);

  Reg#(Bool) r1 <- mkRegU;
  Reg#(Bool) r2 <- mkRegU;
  Reg#(Bool) r3 <- mkRegU;

  rule b ;
     r2 <= r3 ;
  endrule

  method Action a ;
     r1 <= r2 ;
  endmethod

  method Action c ;
     r3 <= True ;
  endmethod
endmodule
