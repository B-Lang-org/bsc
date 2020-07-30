interface IFC;
   method Action a();
   method Action c();
   method Action e();
endinterface

(* synthesize *)
module mkEx3 (IFC);

  Reg#(Bool) r1 <- mkRegU;
  Reg#(Bool) r2 <- mkRegU;
  Reg#(Bool) r3 <- mkRegU;
  Reg#(Bool) r4 <- mkRegU;
  Reg#(Bool) r5 <- mkRegU;

  rule b ;
     r2 <= r3 ;
  endrule

  rule d ;
     r4 <= r5 ;
  endrule

  method Action a ;
     r1 <= r2 ;
  endmethod

  method Action c ;
     r3 <= r4 ;
  endmethod

  method Action e ;
     r5 <= True ;
  endmethod

endmodule
