interface IFC;
   method Action a();
   method Action c();
endinterface

(* synthesize *)
module mkEx4 (IFC);

  Reg#(Bool) r1 <- mkRegU;
  Reg#(Bool) r2 <- mkRegU;
  Reg#(Bool) r3 <- mkRegU;
  Reg#(Bool) r4 <- mkRegU;
  Reg#(Bool) r5 <- mkRegU;
  Reg#(Bool) r6 <- mkRegU;
  Reg#(Bool) r7 <- mkRegU;

  rule b1 ;
     r2 <= r3 ;
  endrule

  rule b2 ;
     r3 <= r4 ;
  endrule

  rule b3 ;
     r4 <= r5 ;
  endrule

  rule b4 ;
     r5 <= r6 ;
  endrule

  rule b5 ;
     r6 <= r7 ;
  endrule

  method Action a ;
     r1 <= r2 ;
  endmethod

  method Action c ;
     r7 <= True ;
  endmethod
endmodule
