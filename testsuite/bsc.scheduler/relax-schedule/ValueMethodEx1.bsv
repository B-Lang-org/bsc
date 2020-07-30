import Counter :: * ;

interface IFC;
   method Action a(Bool x);
   method Bool b();
endinterface

(* synthesize *)
module mkTloop (IFC);

  RWire#(Bool) r1 <- mkRWire;
  RWire#(Bool) r2 <- mkRWire;

  rule copy_it (r1.wget matches tagged Valid .v) ;
     r2.wset(v) ;
  endrule

  method Bool b ;
     return isValid(r2.wget) ;
  endmethod

  method Action a(Bool x) ;
     r1.wset(x) ;
  endmethod

endmodule

(* synthesize *)
module sysTloop(Empty) ;

  Counter#(4) counter <- mkCounter(0) ;
  Reg#(Bool) result <- mkReg(False) ;
  IFC tl <- mkTloop ;

  rule count ;
     counter.inc(1) ;
  endrule
  
  rule quit (counter.value == 5) ;
    $finish(0) ;
  endrule

  rule poke (counter.value == 2) ;
    tl.a(True) ;
  endrule

  rule yell (tl.b) ;
    result <= True ;
  endrule

endmodule
