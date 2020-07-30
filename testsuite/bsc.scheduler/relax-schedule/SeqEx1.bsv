interface IFC;
   method Action a();
   method Action b();
endinterface

(* synthesize *)
module mkSeqEx1 (IFC);

  Reg#(Bit#(8)) r1 <- mkRegU;
  Reg#(Bool) r2 <- mkRegU;
  
  RWire#(Bool) rw1 <- mkRWire;
  RWire#(Bool) rw2 <- mkRWire;

  rule c (rw1.wget != Invalid);
    r1 <= r1 + 2;
  endrule

  (* descending_urgency = "c,d" *)
  rule d ;
    r1 <= r1 + 1;
    rw2.wset(True);
  endrule

  method Action a ;
    r2 <= isValid(rw2.wget);
  endmethod

  method Action b ;
    rw1.wset(True);
  endmethod

endmodule


     
