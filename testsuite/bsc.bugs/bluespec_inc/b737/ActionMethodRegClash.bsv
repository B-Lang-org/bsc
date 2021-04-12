interface Ifc;
   method Action enq;
endinterface

(* synthesize *)
module mkTest (Ifc);
   Reg#(Bool) enq <- mkRegU;

   method Action enq;
      enq <= True;
   endmethod
endmodule

