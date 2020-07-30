interface Ifc;
   interface SubIfc s;
endinterface  

interface SubIfc;
   method Action enq;
endinterface

(* synthesize *)
module mkTest (Ifc);
   Reg#(Bool) enq <- mkRegU;

   interface SubIfc s;
      method Action enq;
         enq <= True;
      endmethod
   endinterface
endmodule

