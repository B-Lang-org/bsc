interface Ifc;
   interface SubIfc s;
endinterface

interface SubIfc;
   method Bool deq;
endinterface

(* synthesize *)
module mkTest (Ifc);
   Wire#(Bool) deq <- mkDWire(False);

   interface SubIfc s;
     method Bool deq if (deq);
        return True;
     endmethod
   endinterface
endmodule

