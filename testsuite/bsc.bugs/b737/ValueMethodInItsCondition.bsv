interface Ifc;
   method Bool deq;
endinterface

(* synthesize *)
module mkTest (Ifc);
   Wire#(Bool) deq <- mkDWire(False);

   method Bool deq if (deq);
      return True;
   endmethod
endmodule

