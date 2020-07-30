interface IFC;
   method Bool m (Integer x);
endinterface

(* synthesize *)
module sysIntegerMethodArg (IFC);
   method Bool m (Integer x);
      return x > 10;
   endmethod
endmodule

