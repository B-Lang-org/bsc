interface IFC#(type n);
   method Bool m (Bit#(n) x);
endinterface

(* synthesize *)
module sysPolymorphicMethodArg (IFC#(t));
   method Bool m (Bit#(t) x);
      return x > 10;
   endmethod
endmodule

