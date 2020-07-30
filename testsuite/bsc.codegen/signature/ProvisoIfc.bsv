interface IFC#(type ty);
   method Bool m (ty x, ty y);
endinterface

(* synthesize *)
module sysProvisoIfc (IFC#(t)) provisos (Ord#(t));
   method Bool m (t x, t y);
      return x > y;
   endmethod
endmodule

