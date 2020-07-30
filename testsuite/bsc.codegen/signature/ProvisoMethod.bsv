interface IFC;
   method Bool m (ty x, ty y) provisos (Eq#(ty));
endinterface

(* synthesize *)
module sysProvisoMethod (IFC);
   method Bool m (t x, t y) provisos (Eq#(t));
      return (x == y);
   endmethod
endmodule

