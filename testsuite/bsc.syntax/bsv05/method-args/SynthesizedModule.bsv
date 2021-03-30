interface IFC;
   method Bool m1(Bool a1, Bool a2);
   method Bool m2(Bool b1, Bool b2);
   method Bool m3(Bool c1, Bool c2);
   method Bool m4(Bool d1, Bool d2);
endinterface

(* synthesize *)
module sysSynthesizedModule (IFC);
   method Bool m1(Bool a2, Bool a1);
      return (a1 && !a2);
   endmethod
   method Bool m2(Bool b1, Bool a1);
      return (b1 && !a1);
   endmethod
   method Bool m3(Bool b1, Bool c2);
      return (b1 && !c2);
   endmethod
   method Bool m4(Bool d1, Bool d2);
      return (d1 && !d2);
   endmethod
endmodule

