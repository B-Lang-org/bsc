interface Ifc;
   method Action m(Bool b);
endinterface

(* synthesize *)
module sysCond_MethodArg_Split(Ifc);
   method Action m(Bool b);
      (* split *)
      if (b)
         $display("True");
      else
         $display("False");
   endmethod
endmodule

