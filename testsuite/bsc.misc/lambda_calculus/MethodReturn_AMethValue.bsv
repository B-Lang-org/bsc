
interface Ifc;
   method ActionValue#(Bool) m();
endinterface

(* synthesize *)
module mkMethodReturn_AMethValue_Sub(Ifc);
   method ActionValue#(Bool) m();
      return True;
   endmethod
endmodule

(* synthesize *)
module sysMethodReturn_AMethValue(Ifc);
   Ifc s <- mkMethodReturn_AMethValue_Sub;
   method m() = s.m();
endmodule

