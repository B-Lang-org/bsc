interface Ifc;
   method Bit#(16) m();
endinterface

(* synthesize *)
module sysMethodValue_Const (Ifc);
   method m = 17;
endmodule

