interface Ifc;
   method ActionValue#(Bit#(64)) m();
endinterface

(* synthesize *)
module sysMethodReturn_ATaskValue(Ifc);
   method m() = $time;
endmodule

