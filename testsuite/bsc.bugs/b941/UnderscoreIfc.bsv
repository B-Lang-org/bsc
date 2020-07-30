interface Ifc;
   method Bool m();
   method ActionValue#(Bool) m2();
endinterface

interface Ifc_;
   method Bit#(8) m3();
endinterface

(* synthesize *)
module sysUnderscoreIfc (Ifc);
endmodule
