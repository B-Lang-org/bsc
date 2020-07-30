
interface Ifc;
  interface Inout#(Bit#(32)) io_ifc;
endinterface

import "BVI" 
module mkInoutPropsBVI (Ifc);
    ifc_inout io_ifc(IO);
endmodule

(*synthesize*)
module sysInoutProps_BVIIfc (Ifc);
  Ifc i <- mkInoutPropsBVI;
  return i;
endmodule

