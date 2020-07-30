// Generate two errors:
//
// (1) Submodule enable is always low () [demotable]
// (2) Action shadowing warning (G0117)
//

interface Ifc;
   method Action m(Bool x);
endinterface

(* synthesize *)
module sysErrors (Ifc);
   Wire#(Bool) w <- mkBypassWire;

   Reg#(Bool) m_x <- mkRegU;

   method m(x) = noAction;
endmodule

