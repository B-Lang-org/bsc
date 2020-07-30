interface Ifc;
  method Bool read(Clock c);
endinterface

import "BVI" MOD =
module mkMod ( Ifc );
  method Q_OUT read(C);
  schedule read CF read;
endmodule

