package TestIVec1;

import IVec1::*;
import ListN::*;
import Connectable::*;

instance Connectable#(ivt#(a), ivt#(b))
   provisos (Connectable#(a,b), IVec#(n,ivt), IVec#(n,ivt));
   module mkConnection#(ivt#(a) iva, ivt#(b) ivb)(Empty);
      mkConnection(fromIVec(iva), fromIVec(ivb));
   endmodule
endinstance

endpackage
