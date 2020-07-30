import TypeclassDup_Wrapper::*;
import TypeclassDup_Leaf::*;

typedef struct {
} LBusContextP#(numeric type sa, numeric type sd);

interface LBusContextIfcP#(numeric type sa, numeric type sd);
endinterface

instance Expose#(LBusContextP#(sa,sd), LBusContextIfcP#(sa,sd), 2);
   module unburyContext#(LBusContextP#(sa,sd) lbc)(LBusContextIfcP#(sa,sd));
   endmodule
endinstance

