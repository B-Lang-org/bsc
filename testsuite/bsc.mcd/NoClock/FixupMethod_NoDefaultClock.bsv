// complicate the return value data type

typedef struct {
  Int#(8) f1;
  Bool f2;
} S deriving (Eq, Bits);

interface Ifc;
   method ActionValue#(Maybe#(S)) m();
endinterface

(* synthesize, no_default_clock *)
module sysFixupMethod_NoDefaultClock(Ifc);
   method ActionValue#(Maybe#(S)) m();
      $display("Hello");
      return (tagged Valid (S { f1: 2, f2: True }));
   endmethod
endmodule
