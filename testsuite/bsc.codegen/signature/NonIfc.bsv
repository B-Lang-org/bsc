typedef struct {
    Bool f1;
    Bool f2;
} S deriving (Bits);

(* synthesize *)
module sysNonIfc (S);
   return (S { f1: True, f2: False });
endmodule

