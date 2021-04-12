
typedef union tagged {
    void Yellow;
    Bit #(1) Red;
} RgbColorTagged  deriving (Eq, Bits, Bounded);

(* synthesize *)
module mkTestbench ();
     RgbColorTagged color = unpack(0);
     Integer bitty;
     case (pack(color))
       0: bitty = 0;
       default: bitty = 1;
     endcase
     error(integerToString(bitty));
endmodule : mkTestbench
