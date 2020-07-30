import Vector::*;

typedef struct { Bit#(5)              field1;
                 Bit#(6)              field2;
                 Vector#(15, Bit#(8)) field3;
                 Bool                 field4;
               } MyStruct
  deriving (Bits);

import "BDPI" function MyStruct modify_struct(MyStruct x);

(* synthesize *)
module mkBDPIPassingStruct ();
   rule r;
      Vector#(15, Bit#(8)) v = replicate(0);
      v[0] = 72;
      v[1] = 101;
      v[2] = 108;
      v[3] = 108;
      v[4] = 111;
      v[5] = 32;
      v[6] = 119;
      v[7] = 111;
      v[8] = 114;
      v[9] = 108;
      v[10] = 100;

      MyStruct s = MyStruct { field1:3, field2:5, field3:v, field4:True };

      MyStruct s2 = modify_struct(s);

      $display("field1: %b", s2.field1);
      $display("field2: %b", s2.field2);
      for (UInt#(4) i = 0; i <= 10; i = i + 1)
        $display("field3[%d]: %c", i, s2.field3[i]);
      $display("field4: %b", s2.field4);

      $finish(0);
   endrule
endmodule
