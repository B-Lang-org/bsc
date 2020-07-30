typedef struct { a field; } S#(type a) deriving(Bits);

//import "BDPI" function Bool my_func (S#(Integer) y);
import "BDPI" function Bool my_func (S#(a) y);

(* synthesize *)
module mkBDPINonBit_ParamNotBitifiable ();
   let x = S { field : 0 };
   rule r;
      $display("%b",my_func(x));
      $finish(0);
   endrule
endmodule
