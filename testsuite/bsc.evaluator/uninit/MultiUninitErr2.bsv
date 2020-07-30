typedef struct {
  UInt#(8) red;
  UInt#(8) blue;
  UInt#(8) green;
} RGB deriving(Eq,Bits);		

(* synthesize *)
module mkMultiUninitErr2();
   RGB color;
   color.red = 255;
   
   rule test;
     $display(color);
   endrule

endmodule

 
