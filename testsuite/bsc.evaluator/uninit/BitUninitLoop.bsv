typedef struct {
  Bit#(5) a;
  Integer b;
} MyStruct;

(* synthesize *)
module mkBitUninitLoop();
   MyStruct s;
   s.b = 0;
   
   rule test;
      for (Integer i = 0; i < 5; i = i + 1) begin
	 $display(s.a);
      end
   endrule
   
endmodule

