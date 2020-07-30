package HiddenType;

export mkFoo;

typedef struct {
   Bool a;    // should be 0
   Bit#(2) b; // should be 10
   Bit#(4) c; // should be 1010
} Hidden
  deriving (Eq, Bits);		 
		
module mkFoo(Empty);
   
  rule test;
    Hidden foo = ?;
    $display("a: %b", foo.a);
    $display("b: %b", foo.b);
    $display("c: %b", foo.c);
    $display("foo: %b", foo); 
    $finish(0);
  endrule

endmodule

endpackage
 	     
