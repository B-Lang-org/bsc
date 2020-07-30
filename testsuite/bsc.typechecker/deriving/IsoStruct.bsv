
typedef struct { Int#(32) x; } Apples1
           deriving (Arith, Literal);

module sysIsoStruct (Empty);
  rule r;
     Apples1 s = 12;
     s = s + 1;
     $display("x = %d", s.x);
     $finish(0);
  endrule

endmodule

