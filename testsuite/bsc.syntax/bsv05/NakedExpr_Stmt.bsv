module mkTest (Empty);
  int x = 1;
  int y = 2;
  x == y ? mkSub1 : mkSub2;
endmodule

module mkSub1 (Empty);
endmodule

module mkSub2 (Empty);
endmodule
