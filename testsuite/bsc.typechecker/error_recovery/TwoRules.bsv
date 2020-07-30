module sysTwoRules();
   rule test1;
      int i=16;
      int bad=True;
      $display("Hello ",i);
   endrule
   rule test2;
      int j=12;
      int worse=False;
      $display("world ",j);
   endrule
endmodule
