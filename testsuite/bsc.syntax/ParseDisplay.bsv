Bit#(5) bar;
bar = 12;

Integer z;
z = 19;

Action foo;
foo = action
         Integer x;
         x = 5; 
         $display(bar, z, 8'h12, 12, x);
      endaction;
