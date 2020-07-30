function Action start(Bit#(1) x1, Bit#(2) x2, Bit#(3) x3, Bit#(4) x4,
		      Bit#(5) x5, Bit#(6) x6, Bit#(7) x7, Bit#(8) x8);
   $display(x1, x2, x3, x4, x5, x6, x7, x8);
endfunction

Bit#(1) v1 = 0;
Bit#(2) v2 = 0;
Bit#(3) v3 = 0;
Bit#(4) v4 = 0;
Bit#(5) v5 = 0;
Bit#(6) v6 = 0;
Bit#(7) v7 = 0;
Bit#(8) v8 = 0;


// Missing the 5th argument
Action a = start(v1, v2, v3, v4, v6, v7, v8);

