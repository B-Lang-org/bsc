function Bit#(to) adjustSize( Bit#(ti) i ) provisos(Add#(ti,to,tx));
   Bit#(tx) bigData = extend(i);
   return (truncate(bigData));
endfunction

module mkMaxTest#(Bit#(n) a, Bit #(m) b)() provisos(Max#(m,n,q));

  Bit#(q) r = adjustSize(a) + adjustSize(b);

  rule test;
    $display(r);
    $finish(0);
  endrule

endmodule

module mkMaxTest2#(Bit#(n) a, Bit#(m) b)() provisos(Max#(m,n,q));

  Bit#(q) s = adjustSize(a) + adjustSize(b);

  let a2 = s;
  
  mkMaxTest(a2,b);

endmodule

    
(* synthesize *)
module mkMaxTest_4_9#(Bit#(4) a, Bit#(9) b)();

  mkMaxTest2(a,b);

endmodule

