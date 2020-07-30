(* synthesize *)
module sysBug791();
  
  match {.a, .b} <- mkTuple();

  rule test;
    $display(a + b);
    $finish(0);
  endrule
  
endmodule

(* synthesize *)
module mkTuple(Tuple2#(Bit#(5), Bit#(5)));

  method fst;
    return 5;
  endmethod
  
  method snd;
    return 10;
  endmethod
endmodule

