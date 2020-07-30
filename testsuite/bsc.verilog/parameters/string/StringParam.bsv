(* synthesize *)
module mkStringParamSub#(parameter String a)();

  rule test;
    $display(a);
    $finish(0);
  endrule

endmodule

(* synthesize *)
module sysStringParam();

  Empty foo <- mkStringParamSub("Did this work?");
  
endmodule

