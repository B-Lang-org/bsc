interface Test;
  method Bool test;
endinterface

(* synthesize *)
module mkSLTZero(Test);

  Reg#(Int#(21)) r <- mkReg(-1);

  method test = r < 0;

endmodule
