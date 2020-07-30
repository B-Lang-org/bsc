interface Test;
  method Bool test;
endinterface

(* synthesize *)
module mkLTEMinusOne(Test);

  Reg#(Int#(21)) r <- mkReg(-1);

  method test = r <= -1;

endmodule
