interface IFC;
  method ActionValue#(Bool) doStuff (Bool p);
endinterface

(* synthesize *)
module mkTest (IFC);
  Reg#(Bool) y <- mkReg (False);

  method ActionValue#(Bool) doStuff (Bool p) if (y);
    return y;
  endmethod
endmodule 
