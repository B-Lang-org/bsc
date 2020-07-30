interface IFC;
  method Action doStuff (Bool p);
endinterface

(* synthesize *)
module mkTest2 (IFC);
  Reg#(Bool) y <- mkReg (False);

  method Action doStuff (Bool p) if (y);
    $display(y);
  endmethod
endmodule 
