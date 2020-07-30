interface IFC;
  method Bool doStuff (Bool p);
endinterface

(* synthesize *)
module mkTest2 (IFC);
  Reg#(Bool) y <- mkReg (False);

  method doStuff (Bool p) if (y);
    return y;
  endmethod
endmodule 
