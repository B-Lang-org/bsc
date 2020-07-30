interface ResetOut;
   interface Reset rst;
endinterface

(* synthesize *)
module sysEUndetReset3(ResetOut ifc);
  interface rst = ?;
endmodule

