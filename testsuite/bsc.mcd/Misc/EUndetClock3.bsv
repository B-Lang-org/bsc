interface ClockOut;
   interface Clock clk;
endinterface

(* synthesize *)
module sysEUndetClock3(ClockOut ifc);
  interface clk = ?;
endmodule

