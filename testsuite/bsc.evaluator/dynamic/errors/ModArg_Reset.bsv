import Clocks :: *;

// A submodule that expects a reset argument
(* synthesize *)
module mkSub_ModArg_Reset(Reset rst_in, Empty ifc);
endmodule

(* synthesize *)
module sysModArg_Reset();

   Reset r1 <- exposeCurrentReset;

   Clock clk <- exposeCurrentClock;
   MakeResetIfc mr <- mkReset(1, True, clk);
   Reset r2 = mr.new_rst;

   Reg#(Bool) b <- mkReg(False);

   Reset r = (b ? r1 : r2);

   let s <- mkSub_ModArg_Reset(r);

endmodule

