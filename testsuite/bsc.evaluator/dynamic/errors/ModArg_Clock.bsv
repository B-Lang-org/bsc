import Clocks :: *;

// A submodule that expects a clock argument
(* synthesize *)
module mkSub_ModArg_Clock(Clock clk_in, Empty ifc);
endmodule

(* synthesize *)
module sysModArg_Clock();
   Clock c1 <- exposeCurrentClock;
   Clock c2 <- mkAbsoluteClock(10, 20);

   Reg#(Bool) b <- mkReg(False);

   Clock c = (b ? c1 : c2);

   let s <- mkSub_ModArg_Clock(c);

endmodule

