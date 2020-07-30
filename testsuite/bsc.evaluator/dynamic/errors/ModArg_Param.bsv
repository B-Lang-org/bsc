// A submodule that expects a parameter argument
(* synthesize *)
module mkSub_ModArg_Param#(parameter Bool b)();
endmodule

(* synthesize *)
module sysModArg_Param();

   Reg#(Bool) b <- mkReg(False);

   let s <- mkSub_ModArg_Param(b);

endmodule

