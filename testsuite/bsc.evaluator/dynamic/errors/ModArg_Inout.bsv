// A submodule that expects an inout argument
(* synthesize *)
module mkSub_ModArg_Inout(Inout#(Bool) io_in, Empty ifc);
endmodule

(* synthesize *)
module sysModArg_Inout(Inout#(Bool) io1, Inout#(Bool) io2, Empty ifc);

   Reg#(Bool) b <- mkReg(False);

   Inout#(Bool) io = (b ? io1 : io2);

   let s <- mkSub_ModArg_Inout(io);

endmodule

