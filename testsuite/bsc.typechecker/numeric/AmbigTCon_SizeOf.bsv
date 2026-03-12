
// Not an error, since nothing actually demands the Bits context.
// A Bits error would arise from actually trying to define an implementation.
module sysAmbigTCon_SizeOf (Reg#(Bit#(SizeOf#(t))));
endmodule
