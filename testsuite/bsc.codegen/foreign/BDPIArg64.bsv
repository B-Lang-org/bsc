import "BDPI" function ActionValue#(Bit#(64)) func64 (Bit#(64) x);

(*synthesize*)
module mkBDPIArg64();

    Reg#(Bit#(64)) r64 <- mkReg(64'hdead_beef_7fff_fffd);
    Reg#(UInt#(16)) count <- mkReg(0);

    rule r;
        let x <- func64(r64);
        r64 <= x;

	count <= count + 1;
	if (count >= 100)
            $finish(0);
    endrule

endmodule
