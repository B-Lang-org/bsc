
(* synthesize *)
module sysTestCReg_TooSmall ();

   Reg#(Bit#(32)) rg[5] <- mkCReg(-1, 'hdeadbeef);

endmodule

