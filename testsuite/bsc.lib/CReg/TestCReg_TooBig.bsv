
(* synthesize *)
module sysTestCReg_TooBig ();

   Reg#(Bit#(32)) rg[6] <- mkCReg(6, 'hdeadbeef);

endmodule

