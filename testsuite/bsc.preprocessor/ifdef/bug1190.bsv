`define firstLevel

(* synthesize *)
module test();

`ifdef firstLevel
   Reg#(Bit#(8)) zero <- mkReg(0);
`else
   Reg#(Bit#(8)) nozero <- mkReg(0);
`endif


`ifdef firstLevel
   Reg#(Bit#(8)) first <- mkReg(0);

`ifdef secondLevel
     Reg#(Bit#(8)) second <- mkReg(0);
`else
     Reg#(Bit#(8)) nosecond <- mkReg(0);
`endif

`else
   Reg#(Bit#(8)) nofirst <- mkReg(0);
`endif

endmodule
