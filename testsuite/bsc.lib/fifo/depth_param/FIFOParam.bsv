import FIFO::*;

(* synthesize *)
module mySizedFIFO#(parameter UInt#(32) depth)(FIFO#(Bit#(32)));
   FIFO#(Bit#(32)) f <- mkDepthParamFIFO(depth);
   return(f);
endmodule


(* synthesize *)
module myLSizedFIFO#(parameter UInt#(32) depth)(FIFO#(Bit#(32)));
   FIFO#(Bit#(32)) f <- mkDepthParamLFIFO(depth);
   return(f);
endmodule

(* synthesize *)
module myZeroWidthFIFO#(parameter UInt#(32) depth)(FIFO#(Bit#(0)));
   FIFO#(Bit#(0)) f <- mkDepthParamFIFO(depth);
   return(f);
endmodule

