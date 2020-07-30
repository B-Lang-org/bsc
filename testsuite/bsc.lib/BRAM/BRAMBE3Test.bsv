import BRAM::*;
import GetPut::*;
import ClientServer::*;
import StmtFSM::*;
import Clocks::*;

(* synthesize *)
module sysBRAMBE3Test();
   BRAM1PortBE#(Bit#(8), Bit#(64), 8) dut0 <- mkBRAM1BE(True);
   
endmodule

