import BRAM::*;
import GetPut::*;
import ClientServer::*;
import StmtFSM::*;
import Clocks::*;

(* synthesize *)
module sysBRAMBE1Test();
   BRAM1PortBE#(Bit#(8), Bit#(10), 1) dut0 <- mkBRAM1ServerBE(defaultValue);
   
endmodule

