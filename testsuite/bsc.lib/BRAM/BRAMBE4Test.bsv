import BRAM::*;
import GetPut::*;
import ClientServer::*;
import StmtFSM::*;
import Clocks::*;

(* synthesize *)
module sysBRAMBE4Test();
   BRAM1PortBE#(Bit#(8), Bit#(9), 1) dut0 <- mkBRAM1BELoad(True, "bram2.txt");
   
endmodule

