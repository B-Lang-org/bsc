import BRAM::*;
import GetPut::*;
import ClientServer::*;
import StmtFSM::*;
import Clocks::*;

(* synthesize *)
module sysBRAMBE2Test();
   let cfg = defaultValue ;
   cfg.loadFormat = tagged Hex "bram2.txt" ;
   BRAM1PortBE#(Bit#(8), Bit#(40), 5) dut0 <- mkBRAM1ServerBE(cfg);
   
endmodule

