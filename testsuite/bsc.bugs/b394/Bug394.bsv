package MkDPSRAM;

import Vector::*;
import RegFile::*;
import DPSRAM::*;
import SyncSRAM::*;
import ClientServer::*;
import GetPut::*;

module mkDesign ();
  
  Tuple2#(SyncSRAMS#(1,16,16),SyncSRAMS#(1,16,16)) tx <- mkDPSRAM(65536);

endmodule: mkDesign 

endpackage: MkDPSRAM
