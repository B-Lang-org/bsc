import RegFile::*;

(* synthesize *)
module sysRegFileWCFLoadBinIndexError(Empty);
  RegFile#(Bit#(2), Bit#(4)) rf  <- mkRegFileWCFLoadBin("data.txt", 3, 0);
endmodule


