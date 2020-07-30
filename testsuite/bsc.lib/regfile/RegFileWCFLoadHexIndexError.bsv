import RegFile::*;

(* synthesize *)
module sysRegFileWCFLoadHexIndexError(Empty);
  RegFile#(Bit#(2), Bit#(4)) rf  <- mkRegFileWCFLoadHex("data.txt", 3, 0);
endmodule


