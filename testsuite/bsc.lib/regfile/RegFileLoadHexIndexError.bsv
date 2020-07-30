import RegFile::*;

(* synthesize *)
module sysRegFileLoadHexIndexError(Empty);
  RegFile#(Bit#(2), Bit#(4)) rf  <- mkRegFileLoadHex("data.txt", 3, 0);
endmodule


