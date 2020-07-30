import RegFile::*;

(* synthesize *)
module sysRegFileLoadBinIndexError(Empty);
  RegFile#(Bit#(2), Bit#(4)) rf  <- mkRegFileLoadBin("data.txt", 3, 0);
endmodule


