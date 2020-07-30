import RegFile::*;

(* synthesize *)
module sysRegFileWCFIndexError(Empty);
  RegFile#(Bit#(2), Bit#(4)) rf  <- mkRegFileWCF(3, 0);
endmodule


