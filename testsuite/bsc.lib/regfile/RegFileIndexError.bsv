import RegFile::*;

(* synthesize *)
module sysRegFileIndexError(Empty);
  RegFile#(Bit#(2), Bit#(4)) rf  <- mkRegFile(3, 0);
endmodule


