import Vector::*;
import RegFile::*;

(* synthesize *)
module mkStringConcat2Sub#(parameter String name)(ReadOnly#(Bit#(8)));
  RegFile#(Bit#(4),Bit#(8)) rf <- mkRegFileFullLoad(name + "_file.txt");
  Reg#(Bit#(4)) addr <- mkReg(0);
  method _read = rf.sub(addr);
endmodule

(* synthesize *)
module sysStringConcat2();
  function String n_to_fname(Integer n) = "theAs_" + integerToString(n);
  let names = map(n_to_fname, genVector);
  Vector#(4,ReadOnly#(Bit#(8))) theAs <- mapM(mkStringConcat2Sub, names);

  rule test;
    for(Integer i = 0; i < 4; i = i + 1) begin
        $display("theAs_%0d: %h", i, theAs[i]);
    end
    $finish(0);
  endrule
endmodule

