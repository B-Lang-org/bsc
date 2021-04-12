import Vector::*;
import RegFile::*;

interface Multi;
    method int read1(Bit#(4) addr);
    method int read2(Bit#(4) addr);
    method Action write1(Bit#(4) addr, int data);
    method Action write2(Bit#(4) addr, int data);
endinterface

(* synthesize *)
module mkMulti(Multi);
    Vector#(4, RegFile#(Bit#(4), int)) rs <- replicateM(mkRegFileFull());

    Vector#(16, Reg#(Bit#(1))) vec <- replicateM(mkReg(0));

    method int read1(Bit#(4) addr);
        let r = (vec[addr] == 0) ? rs[0]: rs[2];
	return r.sub(addr);
    endmethod

    method int read2(Bit#(4) addr);
        let r = (vec[addr] == 0) ? rs[1]: rs[3];
	return r.sub(addr);
    endmethod

    method Action write1(Bit#(4) addr, int data);
        rs[0].upd(addr, data);
        rs[1].upd(addr, data);
        vec[addr] <= 0;
    endmethod

    method Action write2(Bit#(4) addr, int data);
        rs[2].upd(addr, data);
        rs[3].upd(addr, data);
        vec[addr] <= 1;
    endmethod
endmodule
