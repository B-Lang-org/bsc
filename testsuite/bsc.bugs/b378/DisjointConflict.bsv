import FIFO::*;


//All rules are disjoint due to the enq conflict

(* synthesize *)
module mkCTest(Empty);
    Reg#(Bit#(3)) cnd();
    mkReg#(4) the_cnd(cnd);

    Reg#(Bit#(4)) y();
    mkReg#(0) the_y(y);

    FIFO#(Bit#(4)) z();
    mkFIFO the_z(z);

    rule zag (cnd[1:1]==1);
        y <= 2;
        z.enq(2);
    endrule

    rule zig (cnd[0:0]==1);
        y <= 1;
        z.enq(1);
    endrule

    rule zug (cnd[2:2]==1);
        y <= 4;
        z.enq(4);
    endrule

endmodule: mkCTest
