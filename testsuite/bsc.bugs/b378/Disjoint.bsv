import FIFO::*;

(* synthesize *)
module mkTest(Empty); 
    Reg#(Bit#(3)) cnd();  
    mkReg#(4) the_cnd(cnd); 

    Reg#(Bit#(4)) y();
    mkReg#(0) the_y(y);

    rule zug (cnd == 2);
        y <= 4;
    endrule

    rule zig (cnd == 0);
        y <= 2;
    endrule

    rule zag (cnd == 1);
        y <= 1;
    endrule


endmodule: mkTest

