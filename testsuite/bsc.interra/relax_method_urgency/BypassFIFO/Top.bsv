import GetPut::*;
import FIFO::*;
import Design::*;

(* synthesize *)
module mkTop(Get#(Bit#(5)));

Reg#(Bit#(5)) count <- mkReg(4);
// Instantiating the Design
FIFO#(Bit#(5)) dut <- mkDesign;

// enq FIFO in rule
rule inp;
	dut.enq(count);
	count <= count + 2;
    $display($time, "\tData enqued = %d", count);
endrule

return(fifoToGet(dut));

endmodule
