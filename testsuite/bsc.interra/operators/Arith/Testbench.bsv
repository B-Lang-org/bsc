import Dut::*;
import Input::*;
import List::*;
import Vectors::*;
import Vector::*;

typedef enum {SET,CHECK_SUM,CHECK_DIFF,CHECK_MULT,CHECK_LOGICAL,DONE} State deriving(Bits,Eq);
(*synthesize, always_ready, always_enabled*)
module mkTestbench(Empty);

 DUT dut <- mkDut;
 Reg#(State) state <- mkReg(SET);
 Reg#(Bit#(9)) cntr <- mkReg(0);
 List#(Inputs) check = toList(get_vector());
 Integer len = List::length(check);
 
 rule set(state==SET);
    Inputs tmp = List::select(check,cntr);
    dut.start(tmp.a,tmp.b);
	state<=CHECK_SUM;
 endrule

rule check_sum(state==CHECK_SUM);
     
   Inputs tmp  = List::select(check,cntr);
   Vector#(14,Bool) out = 
cons(dut.sum == tmp.sum,
cons (dut.sum_127 == tmp.sum_127,
cons (dut.sum_126 == tmp.sum_126,
cons (dut.sum_96 == tmp.sum_96,
cons (dut.sum_95 == tmp.sum_95,
cons (dut.sum_94 == tmp.sum_94,
cons (dut.sum_64 == tmp.sum_64,
cons (dut.sum_63 == tmp.sum_63,
cons (dut.sum_62 == tmp.sum_62,
cons (dut.sum_32 == tmp.sum_32,
cons (dut.sum_31 == tmp.sum_31,
cons (dut.sum_30 == tmp.sum_30,
cons (dut.sum_1 == tmp.sum_1,
cons (dut.sum_0 == tmp.sum_0,
nil))))))))))))));


Bit#(14) status = pack(out);
if(status == 14'b11111111111111)
   $display("Test %d PASS for SUMS",cntr);
else
   $display("Test %d FAIL for SUMS with Status %b",cntr,status);

state<=CHECK_DIFF;

endrule

rule check_diff(state==CHECK_DIFF);
     
   Inputs tmp  = List::select(check,cntr);
   Vector#(14,Bool) out = 
cons (dut.diff == tmp.diff,
cons (dut.diff_127 == tmp.diff_127,
cons (dut.diff_126 == tmp.diff_126,
cons (dut.diff_96 == tmp.diff_96,
cons (dut.diff_95 == tmp.diff_95,
cons (dut.diff_94 == tmp.diff_94,
cons (dut.diff_64 == tmp.diff_64,
cons (dut.diff_63 == tmp.diff_63,
cons (dut.diff_62 == tmp.diff_62,
cons (dut.diff_32 == tmp.diff_32,
cons (dut.diff_31 == tmp.diff_31,
cons (dut.diff_30 == tmp.diff_30,
cons (dut.diff_1 == tmp.diff_1,
cons (dut.diff_0 == tmp.diff_0, 
nil))))))))))))));


Bit#(14) status = pack(out);
if(status == 14'b11111111111111)
   $display("Test %d PASS for DIFFS",cntr);
else
   $display("Test %d FAIL for DIFFS with Status %b",cntr,status);

state<=CHECK_MULT;

endrule

rule check_mult(state==CHECK_MULT);
     
   Inputs tmp  = List::select(check,cntr);
   Vector#(14,Bool) out = 
cons (dut.mult == tmp.mult,
cons (dut.mult_127 == tmp.mult_127,
cons (dut.mult_126 == tmp.mult_126,
cons (dut.mult_96 == tmp.mult_96,
cons (dut.mult_95 == tmp.mult_95,
cons (dut.mult_94 == tmp.mult_94,
cons (dut.mult_64 == tmp.mult_64,
cons (dut.mult_63 == tmp.mult_63,
cons (dut.mult_62 == tmp.mult_62,
cons (dut.mult_32 == tmp.mult_32,
cons (dut.mult_31 == tmp.mult_31,
cons (dut.mult_30 == tmp.mult_30,
cons (dut.mult_1 == tmp.mult_1,
cons (dut.mult_0 == tmp.mult_0,
nil))))))))))))));

Bit#(14) status = pack(out);
if(status == 14'b11111111111111)
   $display("Test %d PASS for MULTS",cntr);
else
   $display("Test %d FAIL for MULTS with Status %b ",cntr,status);

state<=CHECK_LOGICAL;

endrule


rule check_logical(state==CHECK_LOGICAL);
     
   Inputs tmp  = List::select(check,cntr);

if(dut.logical==tmp.logical)
   $display("Test %d PASS for LOGICAL",cntr);
else
   $display("Test %d FAIL for LOGICAL",cntr);

state<=DONE;

endrule

rule done(state==DONE);
   if(cntr>=fromInteger(len)) $finish(0);
   else
    cntr <= cntr+1;
	state <= SET;
	
endrule	

endmodule
