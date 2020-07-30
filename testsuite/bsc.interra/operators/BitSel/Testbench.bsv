import Dut::*;
import Input::*;
import List::*;
import Vectors::*;
import Vector::*;

typedef enum {SET,CHECK_EXTRACT,CHECK_CONCAT,DONE} State deriving(Bits,Eq);
(*synthesize, always_ready, always_enabled*)
module mkTestbench(Empty);

 DUT dut <- mkDut;
 Reg#(State) state <- mkReg(SET);
 Reg#(Bit#(9)) cntr <- mkReg(0);
 List#(Inputs) check = toList(get_vector());
 Integer len = List::length(check);
 
rule set(state==SET);
    Inputs tmp = List::select(check,cntr);
    dut.start(tmp.a);
	state<=CHECK_EXTRACT;
 endrule

rule check_ex(state==CHECK_EXTRACT);
     
   Inputs tmp  = List::select(check,cntr);
   Vector#(18,Bool) vec =
cons( dut.ex_crs_1_1 == tmp.ex_crs_1_1,
cons( dut.ex_crs_1_2 == tmp.ex_crs_1_2,
cons( dut.ex_crs_1_3 == tmp.ex_crs_1_3,
cons( dut.ex_crs_2_1 == tmp.ex_crs_2_1,
cons( dut.ex_crs_2_2 == tmp.ex_crs_2_2,
cons( dut.ex_crs_3 == tmp.ex_crs_3,
cons( dut.ex_tch_1_1 == tmp.ex_tch_1_1,
cons( dut.ex_tch_1_2 == tmp.ex_tch_1_2,
cons( dut.ex_tch_1_3 == tmp.ex_tch_1_3,
cons( dut.ex_tch_1_4 == tmp.ex_tch_1_4,
cons( dut.ex_tch_1_5 == tmp.ex_tch_1_5,
cons( dut.ex_tch_1_6 == tmp.ex_tch_1_6,
cons( dut.ex_tch_2_1 == tmp.ex_tch_2_1,
cons( dut.ex_tch_2_2 == tmp.ex_tch_2_2,
cons( dut.ex_tch_2_3 == tmp.ex_tch_2_3,
cons( dut.ex_tch_2_4 == tmp.ex_tch_2_4,
cons( dut.ex_tch_2_5 == tmp.ex_tch_2_5,
cons( dut.ex_tch_2_6 == tmp.ex_tch_2_6,nil))))))))))))))))));

Bit#(18) status = pack(vec);
if(status == 18'b111111111111111111)
   $display("Test %d PASS for BIT_EXTRACT",cntr);
else
   $display("Test %d FAIL for BIT_EXTRACT with Status %b",cntr,status);

state<=CHECK_CONCAT;

endrule


rule check_conc(state==CHECK_CONCAT);
     
   Inputs tmp  = List::select(check,cntr);
   Vector#(7,Bool) vec =
cons( dut.con_crs_1 == tmp.con_crs_1 ,
cons( dut.con_crs_2== tmp.con_crs_2,
cons( dut.con_crs_3== tmp.con_crs_3,
cons( dut.con_tch_1_1== tmp.con_tch_1_1,
cons( dut.con_tch_1_2== tmp.con_tch_1_2,
cons( dut.con_tch_1_3== tmp.con_tch_1_3,
cons( dut.con_tch_1_4== tmp.con_tch_1_4,nil)))))));
 
Bit#(7) status = pack(vec);
 if(status == 7'b1111111)
   $display("Test %d PASS for BIT_CONCAT",cntr);
else
   $display("Test %d FAIL for BIT_CONCAT with Status %b",cntr,status);

state<=DONE;

endrule

rule done(state==DONE);
   if(cntr>=fromInteger(len)) $finish(0);
   else
    cntr <= cntr+1;
	state <= SET;
	
endrule	


endmodule
