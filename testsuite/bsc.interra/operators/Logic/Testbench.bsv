import Dut::*;
import Input::*;
import List::*;
import Vectors::*;
import Vector::*;

typedef enum {SET,CHECK_OR,CHECK_AND,CHECK_INV,CHECK_XOR,CHECK_XNOR,DONE} State deriving(Bits,Eq);
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
	state<=CHECK_OR;
 endrule

rule check_or(state==CHECK_OR);
     
   Inputs tmp  = List::select(check,cntr);
   Vector#(14,Bool) vec =
 cons(dut.bOr==tmp.bOr,
 cons(dut.bOr_127==tmp.bOr_127,
 cons(dut.bOr_126==tmp.bOr_126,
 cons(dut.bOr_96==tmp.bOr_96,
 cons(dut.bOr_95==tmp.bOr_95,
 cons(dut.bOr_94==tmp.bOr_94,
 cons(dut.bOr_64==tmp.bOr_64,
 cons(dut.bOr_63==tmp.bOr_63,
 cons(dut.bOr_62==tmp.bOr_62,
 cons(dut.bOr_32==tmp.bOr_32,
 cons(dut.bOr_31==tmp.bOr_31,
 cons(dut.bOr_30==tmp.bOr_30,
 cons(dut.bOr_1==tmp.bOr_1,
 cons(dut.bOr_0==tmp.bOr_0,nil))))))))))))));

 Bit#(14) status = pack(vec);
 if(status == 14'b11111111111111)
   $display("Test %d PASS for BITWISE_OR",cntr);
else
   $display("Test %d FAIL for BITWISE_OR with Status %b",cntr,status);

state<=CHECK_AND;

endrule


rule check_and(state==CHECK_AND);
     
   Inputs tmp  = List::select(check,cntr);
   Vector#(14,Bool) vec =
 cons(dut.bAnd==tmp.bAnd,
 cons(dut.bAnd_127==tmp.bAnd_127,
 cons(dut.bAnd_126==tmp.bAnd_126,
 cons(dut.bAnd_96==tmp.bAnd_96,
 cons(dut.bAnd_95==tmp.bAnd_95,
 cons(dut.bAnd_94==tmp.bAnd_94,
 cons(dut.bAnd_64==tmp.bAnd_64,
 cons(dut.bAnd_63==tmp.bAnd_63,
 cons(dut.bAnd_62==tmp.bAnd_62,
 cons(dut.bAnd_32==tmp.bAnd_32,
 cons(dut.bAnd_31==tmp.bAnd_31,
 cons(dut.bAnd_30==tmp.bAnd_30,
 cons(dut.bAnd_1==tmp.bAnd_1,
 cons(dut.bAnd_0==tmp.bAnd_0,nil))))))))))))));
 
 Bit#(14) status = pack(vec);
 if(status == 14'b11111111111111)
   $display("Test %d PASS for BITWISE_AND",cntr);
else
   $display("Test %d FAIL for BITWISE_AND with Status %b",cntr,status);

state<=CHECK_INV;

endrule

rule check_inv(state==CHECK_INV);
     
   Inputs tmp  = List::select(check,cntr);
   Vector#(14,Bool) vec =
 cons(dut.bInv==tmp.bInv,
 cons(dut.bInv_127==tmp.bInv_127,
 cons(dut.bInv_126==tmp.bInv_126,
 cons(dut.bInv_96==tmp.bInv_96,
 cons(dut.bInv_95==tmp.bInv_95,
 cons(dut.bInv_94==tmp.bInv_94,
 cons(dut.bInv_64==tmp.bInv_64,
 cons(dut.bInv_63==tmp.bInv_63,
 cons(dut.bInv_62==tmp.bInv_62,
 cons(dut.bInv_32==tmp.bInv_32,
 cons(dut.bInv_31==tmp.bInv_31,
 cons(dut.bInv_30==tmp.bInv_30,
 cons(dut.bInv_1==tmp.bInv_1,
 cons(dut.bInv_0==tmp.bInv_0,nil))))))))))))));
 
 Bit#(14) status = pack(vec);
 if(status == 14'b11111111111111)
   $display("Test %d PASS for BITWISE_INV",cntr);
else
   $display("Test %d FAIL for BITWISE_INV with Status %b",cntr,status);

state<=CHECK_XOR;
endrule

rule check_xor(state==CHECK_XOR);
     
   Inputs tmp  = List::select(check,cntr);
   Vector#(14,Bool) vec =
 cons(dut.bXor==tmp.bXor,
 cons(dut.bXor_127==tmp.bXor_127,
 cons(dut.bXor_126==tmp.bXor_126,
 cons(dut.bXor_96==tmp.bXor_96,
 cons(dut.bXor_95==tmp.bXor_95,
 cons(dut.bXor_94==tmp.bXor_94,
 cons(dut.bXor_64==tmp.bXor_64,
 cons(dut.bXor_63==tmp.bXor_63,
 cons(dut.bXor_62==tmp.bXor_62,
 cons(dut.bXor_32==tmp.bXor_32,
 cons(dut.bXor_31==tmp.bXor_31,
 cons(dut.bXor_30==tmp.bXor_30,
 cons(dut.bXor_1==tmp.bXor_1,
 cons(dut.bXor_0==tmp.bXor_0,nil))))))))))))));
 
 Bit#(14) status = pack(vec);
 if(status == 14'b11111111111111)
   $display("Test %d PASS for BITWISE_XOR",cntr);
else
   $display("Test %d FAIL for BITWISE_XOR with Status %b",cntr,status);

state<=CHECK_XNOR;

endrule


rule check_xnor(state==CHECK_XNOR);
     
   Inputs tmp  = List::select(check,cntr);
   Vector#(14,Bool) vec =
 cons(dut.bXnor==tmp.bXnor,
 cons(dut.bXnor_127==tmp.bXnor_127,
 cons(dut.bXnor_126==tmp.bXnor_126,
 cons(dut.bXnor_96==tmp.bXnor_96,
 cons(dut.bXnor_95==tmp.bXnor_95,
 cons(dut.bXnor_94==tmp.bXnor_94,
 cons(dut.bXnor_64==tmp.bXnor_64,
 cons(dut.bXnor_63==tmp.bXnor_63,
 cons(dut.bXnor_62==tmp.bXnor_62,
 cons(dut.bXnor_32==tmp.bXnor_32,
 cons(dut.bXnor_31==tmp.bXnor_31,
 cons(dut.bXnor_30==tmp.bXnor_30,
 cons(dut.bXnor_1==tmp.bXnor_1,
 cons(dut.bXnor_0==tmp.bXnor_0,nil))))))))))))));
 
 Bit#(14) status = pack(vec);
 if(status == 14'b11111111111111)
   $display("Test %d PASS for BITWISE_XNOR",cntr);
else
   $display("Test %d FAIL for BITWISE_XNOR with Status %b",cntr,status);

state<=DONE;

endrule	

rule done(state==DONE);
   if(cntr>=fromInteger(len)) $finish(0);
   else
    cntr <= cntr+1;
	state <= SET;
	
endrule	


endmodule
