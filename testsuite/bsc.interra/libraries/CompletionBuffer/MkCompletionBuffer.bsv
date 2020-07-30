package MkCompletionBuffer;

import CompletionBuffer::*;
import GetPut::*;
import Vector::*;
import RegFile::*;
import RegFile::*;

typedef enum {Reserve, Complete, Drain, Done} State deriving (Eq, Bits);

module mkDesign_MkCompletionBuffer(CompletionBuffer#(2,Bit #(8)));

  CompletionBuffer#(2,Bit #(8)) dut();
  mkCompletionBuffer the_dut(dut);
  return(dut);
endmodule: mkDesign_MkCompletionBuffer

module mkTestbench_MkCompletionBuffer();

  RegFile#(Bit#(4),Bit#(8)) stimulus_io();
  mkRegFileLoad#("input_file",0,15) the_stimulus_io(stimulus_io);

  CompletionBuffer#(16,Bit #(8)) buf1();
  mkCompletionBuffer the_buf1(buf1);
  Reg#(Bit#(32)) counter <- mkReg(0);
  Reg#(Bit#(4)) data_rd_cnt <- mkReg(0);
  Reg#(Bit#(4)) val_count <- mkReg(0);
  Reg#(CBToken#(16)) x <- mkRegU;
  Reg#(Bool) fail <- mkReg(False);
  Reg#(Bool) fire_data_reserve <- mkReg(True);
  Reg#(Bool) fire_data_complete <- mkReg(False);
  Reg#(Bool) fire_data_read <- mkReg(False);
  Reg #(State) state <- mkReg(Reserve);


  Rules r1 = rules
     rule always_fire (True);
   	 counter <= counter + 1;
     endrule
  endrules;
     
  Rules r2 = rules
     rule data_reserve (state == Reserve) ;
       CBToken#(16) y <- buf1.reserve.get;
   	   x <= y;
   	   $display("exec r2 cycle = %d",counter);
	   state <= Complete;
     endrule
  endrules;
   
  Rules r3 = rules
     rule data_complete (state == Complete);
	   val_count <= val_count + 1;
	   Bit#(8) in_val = stimulus_io.sub(val_count);
       Tuple2#(CBToken#(16),Bit #(8)) y = tuple2(x,in_val);
       buf1.complete.put(y);
       $display("exec r3 cycle = %d",counter);
	   state <= Drain;
     endrule
  endrules;
   
  Rules r4 = rules
     rule data_read (state == Drain) ;
       Bit#(8) value <- buf1.drain.get;
   	   $display("value read = %h",value);
	   if (value != stimulus_io.sub(data_rd_cnt))
	     fail <= True;
	   data_rd_cnt <= data_rd_cnt + 1;
	   if (data_rd_cnt == 15)
	     state <= Done;
	   else
	     state <= Reserve;
     endrule
  endrules;
   
  Rules r5 = rules
     rule endofsim (state == Done);
       if (fail)
         $display("Simulation Fails");
       else
         $display("Simulation Passes");
       $finish(2'b00);
      endrule
  endrules;
   
    Vector #(5, Rules) my_list = cons(r1, cons(r2, cons(r3, cons(r4, cons(r5,nil)))));
    addRules (joinRules (my_list) );
     
endmodule: mkTestbench_MkCompletionBuffer
endpackage: MkCompletionBuffer
