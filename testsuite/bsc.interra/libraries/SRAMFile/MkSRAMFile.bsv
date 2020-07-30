package MkSRAMFile;

import RegFile::*;
import Vector::*;
import Precedence::*;
import EqPrecedence::*;
import RegFile::*;
import SyncSRAM::*;
import SRAMFile::*;
import SRAM::*;
import SPSRAM::*;
import RAM::*;
import ClientServer::*;
import GetPut::*;

module mkDesign_MkSRAMFile (RAM#(Bit#(4),Bit#(8)));
  RAM#(Bit#(4),Bit#(8)) tx <- mkWrapSRAM(mkSRAMFile("input_file",16));
  return(tx);
endmodule: mkDesign_MkSRAMFile 

module mkTestbench_MkSRAMFile ();

   RegFile#(Bit#(4),Bit#(8)) stimulus_io();
   mkRegFileLoad#("input_file",0,15) the_stimulus_io(stimulus_io);

   RegFile#(Bit#(4),Bit#(8)) stimulus_io1();
   mkRegFileLoad#("input_file1",0,15) the_stimulus_io1(stimulus_io1);

   RAM#(Bit#(4),Bit#(8)) tx <- mkWrapSRAM(mkSRAMFile("input_file",16));
   Reg#(Bit#(8)) in_data <- mkReg(8'h55);
   Reg#(Bit#(4)) in_address <- mkReg(0);
   Reg#(Bit#(4)) out_address <- mkReg(0);
   Reg#(Bit#(4)) out_address1 <- mkReg(0);
   Reg#(Bit#(8)) out_data <- mkReg(8'h55);
   Reg#(Bit#(8)) counter <- mkReg(0);
   Reg#(Bool) request <- mkReg(True);
   Reg#(Bool) fail <- mkReg(False);
   Reg#(Bool) fire_request_value <- mkReg(True);
   Reg#(Bool) fire_request_data1 <- mkReg(False);
   Reg#(Bool) fire_read_value <- mkReg(False);
   Reg#(Bool) fire_read_value1 <- mkReg(True);
   Reg#(Bit#(4)) value_count <- mkReg(0);
   Reg#(Bit#(4)) value_count1 <- mkReg(0);

   Rules r1 = rules 
       rule always_fire (True);
       	 counter <= counter + 1;
       endrule
     endrules;

   Rules r2 = rules 
       rule request_value (fire_request_value);
	     fire_read_value <= True;
         RAMreq#(Bit#(4),Bit#(8)) z = Read(out_address);
    	 tx.request.put(z);
         out_address <= out_address + 1;
    	 $display("Cycle Number = %d, address requested %h ",counter, out_address);
		 if (out_address == 4'hf)
		    fire_request_value <= False;
       endrule
     endrules;

   Rules r3 = rules 
       rule read_value (fire_read_value);
         Bit #(8) first <- tx.response.get;
    	 $display("Cycle Number = %d, Value read %h value_count %d",counter, first,value_count);
		 value_count <= value_count + 1;
	     if (first != stimulus_io.sub(value_count))
		    fail <= True;
		 if (value_count == 15)
		    fire_read_value <= False;
       endrule
     endrules;

   Rules r4 = rules 
       rule data_write ((counter >= 80) &&(counter < 96));
         Tuple2#(Bit#(4),Bit#(8)) x = tuple2(in_address,in_data) ;
         RAMreq#(Bit#(4),Bit#(8)) y = Write(x);
	     tx.request.put(y);
         in_data <= in_data + 25;
         in_address <= in_address + 1;
         $display("Itr = 2 Cycle Number: %d, Writing Data: %h address %h ", counter, in_data,in_address);
		 if (counter == 95)
		    fire_request_data1 <= True;
       endrule
     endrules;

   Rules r5 = rules 
       rule request_data1 (fire_request_data1);
	     fire_read_value1 <= True;
         RAMreq#(Bit#(4),Bit#(8)) z = Read(out_address1);
    	 tx.request.put(z);
         out_address1 <= out_address1 + 1;
    	 $display("Itr = 2 Cycle Number = %d, address requested %h ",counter, out_address1);
		 if (out_address1 == 4'hf)
		    fire_request_data1 <= False;
       endrule
     endrules;

   Rules r6 = rules 
       rule read_value1 (fire_read_value1 && (counter < 130));
         Bit #(8) first1 <- tx.response.get;
    	 $display("Cycle Number = %d, Value read %h ",counter, first1);
		 value_count1 <= value_count1 + 1;
	     if (first1 != stimulus_io1.sub(value_count1))
		    begin
		      fail <= True;
    	      $display("Itr = 2 Mismatch : Exp %h Actual %h ",stimulus_io1.sub(value_count1),first1);
		    end
       endrule
     endrules;
    
    
   Rules r7 = rules 
      rule endofsim (counter == 130);
    	if (fail)
    	  $display("Simulation Fails");
    	else
    	  $display("Simulation Passes");
    	$finish(2'b00);
      endrule
     endrules;

    addRules (eqprecede(r1,r7,(precede((precede(precede (r2,r3),r4)),precede(r5,r6)))));

endmodule: mkTestbench_MkSRAMFile

endpackage: MkSRAMFile
