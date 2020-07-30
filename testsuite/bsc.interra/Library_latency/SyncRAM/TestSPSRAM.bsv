package SPSRam;

import Vector::*;
import Precedence::*;
import RegFile::*;
import SyncSRAM::*;
import SRAM::*;
import SPSRAM::*;
import RAM::*;
import ClientServer::*;
import GetPut::*;

module mkDesign_SPSram (RAM#(Bit#(16),Bit#(16)));
  
  RAM#(Bit#(16),Bit#(16)) tx <- mkWrapSRAM(mkSPSRAM(65536));

  return(tx);

endmodule: mkDesign_SPSram 

module mkTestbench_SPSRam ();

   RAM#(Bit#(16),Bit#(16)) tx <- mkWrapSRAM(mkSPSRAM(65536));
   Reg#(Bit#(16)) in_data <- mkReg(16'h5555);
   Reg#(Bit#(16)) in_address <- mkReg(16'h0000);
   Reg#(Bit#(16)) in_offset <- mkReg(0);
   Reg#(Bit#(16)) out_offset <- mkReg(0);
   Reg#(Bit#(16)) out_address <- mkReg(16'h0000);
   Reg#(Bit#(16)) out_data <- mkReg(16'h5555);
   Reg#(Bit#(8)) counter <- mkReg(0);
   Reg#(Bool) request <- mkReg(True);
   Reg#(Bool) fail <- mkReg(False);

   //RAMreq#(Bit#(16),Bit#(16)) x = (RAMreqWrite(in_data,in_address));

   Rules r1 = rules 
       rule always_fire (True);
       	 counter <= counter + 1;
       endrule
     endrules;
    
   Rules r2 = rules 
       rule data_write (counter < 16 );
         Tuple2#(Bit#(16),Bit#(16)) x = tuple2(in_address,in_data) ;
         RAMreq#(Bit#(16),Bit#(16)) y = Write(x);
    	 tx.request.put(y);
         in_data <= in_data + 25;
         in_offset <= in_offset + 5;
         in_address <= in_address + in_offset + 1;
         $display("Cycle Number: %d, Writing Data: %h address %h offset %h", counter, in_data,in_address,in_offset);
       endrule
     endrules;
    
   Rules r3 = rules 
       rule request_value ((counter >= 16) && (counter <32));
         RAMreq#(Bit#(16),Bit#(16)) z = Read(out_address);
    	 tx.request.put(z);
         out_offset <= out_offset + 5;
         out_address <= out_address + out_offset +1;
    	 //request <= False;
       endrule
     endrules;
    
   Rules r4 = rules 
       rule read_value ((counter >= 18) && (counter < 34));
         Bit #(16) first <- tx.response.get;
         out_data <= out_data + 25;
    	 $display("Cycle Number = %d, Value read %h address %h offset %h",counter, first,out_address,out_offset);
         if (out_data == first)
		     noAction;
	     else
             fail <= True;
    	 //request <= True;
       endrule
     endrules;
    
   Rules r5 = rules 
      rule endofsim (counter == 35);
    	if (fail)
    	  $display("Simulation Fails");
    	else
    	  $display("Simulation Passes");
    	$finish(2'b00);
      endrule
     endrules;

    Vector #(4, Rules) my_list = cons(r1, cons(r2, cons(r3, cons(r5,nil))));
 
    addRules (precede (r4,joinRules (my_list)));

endmodule: mkTestbench_SPSRam

endpackage: SPSRam
