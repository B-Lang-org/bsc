package Ram;

import RegFile::*;
import RAM::*;
import ClientServer::*;
import GetPut::*;

module mkRAM(RAM#(Bit#(16),Bit#(16))) ;
   RegFile #(Bit #(16) , Bit #(16)) mem();
   mkRegFile #(0, 65535) the_mem (mem);

   Reg #(Bit #(16)) data_in();
   mkReg #(0) the_data_in (data_in);

   function Action f(Bit #(16) a);
       action
	     data_in <= a;
	   endaction
   endfunction

   method request();
     return (interface Put;
               method put(RAMreq#(Bit#(16),Bit#(16)) x);
				 case (x) matches
				   tagged Write (.y) : return(mem.upd(tpl_1(y),tpl_2(y)));
				   tagged Read (.y) :  return (f( mem.sub (y)));
				 endcase 
               endmethod: put
			 endinterface: Put);
   endmethod: request


   method response();
     return (interface Get;
               method get();
			     actionvalue
					  return(data_in);
			     endactionvalue
               endmethod: get
			 endinterface: Get);
   endmethod: response


endmodule: mkRAM

module mkDesign_Ram (RAM#(Bit#(16),Bit#(16)));
  RAM#(Bit#(16),Bit#(16)) tx <- mkRAM;

  return(tx);

endmodule: mkDesign_Ram 


module mkTestbench_Ram ();

   RAM#(Bit#(16),Bit#(16)) tx <- mkRAM;
   //RAM#(Bit#(16),Bit#(16)) rx <- mkRAM;
   Reg#(Bit#(16)) in_data_in <- mkReg(16'h5555);
   Reg#(Bit#(16)) in_address <- mkReg(16'h0000);
   Reg#(Bit#(16)) in_offset <- mkReg(0);
   Reg#(Bit#(16)) out_offset <- mkReg(0);
   Reg#(Bit#(16)) out_address <- mkReg(16'h0000);
   Reg#(Bit#(16)) out_data_in <- mkReg(16'h5555);
   Reg#(Bit#(8)) counter <- mkReg(0);
   Reg#(Bool) request <- mkReg(True);
   Reg#(Bool) fail <- mkReg(False);

   //RAMreq#(Bit#(16),Bit#(16)) x = (Tuple2(in_data_in,in_address));

   rule always_fire (True);
   	 counter <= counter + 1;
   endrule

   rule data_in_write (counter < 16 );
     Tuple2#(Bit#(16),Bit#(16)) x = tuple2(in_address,in_data_in) ;
     RAMreq#(Bit#(16),Bit#(16)) y = Write(x);
	 tx.request.put(y);
     in_data_in <= in_data_in + 25;
     in_offset <= in_offset + 5;
     in_address <= in_address + in_offset + 1;
     $display("Cycle Number: %d, Writing Data: %h address %h offset %h", counter, in_data_in,in_address,in_offset);
   endrule

   rule request_value ((counter >= 16) && (counter < 32 ));
     RAMreq#(Bit#(16),Bit#(16)) z = Read(out_address);
	 tx.request.put(z);
     out_offset <= out_offset + 5;
     out_address <= out_address + out_offset +1;
	 //request <= False;
   endrule

   rule read_value ((counter >= 17) && (counter < 33 ));
     Bit #(16) first <- tx.response.get;
     out_data_in <= out_data_in + 25;
	 $display("Cycle Number = %d, Value read %h address %h offset %h",counter, first,out_address,out_offset);
     if (out_data_in != first)
         fail <= True;
	 //request <= True;
   endrule

  rule endofsim (counter == 32);
	if (fail)
	  $display("Simulation Fails");
	else
	  $display("Simulation Passes");
	$finish(2'b00);
  endrule

endmodule: mkTestbench_Ram
endpackage: Ram







