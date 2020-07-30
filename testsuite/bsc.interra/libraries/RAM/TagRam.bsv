package TagRam;

import RegFile::*;
import TRAM::*;
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
				   tagged RAM::Write (.y) : return(mem.upd(tpl_1(y),tpl_2(y)));
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

module mkDesign_TagRam (TRAM#(Bit#(1),Bit#(16),Bit#(16)));
  RAM#(Bit#(16),Bit#(16)) tx <- mkRAM;
  TRAM#(Bit#(1),Bit#(16),Bit#(16)) tx1();
  tagRAM #(65535,mkRAM) the_tx1(tx1);

  return(tx1);

endmodule: mkDesign_TagRam 

module mkTestbench_TagRam ();

   TRAM#(Bit#(1),Bit#(16),Bit#(16)) tx() ;
  tagRAM #(65535,mkRAM) the_tx(tx);
   //RAM#(Bit#(16),Bit#(16)) rx <- mkRAM;
   Reg#(Bit#(16)) in_data_in <- mkReg(16'h5555);
   Reg#(Bit#(16)) in_address <- mkReg(16'h0000);
   //Reg#(Bit#(16)) in_offset <- mkReg(0);
   //Reg#(Bit#(16)) out_offset <- mkReg(0);
   Reg#(Bit#(16)) out_address <- mkReg(16'h0000);
   Reg#(Bit#(16)) out_data_in <- mkReg(16'h5555);
   Reg#(Bit#(8)) counter <- mkReg(0);
   Reg#(Bit#(1)) in_tag <- mkReg(0);
   Reg#(Bool) request <- mkReg(True);
   Reg#(Bool) fail <- mkReg(False);

   //RAMreq#(Bit#(16),Bit#(16)) x = (RAMreqWrite(in_data_in,in_address));

   rule always_fire (True);
   	 counter <= counter + 1;
   endrule

/*
   rule data_in_write (counter < 1 );
     TRAMreqWrite#(Bit#(1),Bit#(16),Bit#(16)) x = TRAMreqWrite{value: 16'h1234, address: 16'h0001} ;
     TRAMreq#(Bit#(1),Bit#(16),Bit#(16)) y = Write(x);
	 tx.request.put(y);
     $display("Cycle Number: %d, Writing Data: 1234 address 0001 ", counter);
   endrule

   rule request_value (counter == 1); 
     TRAMreqRead#(Bit#(1),Bit#(16),Bit#(16)) z = TRAMreqRead{tag: 1, address: 16'h0001} ;
     TRAMreq#(Bit#(1),Bit#(16),Bit#(16)) req = Read(z);
	 tx.request.put(req);
   endrule

   rule read_value (counter == 2) ;
     TRAMresp#(Bit#(1),Bit #(16)) first <- tx.response.get;
	 $display("Cycle Number = %d, Value read %h ",counter,first.value);
     if (first.value != 16'h1234)
	   begin
	     $display("Data Mismatch Cycle Number = %d, Exp 1234 Value read %h ",counter,first.value);
         fail <= True;
	   end
   endrule

  rule endofsim (counter == 3);
	if (fail)
	  $display("Simulation Fails");
	else
	  $display("Simulation Passes");
	$finish(2'b00);
  endrule
*/

   rule data_in_write (counter < 16 );
     //TRAMreqWrite#(Bit#(1),Bit#(16),Bit#(16)) x = TRAMreqWrite{value: in_data_in, address: in_address} ;
     Tuple2#(Bit#(16),Bit#(16)) x = tuple2(in_address,in_data_in) ;
     TRAMreq#(Bit#(1),Bit#(16),Bit#(16)) y = Write(x);
	 tx.request.put(y);
     in_data_in <= in_data_in + 25;
     in_address <= in_address + 20;
     $display("Cycle Number: %d, Writing Data: %h address %h ", counter, in_data_in,in_address);
   endrule

   rule request_value ((counter >= 16) && (counter < 32 ));
     //TRAMreqRead#(Bit#(1),Bit#(16),Bit#(16)) z = TRAMreqRead{tag: 1, address: out_address} ;
     Tuple2#(Bit#(1),Bit#(16)) z = tuple2(1, out_address) ;
     TRAMreq#(Bit#(1),Bit#(16),Bit#(16)) req = Read(z);
	 tx.request.put(req);
     out_address <= out_address + 20;
	 //request <= False;
   endrule

   rule read_value ((counter >= 17) && (counter < 33 ));
     TRAMresp#(Bit#(1),Bit #(16)) first <- tx.response.get;
     out_data_in <= out_data_in + 25;
     $display("Cycle Number: %d, Reading Data: %h ", counter,tpl_2(first) );
     if (out_data_in != tpl_2(first))
	   begin
	     $display("Data Mismatch Cycle Number = %d, Exp %h Value read %h address %h ",counter,out_data_in,tpl_2(first),out_address);
         fail <= True;
	   end
	 //request <= True;
   endrule

  rule endofsim (counter == 33);
	if (fail)
	  $display("Simulation Fails");
	else
	  $display("Simulation Passes");
	$finish(2'b00);
  endrule

endmodule: mkTestbench_TagRam

endpackage: TagRam







