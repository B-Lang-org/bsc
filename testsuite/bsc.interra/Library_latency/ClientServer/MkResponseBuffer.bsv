package MkResponseBuffer;

import FIFO :: *;
import ClientServer :: *;
import GetPut :: *;
import Connectable :: *;

typedef Server #(Bit #(n),Bit#(n)) Myserver #(type n); 
typedef Client #(Bit #(n),Bit#(n)) Myclient #(type n); 

module mkMyserver(Myserver#(8)) ;
   FIFO#(Bit#(8)) server_datafifo <- mkSizedFIFO(16) ;
   method request();
   return (fifoToPut (server_datafifo));
   endmethod: request
   method response();
   return (fifoToGet (server_datafifo));
   endmethod: response
endmodule: mkMyserver

module mkDesign_MkResponseBuffer(Server #(Bit#(8),Bit#(8)) );
   Server #(Bit#(8),Bit#(8))  serf1 <- mkMyserver();
   Server #(Bit#(8),Bit#(8))  serf2 <- mkResponseBuffer(serf1);

   return(serf2);
endmodule: mkDesign_MkResponseBuffer

module mkTestbench_MkResponseBuffer ();

   Server #(Bit#(8),Bit#(8))  serf1 <- mkMyserver();
   Server #(Bit#(8),Bit#(8))  serf2 <- mkResponseBuffer(serf1);
   Reg#(Bit#(8)) in_data <- mkReg(0);
   Reg#(Bit#(8)) out_data <- mkReg(0);
   Reg#(Bit#(8)) counter <- mkReg(0);
   Reg#(Bool) fail <- mkReg(False);

rule always_fire (True);
   	 counter <= counter + 1;
   endrule

   rule data_write (True);//counter < 5 );
	 serf2.request.put(in_data);
     in_data <= in_data + 1;
     $display("Cycle Number: %d, Writing Data: %d", counter, in_data);
   endrule
   

   rule read_value (True); //(counter >= 5) && (counter < 10 ));
     Bit #(8) first <- serf2.response.get;
     out_data <= out_data + 1;
	 $display("Cycle Number = %d, Value read = %d",counter, first);
     if (out_data != first)
         fail <= True;
  endrule

  rule endofsim (counter == 10);
	if (fail)
	  $display("Simulation Fails");
	else
	  $display("Simulation Passes");
	$finish(2'b00);
  endrule

endmodule : mkTestbench_MkResponseBuffer

endpackage : MkResponseBuffer
