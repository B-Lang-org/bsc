package SplitServer;

//import Precedence :: *;
import Vector :: *;
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

module mkDesign_SplitServer(Server #(Bit#(8),Bit#(8)) );
   Server #(Bit#(8),Bit#(8))  serv1 <- mkMyserver();
   Vector#(4,Server #(Bit#(8),Bit#(8))) my_server_list <- splitServer(2,serv1);

   Server #(Bit#(8),Bit#(8)) serv2 = head(my_server_list);
   return(serv1);
endmodule: mkDesign_SplitServer

module mkTestbench_SplitServer ();

   Server #(Bit#(8),Bit#(8))  serv <- mkMyserver();
   Vector#(2,Server #(Bit#(8),Bit#(8))) my_server_list <- splitServer(2,serv);
   //Server #(Bit#(8),Bit#(8)) serv1 = my_server_list[0];
   //Server #(Bit#(8),Bit#(8)) serv2 = my_server_list[1];

   Reg#(Bit#(8)) in_data <- mkReg(0);
   Reg#(Bit#(8)) out_data <- mkReg(0);
   Reg#(Bit#(8)) counter <- mkReg(0);
   Reg#(Bool) fail <- mkReg(False);

     rule always_fire (True);
   	   counter <= counter + 1;
     endrule

     rule data_write2 (counter < 20 );
	   head(my_server_list).request.put(in_data);
       in_data <= in_data + 1;
       $display("Cycle Number: %d, Writing Data: %d", counter, in_data);
     endrule
   
     rule read_value2 (counter < 30);
       Bit #(8) val <- head(my_server_list).response.get;
       out_data <= out_data + 1;
	   $display("Cycle Number = %d, Value read = %d",counter, val);
       if (out_data != val) 
	     begin
	       $display("Mismatch Exp = %d Actual= %d",out_data, val);
           fail <= True;
	     end
     endrule

     rule data_write3 ((counter > 30) && (counter <50));
	   last(my_server_list).request.put(in_data);
       in_data <= in_data + 1;
       $display("Cycle Number: %d, Writing Data: %d", counter, in_data);
     endrule
   
     rule read_value3 ((counter > 30) && (counter < 60));
       Bit #(8) val1 <- last(my_server_list).response.get;
       out_data <= out_data + 1;
	   $display("Cycle Number = %d, Value read = %d",counter, val1);
       if (out_data != val1) 
	     begin
	       $display("Mismatch Exp = %d Actual= %d",out_data, val1);
           fail <= True;
	     end
     endrule

    rule endofsim (counter == 60);
	  if (fail)
	    $display("Simulation Fails");
	  else
	    $display("Simulation Passes");
	  $finish(2'b00);
    endrule
   
   
endmodule : mkTestbench_SplitServer

endpackage : SplitServer
