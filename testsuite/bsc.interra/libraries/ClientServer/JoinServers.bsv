package JoinServers;

import List :: *;
import FIFO :: *;
import ClientServer :: *;
import GetPut :: *;
import Connectable :: *;

typedef Server #(Bit #(n),Bit#(n)) Myserver #(type n);
typedef Client #(Bit #(n),Bit#(n)) Myclient #(type n);

function Maybe#(Bit#(8)) f (Bit#(8) a);
     Maybe #(Bit #(8)) x = Invalid;
     if (a < 10)
        return (Invalid);
     else
        return (Valid(a));
endfunction

module mkMyserver(Myserver#(8)) ;
   FIFO#(Bit#(8)) server_datafifo <- mkSizedFIFO(16) ;
   method request();
   return (fifoToPut (server_datafifo));
   endmethod: request
   method response();
   return (fifoToGet (server_datafifo));
   endmethod: response
endmodule: mkMyserver

module mkDesign_JoinServers(Server #(Bit#(8),Bit#(8)) );
   Server #(Bit#(8),Bit#(8))  serv1 <- mkMyserver();
   Server #(Bit#(8),Bit#(8))  serv2 <- mkMyserver();
   Server #(Bit#(8),Bit#(8))  serv3 <- mkMyserver();
   Server #(Bit#(8),Bit#(8))  serv4 <- mkMyserver();
   Server #(Bit#(8),Bit#(8))  serv5 <- mkMyserver();
   List#(Tuple2 #(function Maybe#(Bit#(8)) f(Bit#(8) a) ,Server #(Bit#(8),Bit#(8)))) my_server_list =
                  Cons (tuple2 (f,serv1),
				  Cons (tuple2 (f,serv2),
				  Cons (tuple2 (f,serv3),
				  Cons (tuple2 (f,serv4),
				  Cons (tuple2 (f,serv5),Nil)))));

   Server #(Bit#(8),Bit#(8))  joinedservers <- joinServers(my_server_list);

   return(joinedservers);
endmodule: mkDesign_JoinServers

module mkTestbench_JoinServers ();

   Server #(Bit#(8),Bit#(8))  serv1 <- mkMyserver();
   Server #(Bit#(8),Bit#(8))  serv2 <- mkMyserver();
   Server #(Bit#(8),Bit#(8))  serv3 <- mkMyserver();
   Server #(Bit#(8),Bit#(8))  serv4 <- mkMyserver();
   Server #(Bit#(8),Bit#(8))  serv5 <- mkMyserver();

   Reg#(Bit#(8)) in_data <- mkReg(0);
   Reg#(Bit#(8)) out_data <- mkReg(10);
   Reg#(Bit#(8)) counter <- mkReg(0);
   Reg#(Bool) fail <- mkReg(False);

   rule always_fire (True);
   	 counter <= counter + 1;
   endrule

   rule read_value (counter < 20 );
     Bit #(8) first <- serv1.response.get;
     Bit #(8) second <- serv2.response.get;
     Bit #(8) third <- serv3.response.get;
     Bit #(8) fourth <- serv4.response.get;
     Bit #(8) fifth <- serv5.response.get;
     out_data <= out_data + 1;
	 $display("Cycle Number = %d, Value read = %d",counter, first);
     if ((out_data != first) || (out_data != second) || (out_data != third) || (out_data != fourth) || (out_data != fifth))
	   begin
	     $display("Mismatch Actual server1 =  %d  server2 = %d server3 = %d server4 = %d server5 = %d Exp= %d",first,second,third,fourth,fifth,out_data);
         fail <= True;
	   end
  endrule

   // XXX This was moved here because the testcase is sensitive to
   // arbitrary urgency choices.
   List#(Tuple2 #(function Maybe#(Bit#(8)) f(Bit#(8) a) ,Server #(Bit#(8),Bit#(8)))) my_server_list =
                  Cons (tuple2 (f,serv1),
				  Cons (tuple2 (f,serv2),
				  Cons (tuple2 (f,serv3),
				  Cons (tuple2 (f,serv4),
				  Cons (tuple2 (f,serv5),Nil)))));

   Server #(Bit#(8),Bit#(8))  joinedservers <- joinServers(my_server_list);

   rule data_write (counter < 20 );
	 joinedservers.request.put(in_data);
     in_data <= in_data + 1;
     $display("Cycle Number: %d, Writing Data: %d", counter, in_data);
   endrule

   rule read_value2 (counter >= 20 );
     Bit #(8) val <- joinedservers.response.get;
     out_data <= out_data + 1;
	 $display("Cycle Number = %d, Value read = %d",counter, val);
     if (out_data != val)
	   begin
	     $display("Mismatch Exp = %d Actual= %d",out_data, val);
         fail <= True;
	   end
  endrule

   rule data_write2 (counter >= 20 );
	 serv1.request.put(in_data);
     in_data <= in_data + 1;
     $display("Cycle Number: %d, Writing Data: %d", counter, in_data);
   endrule

  rule endofsim (counter == 40);
	if (fail)
	  $display("Simulation Fails");
	else
	  $display("Simulation Passes");
	$finish(2'b00);
  endrule

endmodule : mkTestbench_JoinServers

endpackage : JoinServers
