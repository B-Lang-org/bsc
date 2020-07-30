import Interfaces :: * ;
import Buses :: * ;
import Slaves :: * ;
import Masters :: * ;
import Connectable :: * ;

(* synthesize *)
module sysTB1m2s( Empty ) ;
   // create the bus
   B1m2s bus <- bus_1m_2s ;

   // create Slaves
   Slave defSlave <- defaultSlave ;
   Slave slave0 <- mkSlave1 ;
   Slave slave1 <- mkSlave2 ;

   // create the Master
   Master master0 <- mkMaster ;

   mkConnection ( master0, bus.ms0 ) ;
   mkConnection ( defSlave, bus.defSlave ) ;
   mkConnection ( slave0, bus.ss0 ) ;
   mkConnection ( slave1, bus.ss1 ) ;

endmodule
