import Interfaces :: * ;
import Buses :: * ;
import Slaves :: * ;
import Masters :: * ;
import Connectable :: * ;

// 1 master 25% load
(* synthesize *)
module sysM1_25( Empty ) ;
   // create the bus structure use slaveSel3 function for decoding
   B1m2s bus <- bus_1m_2s ( slaveSel3 ) ;

   // create Slaves
   Slave defSlave <- defaultSlave ;
   Slave slave0 <- mkADPSlave(1) ;
   Slave slave1 <- mkADPSlave(2) ;

   // create the Master
   // simulate for 10000 cycles random seed 1, bus load is 64/256 (25%) 
   Master  master0 <- mkAAMasterP( 10000, 1, 64, "M0" ) ;
   
   // connect the masters and slaves to the bus
   Empty connMaster <- mkConnection ( master0, bus.ms0 ) ;
   Empty connDefSlave <- mkConnection ( defSlave, bus.defSlave ) ;
   Empty connSlave0 <- mkConnection ( slave0, bus.ss0 ) ;
   Empty connSlave1 <- mkConnection ( slave1, bus.ss1 ) ;

endmodule

(* synthesize *)
module sysM1_50( Empty ) ;
   // create the bus
   B1m2s bus <- bus_1m_2s( slaveSel3 )  ;

   // create Slaves
   Slave defSlave <- defaultSlave ;
   Slave slave0 <- mkSlave(1) ;
   Slave slave1 <- mkSlave(2) ;

   // create the Master
   Master master0 <- mkMasterP( 10000, 1, 128, "M0" ) ;

   mkConnection ( master0, bus.ms0 ) ;
   mkConnection ( defSlave, bus.defSlave ) ;
   mkConnection ( slave0, bus.ss0 ) ;
   mkConnection ( slave1, bus.ss1 ) ;

endmodule

(* synthesize *)
module sysM1_75( Empty ) ;
   // create the bus
   B1m2s bus <- bus_1m_2s (slaveSel3)  ;

   // create Slaves
   Slave defSlave <- defaultSlave ;
   Slave slave0 <- mkSlave(1) ;
   Slave slave1 <- mkSlave(2) ;

   // create the Master
   Master master0 <- mkMasterP( 10000, 1, 192, "M0" ) ;

   mkConnection ( master0, bus.ms0 ) ;
   mkConnection ( defSlave, bus.defSlave ) ;
   mkConnection ( slave0, bus.ss0 ) ;
   mkConnection ( slave1, bus.ss1 ) ;

endmodule
