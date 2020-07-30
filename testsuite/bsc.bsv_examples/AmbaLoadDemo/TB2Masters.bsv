import Interfaces :: * ;
import Buses :: * ;
import Slaves :: * ;
import Masters :: * ;
import Connectable :: * ;

(* synthesize *)
module sysM2_25( Empty ) ;
   // create the bus structure use slaveSel3 function for decoding
   B2m2s bus <- bus_2m_2s ( slaveSel3 ) ;

   // create Slaves
   Slave defSlave <- defaultSlave ;
   Slave slave0 <- mkSlave(1) ;
   Slave slave1 <- mkSlave(2) ;

   // create the Master
   Master master0 <- mkMasterP( 10000,  1, 64, "M0" ) ;
   Master master1 <- mkMasterP( 10000, 29, 64, "M1" ) ;

   mkConnection ( master0, bus.ms0 ) ;
   mkConnection ( master1, bus.ms1 ) ;
   mkConnection ( defSlave, bus.defSlave ) ;
   mkConnection ( slave0, bus.ss0 ) ;
   mkConnection ( slave1, bus.ss1 ) ;

endmodule

(* synthesize *)
module sysM2_50( Empty ) ;
   // create the bus
   B2m2s bus <- bus_2m_2s( slaveSel3 )  ;

   // create Slaves
   Slave defSlave <- defaultSlave ;
   Slave slave0 <- mkSlave(1) ;
   Slave slave1 <- mkSlave(2) ;

   // create the Master
   Master master0 <- mkMasterP( 10000,  1, 128, "M0" ) ;
   Master master1 <- mkMasterP( 10000, 29, 128, "M1" ) ;

   mkConnection ( master0, bus.ms0 ) ;
   mkConnection ( master1, bus.ms1 ) ;
   mkConnection ( defSlave, bus.defSlave ) ;
   mkConnection ( slave0, bus.ss0 ) ;
   mkConnection ( slave1, bus.ss1 ) ;

endmodule

(* synthesize *)
module sysM2_75( Empty ) ;
   // create the bus
   B2m2s bus <- bus_2m_2s (slaveSel3)  ;

   // create Slaves
   Slave defSlave <- defaultSlave ;
   Slave slave0 <- mkSlave(1) ;
   Slave slave1 <- mkSlave(2) ;

   // create the Master
   Master master0 <- mkMasterP( 10000,  1, 192, "M0" ) ;
   Master master1 <- mkMasterP( 10000, 29, 192, "M1" ) ;

   mkConnection ( master0, bus.ms0 ) ;
   mkConnection ( master1, bus.ms1 ) ;
   mkConnection ( defSlave, bus.defSlave ) ;
   mkConnection ( slave0, bus.ss0 ) ;
   mkConnection ( slave1, bus.ss1 ) ;

endmodule
