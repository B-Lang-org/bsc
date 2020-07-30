
import AmbaSynthesis :: * ;
import FIFOF :: * ;
import ConfigReg :: * ;

typedef Bit#(32)  DataReg ;

interface DMA ;
   interface Master master ;
   interface Slave slave ;
endinterface        

typedef enum { Grab, Send } State
      deriving(Bits,Eq) ;
      
(* always_ready, synthesize *)
module mkDMA ( DMA ) ;

   AmbaMasterAdapter master_adp <- mkBlueAmbaMaster ;
   BlueMasterAdapter mbus = master_adp.bbus ;
   
   AmbaSlaveAdapter slave_adp <- mkBlueAmbaSlaveReg ;
   BlueSlaveAdapter sbus = slave_adp.bbus ;

   Reg#(DataReg) transfer_cnt <- mkReg(0) ;
   Reg#(BusAddr) source_addr <- mkReg(0) ;
   Reg#(BusAddr) dest_addr <- mkReg(0) ;

   FIFOF#(State) inProgressOps <- mkSizedFIFOF( 4 ) ;
   Reg#(Bool)   readsFinished <- mkReg( False ) ;

   Reg#(int) cntr <- mkConfigReg(0);
   rule c ; cntr <= cntr + 1; endrule 
   
   //// DMA specific operations  
   rule getData ( transfer_cnt > 0 ) ;
      mbus.read( source_addr ) ;
      inProgressOps.enq( Grab ) ;
      source_addr <= source_addr + 4 ;
      transfer_cnt <= transfer_cnt - 1 ;
      // $display( "rule get data: %0d", cntr  ) ;
   endrule

   (* descending_urgency="storeData, getData " *)
      
   // Need to handle error here
   rule storeData (inProgressOps.first == Grab ) ;
      BusResponse resp = mbus.response ;
      mbus.takeResponse ;
      inProgressOps.deq ;

      dest_addr <= dest_addr + 4 ;
      mbus.write(  dest_addr, resp.data ) ;
      inProgressOps.enq ( Send );
      
      // $display( "rule send transfer back out: %0d", cntr ) ;
   endrule


   rule writeAck ( inProgressOps.first == Send ) ;
      // XXX need to handle error
      mbus.takeResponse ;
      inProgressOps.deq ;
      // $display( "rule write ACK data: %0d", cntr ) ;
   endrule

   rule markComplete ( readsFinished  && ! inProgressOps.notEmpty ) ;
      $display( "DMA transfer complete at cycle %0d", cntr._read  ) ;
      readsFinished <= False ;
   endrule
      
   // Slave operations  updating the configuration registers..
   addRules( updRegRule ( sbus, transfer_cnt,    0 ) ) ;
   addRules( readRegRule( sbus, transfer_cnt,    0 ) ) ;

   addRules( updRegRule ( sbus, source_addr,     4 ) ) ;
   addRules( readRegRule( sbus, source_addr,     4 ) ) ;

   addRules( updRegRule ( sbus, dest_addr,       8 ) ) ;
   addRules( readRegRule( sbus, dest_addr,       8 ) ) ;

   // XXX need rule to handle slave reads of unknown address.

   interface master = master_adp.amaster ;
   interface slave = slave_adp.aslave ;


endmodule
      

      
function Rules updRegRule( BlueSlaveAdapter ifc, Reg#(BusData) reg_ifc, Bit#(16) addr ) ;
   Rules r = 
    rules 
       rule updRegrule (ifc.slaveSelect && (ifc.request.addr[15:0] == addr ) && (ifc.request.read_write == Write )) ;
          let req = ifc.request ;
          // $display("DMA: %m updRegrule: %h %h %h", req.read_write, req.addr, req.data ) ;
          reg_ifc._write( ifc.request.data ) ;
          ifc.response( BusResponse{ data: 0, status: OK} ) ;
       endrule
    endrules ;
   return r ;
endfunction

function Rules readRegRule( BlueSlaveAdapter ifc, Reg#(BusData) reg_ifc, Bit#(16) addr ) ;
   Rules r = 
    rules 
       rule readRegrule (ifc.slaveSelect && (ifc.request.addr[15:0] == addr ) && (ifc.request.read_write == Read )) ;
          let req = ifc.request ;
          let val = reg_ifc._read ;
          // $display("DMA: %m readRegrule: %h %h %h", req.read_write, req.addr, val ) ;
          ifc.response( BusResponse{ data: val , status: OK} ) ;
       endrule
    endrules ;
   return r ;
endfunction
      
