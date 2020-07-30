
// 1. Clean up test - done
// 2. Add memory
// 2. Add monitoring to slavetx
// 3. Add fifo to slaverx
// 4. Add sending to slaverx
// 5. Add 2 more slaves
// 6. Enhance test to move data between all slaves
// 7. 

import Slaves :: *;
import Connectable :: *;
import AmbaSynthesis :: *;
import DMA :: *;
import ConfigReg :: *;


// ===========================================================================
// successor and predecessor functions for enums.

   function any_enum succ( any_enum in )
      provisos ( Eq#(any_enum), Bits#(any_enum,x), Bounded#(any_enum) ) ;
      any_enum retValue ;
      any_enum min = minBound;
      any_enum max = maxBound;
      if (( pack(in) < pack(min)) || ( pack(in) >= pack(max) ))
         retValue = maxBound ;
      else begin
         retValue = unpack( pack(in) + 1 ) ;
      end
      return retValue ;
   endfunction

   function any_enum pred( any_enum in )
      provisos ( Eq#(any_enum), Bits#(any_enum,x), Bounded#(any_enum) ) ;
      any_enum retValue ;
      any_enum min = minBound;
      any_enum max = maxBound;

      if (( pack(in) <= pack(min)) || ( pack(in) > pack(max) ))
         retValue = minBound ;
      else begin
         retValue = unpack( pack(in) - 1 ) ;
      end
      return retValue ;
   endfunction

//
// ===========================================================================


// ===========================================================================
// Bus Decode logic


   // Slave Selection Decode Function
   function Bit#(n) slaveSelDMA( BusAddr addr )
      provisos( Add#(n,j,16) ) ;
      Nat selbit = unpack({28'b0,addr[31:28]});
      return (selbit < fromInteger(valueOf(n))) ? 'h1 << selbit : 0;
   endfunction

//
// ===========================================================================


// ===========================================================================
// Basic Read/Write Bus Transactions
// 

   function Rules readData( Bool               fire_condition,
                            Reg#(any_enum)     state,
                            Reg#(Bool)         access_pending,
                            BlueMasterAdapter  ifc, 
                            Bit#(32)           addr, 
                            Reg#(Bit#(32))     r_data )
   provisos (Eq#(any_enum), Bits#(any_enum,x), Bounded#(any_enum) ) ;

      Rules r = rules 
        rule startRead(fire_condition && !access_pending);
           ifc.read( addr );
           access_pending <= True;
        endrule

        rule finishRead(fire_condition && access_pending);
           ifc.takeResponse;
           BusResponse resp = ifc.response;
           r_data <= resp.data;
           access_pending <= False;
           state <= succ(state);
        endrule
      endrules;
      return r;
   endfunction


   function Rules writeData( Bool               fire_condition, 
                             Reg#(any_enum)     state,
                             Reg#(Bool)         access_pending,
                             BlueMasterAdapter  ifc, 
                             Bit#(32)           addr, 
                             Bit#(32)           data )
   provisos (Eq#(any_enum), Bits#(any_enum,x), Bounded#(any_enum) ) ;
      Rules r =  rules 
         rule startWrite(fire_condition && !access_pending);
           ifc.write(addr,data);
           access_pending <= True;
         endrule

         rule finishWrite(fire_condition && access_pending);
            ifc.takeResponse;
            access_pending <= False;
            state <= succ(state);
         endrule
      endrules;
      return r;
   endfunction

//
// ===========================================================================

// ===========================================================================
// dmaTransfer
// Perform a complete dma transfer including:
//    - Programming the source start address
//    - Programming the destination start address
//    - Programming the transfer count (number of words to transfer)
//    - Polling the transfer count until all data has been transferred

   typedef enum {
      DMA_IDLE ,
      DMA_WRITE_DMA_SRC ,
      DMA_READ_DMA_SRC  ,
      DMA_WRITE_DMA_DEST,
      DMA_READ_DMA_DEST ,
      DMA_WRITE_DMA_CNT ,
      DMA_READ_DMA_CNT  ,
      DMA_READ_DMA_POLL ,
      DMA_DONE
   }  DmaStateType deriving (Bits, Eq, Bounded );

   function Rules dmaTransfer (BlueMasterAdapter  ifc, 
                               Bool               go,                  
                               Reg#(DmaStateType) state,               
                               Bit#(32)           saddr,               
                               Bit#(32)           daddr,               
                               Bit#(32)           tsize,               
                               Reg#(Bit#(32))     test_cnt,
                               Reg#(Bit#(32))     rdata,
                               Bit#(32)           tick_counter,
                               Reg#(Bool)         access_pending,
                               BusAddr            dmaBase
                               );
      Rules r = rules
         rule startTransfer(state==DMA_IDLE && go);
            $display("%t *********** START OF TRANSFER %d ***************",$time,test_cnt);
            test_cnt <= test_cnt + 1;  // increment iteration
            state <= DMA_WRITE_DMA_SRC;
         endrule

         rule read_dma_cnt (state==DMA_READ_DMA_POLL && tick_counter[6:0]==0);      
            // $display("%t DMA_READ_DMA_POLL dma.cnt = %d, tsize = %d",$time, rdata,tsize);
            state <= (rdata==0) ? DMA_DONE : pred(state);      
         endrule

         rule dmaDone (state==DMA_DONE);
            // $display("%t DMA_DONE",$time);
            state <= DMA_IDLE;      
         endrule

      endrules;
      
      r = rJoin(r, writeData(state==DMA_WRITE_DMA_SRC, state, access_pending, ifc, dmaBase+4, saddr));
      r = rJoin(r, readData (state==DMA_READ_DMA_SRC,  state, access_pending, ifc, dmaBase+4, rdata));
      r = rJoin(r, writeData(state==DMA_WRITE_DMA_DEST,state, access_pending, ifc, dmaBase+8, daddr));
      r = rJoin(r, readData (state==DMA_READ_DMA_DEST, state, access_pending, ifc, dmaBase+8, rdata));
      r = rJoin(r, writeData(state==DMA_WRITE_DMA_CNT, state, access_pending, ifc, dmaBase+0, tsize));
      r = rJoin(r, readData (state==DMA_READ_DMA_CNT,  state, access_pending, ifc, dmaBase+0, rdata));
     
      return r;
   endfunction // dmaTransfer

//
// ===========================================================================


// ===========================================================================
// srcSinkTest
// The source to sink test uses the dma to transfer data from the source slave
// to the sink slave.  As each word is sent the source slave calculates a 
// checksum.  As each word is received the sink slave also calculates a checksum.
// The test verifies that the two checksums match.

   typedef enum {
      START_DMA ,
      WAIT_FOR_DMA,
      READ_SRC_CHK  ,
      READ_SINK_CHK ,
      CMP_SRC_SINK ,
      SRCSINKDONE
   }  SrcSinkTestStateType deriving (Bits, Eq, Bounded );

   
   function Rules srcSinkTest(Bool                srcSinkTest_go,
                              Nat                 loops,
                              Reg#(SrcSinkTestStateType) srcSinkTestState,
                              Reg#(DmaStateType)  dmaTransferState,
                              Reg#(Bit#(32))      src_checksum, 
                              Reg#(Bit#(32))      sink_checksum,
                              Reg#(Bool)          fail,
                              BlueMasterAdapter   adp_ifc,
                              BusAddr             srcRegBase,
                              BusAddr             snkRegBase,
                              BusAddr             srcBase,
                              BusAddr             snkBase,
                              Reg#(Bit#(32))      transferSize,
                              Reg#(Bit#(32))      test_number,
                              Reg#(Bit#(32))      rdata,
                              Bit#(32)            tick_counter,
                              Reg#(Bool)          access_pending,
                              BusAddr             dmaBase
                              );

      Rules r = rules

         rule dmaStart(srcSinkTestState==START_DMA && srcSinkTest_go);
            // $display("%t srcSinkTestState==START_DMA",$time);
            srcSinkTestState<=WAIT_FOR_DMA;
         endrule

         rule dmaWait(srcSinkTestState==WAIT_FOR_DMA);
            // $display("%t srcSinkTestState==WAIT_FOR_DMA",$time);
            if (dmaTransferState==DMA_DONE) begin
               srcSinkTestState<=READ_SRC_CHK;
            end
         endrule

         rule cmp_src_sink (srcSinkTestState==CMP_SRC_SINK);
            $display("%t Checksum:  %d  %d",$time,src_checksum, sink_checksum);
            if (sink_checksum == src_checksum)
               $display("%t sub-test passed",$time);
            else begin
               fail <= True;
               $display("%t SUB-TEST FAILED",$time);
            end
            srcSinkTestState <= START_DMA;
            transferSize <= transferSize + 20;

            if (test_number >= loops) begin
              if (fail)
                  $display("%t TEST FAILED!!",$time);
               else begin
                  $display("%t test passed",$time);
               end
               $finish(0);
            end
         endrule
      endrules;

      r = rJoin(r,readData (srcSinkTestState==READ_SRC_CHK, srcSinkTestState, 
                access_pending,  adp_ifc, srcRegBase+0, src_checksum)) ;  
      r = rJoin(r,readData (srcSinkTestState==READ_SINK_CHK, srcSinkTestState,
                access_pending,  adp_ifc, snkRegBase+0, sink_checksum)) ; 
      r = rJoin(r,dmaTransfer(adp_ifc,srcSinkTestState==START_DMA && srcSinkTest_go,
                dmaTransferState,srcBase,snkBase,transferSize,test_number,rdata,
                tick_counter, access_pending,dmaBase));
      return r;
   endfunction // SrcSinkTest

//
// ===========================================================================



   typedef enum {
      SRCSNKTEST ,
      TESTDONE
   }  TestStateType deriving (Bits, Eq, Bounded );


(* synthesize *)
module sysDMA( Empty );

   BusParam#(2,4) bus <- busP (slaveSelDMA ) ;

   // create Slaves
   Slave   defSlave <- defaultSlave ;
   SlaveRx slave0   <- mkSlaveRx;
   SlaveTx slave1   <- mkSlaveTx;
   Slave   sram3    <- mkSRAM64k; 

   // create the Testbench master
   Master  master0 <- mkDMATester ;

   // Create the DMA 
   DMA dma <- mkDMA ;
   
   // connect the masters and slaves to the bus
   Empty connMaster0 <- mkConnection ( master0, bus.ms[0] ) ;
   Empty connMaster1 <- mkConnection ( dma.master, bus.ms[1] ) ;
   Empty connDefSlave <- mkConnection ( defSlave, bus.defSlave ) ;

   Empty connSlave0 <- mkConnection ( slave0.slave, bus.ss[0] ) ;
   Empty connSlave1 <- mkConnection ( slave1.slave, bus.ss[1] ) ;
   Empty connSlave2 <- mkConnection ( dma.slave, bus.ss[2] ) ;
   Empty connSram3  <- mkConnection ( sram3, bus.ss[3] );

   rule readTx;
      // TxData chksum <- slave1.tx();  // BOZO FIXME - why do I need <- ???
   endrule
endmodule

(* always_ready *) 
module mkDMATester (Master);
   BusAddr srcBase    = 32'h0000_0000;
   BusAddr srcRegBase = 32'h0800_0000;
   BusAddr snkBase    = 32'h1000_0000;
   BusAddr snkRegBase = 32'h1800_0000;
   BusAddr dmaBase    = 32'h2000_0000;
   BusAddr sramBase   = 32'h3000_0000;

   AmbaMasterAdapter adapter <- mkBlueAmbaMaster;
   BlueMasterAdapter adp_ifc = adapter.bbus;

   Reg#(Bit#(32)) test_number    <- mkConfigReg(0);
   Reg#(Bit#(32)) transferSize   <- mkConfigReg(100);
   Reg#(Bool)     access_pending <- mkReg(False);
   Reg#(Bool)     fail           <- mkReg(False);
   Reg#(Bool)     inprogress     <- mkReg(False);
   Reg#(TestStateType) testState <- mkReg(SRCSNKTEST);
   Reg#(SrcSinkTestStateType) srcSinkTestState <- mkReg(START_DMA);
   Reg#(DmaStateType)  dmaTransferState <- mkReg(DMA_IDLE);
   Reg#(Bit#(32)) src_addr       <- mkConfigReg(0);
   Reg#(Bit#(32)) dest_addr      <- mkConfigReg(0);
   Reg#(Bit#(32)) src_checksum   <- mkConfigReg(0);
   Reg#(Bit#(32)) sink_checksum  <- mkConfigReg(0);
   Reg#(Bit#(32)) rdata          <- mkConfigReg(0);
   Reg#(Bit#(32)) tick_counter   <- mkConfigReg(0);  // BOZO must be ConfigReg
   
// ------------------------------------------------------------------------------
   
   rule dump (tick_counter==0);
      //$dumpvars();
      //$dumpon();
   endrule

// ------------------------------------------------------------------------------
   
   rule tick;
      tick_counter <= tick_counter + 1;
      //if (tick_counter[6:0]==0) begin
      //   $display("tick_counter = %d, test_step = %d",tick_counter, test_step);
      //end
   endrule
         
// ------------------------------------------------------------------------------

   addRules(srcSinkTest(True,5,srcSinkTestState,dmaTransferState,
            src_checksum,sink_checksum,fail,adp_ifc,srcRegBase,snkRegBase,
            srcBase,snkBase,transferSize,test_number,rdata,tick_counter, 
            access_pending,dmaBase));
            
//   rule start_srcSinkTest (testState==SRCSNKTEST && !inprogress);
//      $display("%t testState==SRCSNKTEST && !inprogress",$time);
//     inprogress <= True;
//   endrule
//
//   rule wait_srcSinkTest (testState==SRCSNKTEST && inprogress && srcSinkTestState==SRCSINKDONE );
//      // $display("%t testState==SRCSNKTEST && inprogress");
//      inprogress <= False;
//      testState <= succ(testState);
//   endrule
//   
//   rule testdone (testState==TESTDONE);
//      $display("%t Test Done.",$time);
//      $finish;
//   endrule

   return adapter.amaster;
endmodule
