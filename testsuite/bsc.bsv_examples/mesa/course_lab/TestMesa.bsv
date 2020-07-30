package TestMesa;

// A simple testbed for the Mesa model

import RegFile::*;
import RegFile::*;
import GetPut::*;
import FIFO::*;
import RAM::*;
import Connectable::*;

import MesaDefs::*;
import Mesa::*;
import SDRAM::*;
import ExtSDRAM::*;

// The main test module

(* synthesize *)
module[Module] sysTestMesa(Empty);

   // Instantiate the Mesa block.
   IMesa mesa();
   mkMesa mesa_inst(mesa);

   // Add and connect a ram with a routing table (just loaded with RegFile File for
   // now.
   Tuple2#(ExtSDRAM, RAM#(Bit#(21),Bit#(32))) ram();
   mkSDRAM ram_inst(ram);

   ExtSDRAM ram_ext;
   ram_ext = tpl_1(ram);

   RAM#(Bit#(21),Bit#(32)) ram_wrapper;
   ram_wrapper = tpl_2(ram);

   mkExtSDRAM(ram_ext);

   // Instantiate a "Transmitter" (from the outside world - a Data Receiver from Mesa).
   ITestTrans transmitter();
   mkTestTrans transmitter_inst(transmitter);

   // Instantiate a "Receiver" (from the outside world - a Data Transmitter to Mesa).
   ITestRecv receiver();
   mkTestRecv receiver_inst(receiver);

   // Connect things up.
   mkConnection(mesa.dram, ram_wrapper);
   mkConnection(mesa.dta_in, receiver.dta_out);
   mkConnection(mesa.dta_out, transmitter.dta_in);
endmodule

// The module to send data to Mesa:

interface ITestRecv;
   method Get#(EthPacket) dta_out;
endinterface

module mkTestRecv(ITestRecv);

   Reg#(Bit#(32)) marker();
   mkReg#(0) marker_inst(marker);

   Reg#(Bit#(16)) addr_count();
   mkReg#(0) addr_count_inst(addr_count);

   RegFile#(Bit#(AddrSize), Bit#(DataSize)) addrs() ;
   mkRegFileLoad#("addrs.handbuilt", 0, 'h1fffff) addrs_inst(addrs) ;

   FIFO#(EthPacket) eth_out_fifo();
   mkFIFO eth_out_fifo_inst(eth_out_fifo);

   Reg#(Bit#(32)) cycles();
   mkReg#(0) i_cycles(cycles);

   rule startit (cycles == 0);
      $dumpvars;
   endrule

   rule exit (True);
     Bit#(64) x <- $time;
     if (x > 10000)
       $finish(0);
   endrule

   rule every (True);
      marker <= marker + 1;
      addr_count <= addr_count > 15 ? 0 : addr_count + 1;
      let temp = create_eth_packet(addrs.sub(zeroExtend(addr_count)), marker);
      eth_out_fifo.enq(temp);
      L3Pkt zow = temp.l3pkt;
      begin case (zow) matches
	       tagged IPv4 {.packet} :
		  action
		     $display("NOTICE: Packet [%h]  exiting the Spi Receiver    (Packet In)  -- (Src Addr = %h)",
			      packet.marker,
			      packet.dst_addr
			      );
		  endaction
	       default: $display("bad packet");
	    endcase
      end
   endrule

   rule cycle (True);
     cycles <= cycles + 1;
     $display("Cycle: %0d Tick: %t", cycles, $time);
   endrule

   method dta_out();
      dta_out = fifoToGet(eth_out_fifo);
   endmethod

endmodule

function EthPacket create_eth_packet(IPAddr addr, Bit#(32) marker);
   begin

      IPPacket packet_ip;
      L3Pkt packet_l3;
      EthPacket packet_eth;

      packet_ip = IPPacket{
			   dst_addr:addr,
			   length:64,
			   marker:marker};
      packet_l3 = IPv4(packet_ip);
      packet_eth = EthPacket{
			     l3pkt:packet_l3,
			     length:64
			     };

      return packet_eth;
   end
endfunction

// The module to receive data from Mesa:

interface ITestTrans;
   method Put#(RhPacket) dta_in;
endinterface

module mkTestTrans(ITestTrans);

   Reg#(Bit#(16)) addr_count();
   mkReg#(0) addr_count_inst(addr_count);

   FIFO#(RhPacket) rh_in_fifo();
   mkFIFO rh_in_fifo_inst(rh_in_fifo);

   rule every (True);
      addr_count <= addr_count > 15 ? 0 : addr_count + 1;
      rh_in_fifo.deq;
      let temp = rh_in_fifo.first;
      L3Pkt zow = temp.pkt.l3pkt;
      begin case (zow) matches
	       tagged IPv4 {.packet} :
		  action
		     $display("NOTICE: Packet [%h] entering the Spi Transmitter (Packet Out) -- (Src Addr = %h) (Routing Header: %h )",
			      packet.marker,
			      packet.dst_addr,
			      {temp.route_hdr.node,
  			       temp.route_hdr.port,
  			       temp.route_hdr.cos,
  			       temp.route_hdr.dp}
			      );
		  endaction
	       default: $display("bad packet");
	    endcase
      end
   endrule

   method dta_in();
      dta_in = fifoToPut(rh_in_fifo);
   endmethod

endmodule

endpackage
