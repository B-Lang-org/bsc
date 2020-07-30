import FIFO::*;
import RegFile::*;
import GetPut::*;
import ClientServerLib::*;
import ClientServer::*;

import MesaDefs::*;
import MesaIDefs::*;

(* synthesize *)
module mkMesa_Vff (IVff);

    // notification FIFO to MIF
    FIFO#(IVffMifNotify) mif_notify_fifo();
    mkFIFO the_mif_notify_fifo(mif_notify_fifo);

    // Dm request FIFO
    FIFO#(IVffDmRequest) dm_req_fifo();
    mkFIFO the_dm_req_fifo(dm_req_fifo);

    // Dm result FIFO
    FIFO#(IVffDmResponse) dm_res_fifo();
    mkFIFO the_dm_res_fifo(dm_res_fifo);

    // input FIFO from Mesa output (via spir)
    FIFO#(IVffIn) spi_in_fifo();
    mkFIFO the_spi_in_fifo(spi_in_fifo);

/* These are not needed in this level of model

    // VFF request FIFO
    FIFO#(IVffMifRequest) mif_req_fifo();
    mkFIFO the_mif_req_fifo(mif_req_fifo);

    // VFF result FIFO
    FIFO#(IVffMifResponse) mif_res_fifo();
    mkFIFO the_mif_res_fifo(mif_res_fifo);

    method mif();
      mif = mkServerFromFIFOs(mif_req_fifo, mif_res_fifo);
    endmethod

*/

    // Need memory to hold the packets, indexed by VffBaseAddr
    RegFile#(VffBaseAddr, EthPacket) pkt_mem();
    // For this model, just use the bottom 5 bits
    mkRegFile#(0,32) the_pkt_mem(pkt_mem);

    // Start address for next packet
    Reg#(VffBaseAddr) next_base_addr();
    mkReg#(0) the_next_base_addr(next_base_addr);

    // Memory usage
    Reg#(Bit#(5)) pkt_count();
    mkReg#(0) the_pkt_count(pkt_count);

    Reg#(Bit#(32)) mem_usage();
    mkReg#(0) the_mem_usage(mem_usage);

    Bool mem_not_full = (pkt_count < 31);

    function Action incr_next_base_addr();
        action
            next_base_addr <= {0, (next_base_addr + 1)[4:0]};
        endaction
    endfunction

    (* descending_urgency = "handle_dm_request,handle_in" *)
    rule handle_in (mem_not_full);
        let l2pkt = spi_in_fifo.first();
	case (l2pkt.l3pkt) matches
	  tagged IPv4 .l3pkt:
	    begin
	      let l2pktlen = getEthLength(l2pkt);
	      let msg = IVffMifNotify { vff_addr:    next_base_addr,
		                        vff_pkt_len: truncate(l2pktlen),
		                        ip_dst_addr: l3pkt.dst_addr };

	      mif_notify_fifo.enq(msg);
	      pkt_mem.upd(next_base_addr, l2pkt); // pkt_mem[next_base_addr] <= l2pkt;
	      pkt_count <= pkt_count + 1;
	      mem_usage <= mem_usage + zeroExtend(l2pktlen);

	      incr_next_base_addr();
	    end
          default:
	    // throw bad packets away :)
	    noAction;
        endcase
	spi_in_fifo.deq();
    endrule

    rule handle_dm_request (True);
        let addr = dm_req_fifo.first();
	let pkt = pkt_mem.sub(addr); // pkt_mem[addr];

	dm_res_fifo.enq(pkt);
	pkt_count <= pkt_count - 1;
	mem_usage <= mem_usage - zeroExtend(getEthLength(pkt));
	dm_req_fifo.deq();
    endrule


    method notify();
      notify = fifoToGet(mif_notify_fifo);
    endmethod

    method dm();
      dm = mkServerFromFIFOs(dm_req_fifo, dm_res_fifo);
    endmethod

    method dta_in();
      dta_in = fifoToPut(spi_in_fifo);
    endmethod

endmodule: mkMesa_Vff
