import FIFO::*;
import RegFile::*;
import GetPut::*;
import ClientServerLib::*;
import ClientServer::*;

import MesaDefs::*;
import MesaIDefs::*;

(* synthesize *)
module mkMesa_Mif (IMif);

    // notification FIFO from VFF
    FIFO#(IVffMifNotify) vff_notify_fifo();
    mkFIFO the_vff_notify_fifo(vff_notify_fifo);

    // route header FIFO to DM
    FIFO#(Ftag) dm_out_fifo();
    mkFIFO the_dm_out_fifo(dm_out_fifo);

    // LPM request FIFO
    FIFO#(Tuple2#(LuRequest, LuTag)) lpm_req_fifo();
    mkFIFO the_lpm_req_fifo(lpm_req_fifo);

    // LPM response FIFO
    FIFO#(Tuple2#(LuResponse, LuTag)) lpm_res_fifo();
    mkFIFO the_lpm_res_fifo(lpm_res_fifo);

/* These are not needed in this level of model

    // VFF request FIFO
    FIFO#(IVffMifRequest) vff_req_fifo();
    mkFIFO the_vff_req_fifo(vff_req_fifo);

    // VFF result FIFO
    FIFO#(IVffMifResponse) vff_res_fifo();
    mkFIFO the_vff_res_fifo(vff_res_fifo);

    method vff();
      vff = mkClientFromFIFOs(vff_req_fifo, vff_res_fifo);
    endmethod

*/

    // Need a table to hold the mapping from packet info to LuTag
    //   In this model, all the info we need came with the notify
    RegFile#(LuTag, IVffMifNotify) tag_map();
    mkRegFileFull the_tag_map(tag_map);

    // Next available tag
    Reg#(LuTag) next_tag();
    mkReg#(0) the_next_tag(next_tag);

    function RouteHeader mkRHeader(LuResponse lu,
				   VffPacketLength length);
       // This is 14 or 15 for errors, 1 for multicast, and 0 for unicast
       let tmpRhType = 0;
       // For RhType == 0, this is 0
       let tmpRhCtlWord = 0;

       return (RouteHeader {
                   node:     lu[15:10],     // bit 6
		   port:     lu[9:5],       // bit 5
		   cos:      lu[4:2],       // bit 3
		   dp:       lu[1:0],       // bit 2
		   ecn:      1'b0,          // bit 1
		   test:     1'b0,          // bit 1
		   length:   length[13:0],  // bit 14
		   pkttype:  tmpRhType,     // bit 4
		   ctlWord:  tmpRhCtlWord,  // bit 20
		   reserved: 0              // bit 8
	       });
    endfunction

    rule handle_notify (True);
        let msg = vff_notify_fifo.first();
        let lpm_request = tuple2(msg.ip_dst_addr, next_tag);
	
	lpm_req_fifo.enq(lpm_request);
	tag_map.upd(next_tag, msg); // (tag_map[next_tag]) <= msg;
	next_tag <= next_tag + 1;
	vff_notify_fifo.deq();
    endrule

    rule handle_lpm_result (True);
        let res = lpm_res_fifo.first();
	let lu_result = tpl_1(res);
	let lu_tag = tpl_2(res);
	let pkt_dta = tag_map.sub(lu_tag); // tag_map[lu_tag];
        let rheader = mkRHeader(lu_result, pkt_dta.vff_pkt_len);
	let ftag = Ftag {length: pkt_dta.vff_pkt_len,
	                 addr: pkt_dta.vff_addr,
	                 route_header: rheader};

	dm_out_fifo.enq(ftag);
	lpm_res_fifo.deq();
    endrule
       

    method notify();
      notify = fifoToPut(vff_notify_fifo);
    endmethod

    method dm();
      dm = fifoToGet(dm_out_fifo);
    endmethod

    method lpm();
      lpm = mkClientFromFIFOs(lpm_req_fifo, lpm_res_fifo);
    endmethod

endmodule: mkMesa_Mif

